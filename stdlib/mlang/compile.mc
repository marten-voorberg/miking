-- The MLangCompiler compiles a `MLangProgram` into a single `Expr`. 
-- 
-- Before the MLangCompiler can be used to lower MLang to MExpr, the following 
-- transformations must have been performed (in order) as prerequisites:
-- (0) All `DeclInclude`s must have been handled by `include-handler.mc`.
-- (1) All constants that have been parsed as TmVars should be transformed
---    into TmConst using `const-transformer.mc`.
-- (2) The LanguageComposer in `language-composer.mc` must have been used
--     to generate syns and sems under langauge composition.
-- (3) The entire MLangProgram must have been symbolized using `symbolize.mc`.
-- (4) The MLangProgram must pass all of the conditions of valid composition
--     as checked by `composition-check.mc`. Furthermore, the environment
--     that is generated by these checks must be passed to the compiler.
--
-- The current compilation strategy can be summarized as follows:
-- (1) MLang Decls with a corresponding construct in MExpr, are converted 1-to-1.
--     E.g. DeclLet, DeclRecLets, DeclConDef.
-- (2) For each langauge fragment, a syntax declaration is turned into
--     a TmType if syntax definition is the base of this syntax and constructor
--     defintions are converted to TmConDefs.
-- (3) All of the semantic functions in a Reclets are turned into a TmReclet. 
--     The cases of a semantic functions are converted into a chain of TmMatch
--     expressions based on the orderning that computed in `composition-check.mc`
--     We also perform subtitution on the name of semantic functions, arguments,
--     and type variables which are included from other language fragments.
include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"
include "symbolize.mc"
include "composition-check.mc"
include "language-composer.mc"

include "mexpr/eval.mc"
include "mexpr/eq.mc"

include "common.mc"
include "option.mc"
include "map.mc"
include "bool.mc"
include "name.mc"
include "set.mc"
include "result.mc"

type CompilationContext = use MLangAst in {
  -- Accumulator of compilation result
  exprs: [Expr],

  compositionCheckEnv : CompositionCheckEnv,

  -- A map from identifier strings of semantic functions to the 
  -- symbolized names that the function has in different fragments.
  semSymbols : Map String [Name]
}

-- Substitute the identifier stored in a TmVar based on the provided substitution
recursive let subTmVarSymbol = lam subst : (Name -> Name). lam expr. 
  use MExprAst in 
  switch expr
    case TmVar tm then TmVar {tm with ident = subst tm.ident}
    case other then smap_Expr_Expr (subTmVarSymbol subst) other
  end
end

recursive 
  let subTyVar = lam subst : (Name -> Name). lam expr. 
  use MExprAst in 
  recursive let work = lam ty. switch ty 
    case TyVar t then TyVar {t with ident = subst t.ident}
    case other then smap_Type_Type work ty
  end
  in 
  smap_Expr_Type work expr
end


let _emptyCompilationContext : CompositionCheckEnv -> CompilationContext = lam env : CompositionCheckEnv. {
  exprs = [],
  compositionCheckEnv = env,
  semSymbols = mapEmpty cmpString
}

let withExpr = lam ctx. lam expr. {ctx with exprs = snoc ctx.exprs expr}

let withSemSymbol = lam ctx : CompilationContext. lam n : Name.
  let s = nameGetStr n in 
  let newValue = match mapLookup s ctx.semSymbols with Some names 
                 then cons n names 
                 else [n]
  in
  {ctx with semSymbols = mapInsert s newValue ctx.semSymbols}

-- Create a substitution function by partially applying the first two elements
-- This substitution function maps symbols belonging to semantic function in 
-- included language fragments to the symbol of the semantic function in the 
-- current fragment
let createSubst = lam semSymbols. lam semNames. lam n. 
  let s = nameGetStr n in 
  match mapLookup s semSymbols with Some xs then
    if optionIsSome (find (lam x. nameEqSym x n) xs) then
      match mapLookup s semNames with Some res then res
      else n
    else
      n
  else 
    n

let createSubst2 : [Name] -> [Name] -> (Name -> Name) = lam orig. lam trgt.
  let m = mapFromSeq nameCmp (zip orig trgt) in
  lam n. mapLookupOrElse (lam. n) n m

let createSubst3 = lam env. lam origLang. lam targetLang. lam fallback. 
  match mapLookup origLang env.compositionCheckEnv.langToSems with Some origNames in 
  match mapLookup targetLang env.compositionCheckEnv.langToSems with Some targetNames in 

  let origSet = setOfSeq nameCmp origNames in 
  let targetPairs = map (lam n. (nameGetStr n, n)) targetNames in 
  let targetMap = mapFromSeq cmpString targetPairs in 

  lam n.
    if setMem n origSet then
      match mapLookup (nameGetStr n) targetMap with Some result in 
      result 
    else 
      fallback n



type CompilationError
con FoundIncludeError : {info : Info, path: String} -> CompilationError

type CompilationWarning

type CompilationResult = Result CompilationWarning CompilationError CompilationContext 

let isTypeDecl = use MLangAst in 
  lam d. match d with DeclType _ then true else false
let isSynDecl = use MLangAst in 
  lam d. match d with DeclSyn _ then true else false
let isSemDecl = use MLangAst in 
  lam d. match d with DeclSem _ then true else false

lang DeclCompiler = DeclAst + Ast
  sem compileDecl : CompilationContext -> Decl -> CompilationResult
end

lang LetDeclCompiler = DeclCompiler + LetDeclAst + LetAst
  sem compileDecl ctx = 
  | DeclLet d -> result.ok (
    withExpr ctx (TmLet {ident = d.ident,
                         tyAnnot = d.tyAnnot,
                         tyBody = d.tyBody,
                         body = d.body,
                         info = d.info,
                         ty = tyunknown_,
                         inexpr = uunit_}))
end

lang RecletsDeclCompiler = DeclCompiler + RecLetsDeclAst + RecLetsAst
  sem compileDecl ctx = 
  | DeclRecLets d -> result.ok (
    withExpr ctx (TmRecLets {bindings = d.bindings,
                             inexpr = uunit_,
                             ty = tyunknown_,
                             info = d.info}))
end

lang UtestDeclCompiler = DeclCompiler + UtestDeclAst + UtestAst
  sem compileDecl ctx = 
  | DeclUtest d -> result.ok (
    withExpr ctx (TmUtest {test = d.test,
                           expected = d.expected,
                           next = uunit_,
                           tusing = d.tusing,
                           tonfail = None (),
                           ty = tyunknown_,
                           info = d.info}))
end

lang TypeDeclCompiler = DeclCompiler + TypeDeclAst + TypeAst
  sem compileDecl ctx = 
  | DeclType d -> 
    result.ok (withExpr ctx (TmType {ident = d.ident,
                               params = d.params,
                               tyIdent = d.tyIdent,
                               info = d.info,
                               ty = tyunknown_,
                               inexpr = uunit_}))
end

lang ConDefDeclCompiler = DeclCompiler + DataDeclAst + DataAst
  sem compileDecl ctx = 
  | DeclConDef d -> result.ok (
    withExpr ctx (TmConDef {ident = d.ident,
                            tyIdent = d.tyIdent,
                            info = d.info,
                            ty = tyunknown_,
                            inexpr = uunit_}))
end

lang ExtDeclCompiler = DeclCompiler + ExtDeclAst + ExtAst
  sem compileDecl ctx = 
  -- TODO(voorberg, 2024-04-23): Add test case for the compilation of externals.
  | DeclExt d -> result.ok (
    withExpr ctx (TmExt {ident = d.ident,
                         tyIdent = d.tyIdent,
                         effect = d.effect,
                         info = d.info,
                         ty = tyunknown_,
                         inexpr = uunit_}))
end

lang LangDeclCompiler = DeclCompiler + LangDeclAst + MExprAst + SemDeclAst + 
                        SynDeclAst + TypeDeclAst 
  sem compileDecl ctx = 
  | DeclLang l -> 
    let langStr = nameGetStr l.ident in

    let typeDecls = filter isTypeDecl l.decls in 
    let synDecls = filter isSynDecl l.decls in 
    let semDecls = filter isSemDecl l.decls in 

    let nameSeq =  (map (lam s. match s with DeclSem s in (nameGetStr s.ident, s.ident)) semDecls) in 
    let semNames = mapFromSeq cmpString nameSeq in 

    let ctx = foldl withSemSymbol ctx (map (lam s. match s with DeclSem s in s.ident) semDecls) in 

    let res = result.foldlM compileDecl ctx typeDecls in 
    let res = result.map (lam ctx. foldl compileSynTypes ctx synDecls) res in 
    let res = result.map (lam ctx. foldl (compileSynConstructors langStr) ctx synDecls) res in 

    let compileSemToResult : CompilationContext -> [Decl] -> CompilationContext
      = lam ctx. lam sems.
        let bindings = map (compileSem langStr ctx semNames) sems in 
        withExpr ctx (TmRecLets {bindings = bindings,
                                 inexpr = uunit_, 
                                 ty = tyunknown_,
                                 info = l.info})
    in
    result.map (lam ctx. compileSemToResult ctx semDecls) res
  | DeclSyn s -> 
    error "Unexpected DeclSyn"
  | DeclSem s -> 
    error "Unexpected DeclSem!"

  sem compileSynTypes : CompilationContext -> Decl -> CompilationContext
  sem compileSynTypes ctx =
  | DeclSyn s ->
    -- We only include a type definition if this is the base declaration of
    -- a syntax type. To check that something is a base syn definition,
    -- we check that it does not include any other definitions.
    if null s.includes then
      withExpr ctx (TmType {ident = s.ident,
                            params = s.params,
                            tyIdent = tyvariant_ [],
                            inexpr = uunit_,
                            ty = tyunknown_,
                            info = s.info})
    else
      ctx
  
  sem compileSynConstructors : String -> CompilationContext -> Decl -> CompilationContext
  sem compileSynConstructors langStr ctx = 
  | DeclSyn s ->
    let baseIdent = (match mapLookup (langStr, nameGetStr s.ident) ctx.compositionCheckEnv.baseMap with Some ident in ident) in

    recursive let makeForallWrapper = lam params. lam ty. 
      match params with [h] ++ t then
        ntyall_ h (makeForallWrapper t ty)
      else
        ty
    in 
    let forallWrapper = makeForallWrapper s.params in 
    let tyconApp = foldl (lam acc. lam n. tyapp_ acc (ntyvar_ n)) (ntycon_ baseIdent) s.params in 
    let compileDef = lam ctx. lam def : {ident : Name, tyIdent : Type}.
      withExpr ctx (TmConDef {ident = def.ident,
                              tyIdent = forallWrapper (tyarrow_ def.tyIdent tyconApp),
                              inexpr = uunit_,
                              ty = tyunknown_,
                              info = s.info}) in 
    let ctx = foldl compileDef ctx s.defs in 
    ctx
  -- sem compileSem : CompilationContext -> Map String Name -> Map String Name -> Decl -> RecLetBinding 
  sem compileSem langStr ctx semNames = 
  | DeclSem d -> 
    let baseIdent = (match mapLookup (langStr, nameGetStr d.ident) ctx.compositionCheckEnv.baseMap with Some ident in ident) in
    let baseTyAnnot = match mapLookup baseIdent ctx.compositionCheckEnv.semBaseToTyAnnot with Some ty in ty in 
    let tyAnnot = match d.tyAnnot with TyUnknown _ then baseTyAnnot else d.tyAnnot in 

    -- Create substitution function for param aliasing
    let args = match d.args with Some args then args else [] in 
    let paramAliases : [[Name]] = mapOption
      (lam incl. match mapLookup incl ctx.compositionCheckEnv.semArgsMap with Some opt in opt)
      d.includes 
    in 
    let argsIdents : [Name] = map (lam a. a.ident) args in 

    let pairs = join (map (lam params. zip params argsIdents) paramAliases) in 
    let paramAliasMap = mapFromSeq nameCmp pairs in 
    let subst2 = lam n. mapLookupOrElse (lam. n) n paramAliasMap in

    -- Create subst for recursive all semantic functions
    let subst = createSubst ctx.semSymbols semNames in 

    let targetName = nameSym "target" in 
    let target = nvar_ targetName in 

    -- OPT(voorberg, 23-04-2024): The implementation of compileBody and
    --                            compileArgs can be made tail-recursive.
    recursive 
      let compileBody = lam cases : [{pat : Pat, thn : Expr}]. 
        match cases with [h] ++ t then
          TmMatch {target = target,
                   pat = h.pat,
                   thn = h.thn,
                   els = compileBody t,
                   ty = tyunknown_,
                   info = d.info}
        -- else (error_ (str_ "Inexhaustive match!"))
        else 
          let s = join ["Inexhaustive match in ", langStr, ".", nameGetStr d.ident, "!\n"] in 
          semi_ (print_ (str_ s)) never_
    in 
    let cases = match mapLookup (langStr, nameGetStr d.ident) ctx.compositionCheckEnv.semPatMap 
                with Some x then x
                else error "CompositionCheckEnv must contain the ordered cases for all semantic functions!"
    in

    -- Substitute parameters and sem symbols.
    let work = lam c.
      let origArgs : Option[Name] = match mapLookup c.orig ctx.compositionCheckEnv.semArgsMap with Some args in args in 
      let origIdent : Name = match mapLookup c.orig ctx.compositionCheckEnv.semSymMap with Some ident in ident in 

      let fallback = match origArgs with Some args then createSubst2 args argsIdents
                       else (lam x. x) in 
      let subst = createSubst3 ctx c.orig.0 langStr fallback in
      {c with thn = subTmVarSymbol subst c.thn} in 
    let cases = map work cases in

    -- Substitute tyvars introduced by type signature.
    -- Todo: handle case in which lengths are unequal.
    let curSymbols = match mapLookup (langStr, nameGetStr d.ident) ctx.compositionCheckEnv.semTyVarMap with Some ns in ns in  
    let work = lam c. 
      let origSymbols = match mapLookup c.orig ctx.compositionCheckEnv.semTyVarMap with Some ns in ns in 
      let subst = createSubst2 origSymbols curSymbols in 
      {c with thn = subTyVar subst c.thn} in 
    let cases = map work cases in 

    let cases = map (lam c. {thn = c.thn, pat = c.pat}) cases in
    let body = compileBody cases in 
    recursive let compileArgs = lam args. 
          match args with [h] ++ t then
            TmLam {ident = h.ident,
                   tyAnnot = h.tyAnnot,
                  --  tyAnnot = tyunknown_,
                   tyParam = tyunknown_,
                   body = compileArgs t,
                   ty = tyunknown_,
                   info = d.info}
          else
            TmLam {ident = targetName,
                   tyAnnot = tyunknown_,
                   tyParam = tyunknown_,
                   body = body,
                   ty = tyunknown_,
                   info = d.info}
    in 
    let result = compileArgs (optionGetOrElse (lam. []) d.args) in 
    match d.args with Some _ then 
      {ident = d.ident,
      tyAnnot = tyAnnot,
      tyBody = tyunknown_,
      body = result,
      info = d.info}
    else 
      {ident = d.ident,
      tyAnnot = tyAnnot,
      tyBody = tyunknown_,
      body = (nulam_ (nameSym "") (semi_ (print_ (str_ (join ["Semantic function without cases!: ", langStr, ".", nameGetStr d.ident]))) never_)),
      info = d.info}
end 

lang MLangTopLevelCompiler = MLangTopLevel + DeclCompiler
  sem compileProg : CompilationContext -> MLangProgram -> CompilationResult
  sem compileProg ctx = 
  | prog -> 
    let res = result.foldlM compileDecl ctx prog.decls in
    result.map (lam ctx. withExpr ctx prog.expr) res
end

lang MLangCompiler = MLangAst + MExprAst +
                     MLangTopLevelCompiler + LangDeclCompiler + ExtDeclCompiler +
                     ConDefDeclCompiler + TypeDeclCompiler + UtestDeclCompiler +
                     RecletsDeclCompiler + LetDeclCompiler
  sem compile : CompilationContext -> MLangProgram -> Result CompilationWarning CompilationError Expr
  sem compile ctx =| prog -> 
    match _consume (compileProg ctx prog) with (_, res) in
    switch res
      case Left err then result.err (head err)
      case Right ctx then result.ok (bindall_ ctx.exprs)
    end
end

lang TestLang = MLangCompiler + MLangSym + MLangCompositionCheck + 
                MExprPrettyPrint + MExprEval + MExprEq end

mexpr
use TestLang in 
use LanguageComposer in 

let simpleEval = lam e. eval (evalCtxEmpty ()) e in 

let testCompile = lam p. 
  let p = composeProgram p in 
  match symbolizeMLang symEnvDefault p with (_, p) in 
  match _consume (checkComposition p) with (_, res) in 
  match res with Right env in
  let ctx = _emptyCompilationContext env in 
  let res = _consume (compile ctx p) in 
  match res with (_, rhs) in 
  match rhs with Right expr in expr
in

let testError = lam p. 
  match symbolizeMLang symEnvDefault p with (_, p) in 
  match _consume (checkComposition p) with (_, res) in 
  match res with Right env in
  let ctx = _emptyCompilationContext env in 
  let res = _consume (compile ctx p) in 
  match res with (_, rhs) in 
  match rhs with Left errs in errs
in

let testEval = lam p.
  simpleEval (testCompile p)
in 

-- Test simple let binding
let p : MLangProgram = {
    decls = [
        decl_ulet_ "x" (int_ 1)
    ],
    expr = var_ "x"
} in 
utest testEval p with int_ 1 using eqExpr in 

-- Test recursive let bindings through mutually recursive odd/even
let odd = (ulam_ "x" 
  (if_ 
    (eqi_ (var_ "x") (int_ 0))
    (false_)
    (appf1_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
in 
let even = (ulam_ "x" 
  (if_ 
    (eqi_ (var_ "x") (int_ 0))
    (true_)
    (appf1_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
in 
let p : MLangProgram = {
    decls = [
        decl_ureclets_ [("odd", odd), ("even", even)]
    ],
    expr = appf1_ (var_ "odd") (int_ 9)
} in 
utest testEval p with true_ using eqExpr in 
let p : MLangProgram = {
    decls = [
        decl_ureclets_ [("odd", odd), ("even", even)]
    ],
    expr = appf1_ (var_ "odd") (int_ 10)
} in 
utest testEval p with false_ using eqExpr in 

-- Test Utest
let p : MLangProgram = {
    decls = [
        decl_utest_ (int_ 3) (addi_ (int_ 1) (int_ 2))
    ],
    expr = uunit_
} in 
let expected : Expr = utest_ (int_ 3) (addi_ (int_ 1) (int_ 2)) uunit_ in 
utest testCompile p with expected using eqExpr in 

-- Test Declype and DeclConDef
let p : MLangProgram = {
    decls = [
      decl_type_ "Foo" [] (tyvariant_ []),
      decl_condef_ "Bar"
        (tyarrow_ tyint_ (tycon_ "Foo"))
      ],
    expr = matchex_ 
      (conapp_ "Bar" (int_ 1))
      (pcon_ "Bar" (pvar_ "x"))
      (addi_ (var_ "x") (int_ 1))
} in 
let res = testCompile p in 
utest testEval p with int_ 2 using eqExpr in 

-- Test basic semantic function
let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [
            decl_sem_ 
                "f"
                [("x", tyint_)]
                [(pvar_ "y", addi_ (var_ "x") (var_ "y"))]
        ]
    ],
    expr = bind_ (use_ "L1") (appf2_ (var_ "f") (int_ 10) (int_ 20))
} in 
utest testEval p with int_ 30 using eqExpr in 

-- Test semantic function with pattern that must be ordered
-- Since the 2nd pattern is a strict subset of the first,
-- the first pattern is checked first and only if this is not a match
-- do we fall through to the first pattern. 
let fsem = decl_sem_ "f" [] [(por_ (pint_ 1) (pint_ 2), int_ -1),
                             (pint_ 2, int_ 1)]
in
let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [fsem]
    ],
    expr = bind_ (use_ "L1") (appf1_ (var_ "f") (int_ 2))
} in 
utest testEval p with int_ 1 using eqExpr in 

let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [fsem]
    ],
    expr = bind_ (use_ "L1") (appf1_ (var_ "f") (int_ 1))
} in 
utest testEval p with int_ -1 using eqExpr in

-- Test DeclSyn and DeclSem using a small arithmetic language
let exprSyn = decl_syn_ "Expr" [("IntExpr", tyint_), 
                                ("AddExpr", tytuple_ [tycon_ "Expr", tycon_ "Expr"])] in 
let evalSem = decl_sem_ "eval" [] [(pcon_ "IntExpr" (pvar_ "i"), var_ "i"),
                                   (pcon_ "AddExpr" (ptuple_ [pvar_ "lhs", pvar_ "rhs"]), 
                                    addi_ (appf1_ (var_ "eval") (var_ "lhs")) (appf1_ (var_ "eval") (var_ "rhs")))] in 

let p : MLangProgram = {
    decls = [
        decl_lang_ "MyIntArith" [exprSyn, evalSem]
    ],
    expr = bind_ (use_ "MyIntArith") 
                 (appf1_ (var_ "eval") 
                         (conapp_ "AddExpr" (utuple_ [(conapp_ "IntExpr" (int_ 40)),
                                                      (conapp_ "IntExpr" (int_ 2))])))
} in 
utest testEval p with int_ 42 using eqExpr in

-- Test Sum Extension
let baseSyn = decl_syn_ "Expr" [("IntExpr", tyint_), 
                                ("AddExpr", tytuple_ [tycon_ "Expr", tycon_ "Expr"])] in 
let baseSem = decl_sem_ "eval" [] [(pcon_ "IntExpr" (pvar_ "i"), var_ "i"),
                                   (pcon_ "AddExpr" (ptuple_ [pvar_ "lhs", pvar_ "rhs"]), 
                                    addi_ (appf1_ (var_ "eval") (var_ "lhs")) (appf1_ (var_ "eval") (var_ "rhs")))] in 
let sugarSyn = decl_syn_ "Expr" [("IncrExpr", tycon_ "Expr")] in 
let sugarEval = decl_sem_ "eval" [] [(pcon_ "IncrExpr" (pvar_ "e"), addi_ (int_ 1) (appf1_ (var_ "eval") (var_ "e")))] in 
let p : MLangProgram = {
    decls = [
        decl_lang_ "MyIntArith" [baseSyn, baseSem],
        decl_langi_ "SugaredIntArith" ["MyIntArith"] [sugarSyn, sugarEval]
    ],
    expr = bind_ (use_ "SugaredIntArith") 
                 (appf1_ (var_ "eval") 
                         (conapp_ "IncrExpr" (conapp_ "AddExpr" (utuple_ [(conapp_ "IntExpr" (int_ 20)),
                                                      (conapp_ "IntExpr" (int_ 2))]))))
} in 
utest testEval p with int_ 23 using eqExpr in

let p : MLangProgram = {
    decls = [
        decl_lang_ "MyIntArith" [baseSyn, baseSem],
        decl_langi_ "SugaredIntArith" ["MyIntArith"] [sugarSyn, sugarEval]
    ],
    expr = bind_ (use_ "SugaredIntArith")
                 (appf1_ (var_ "eval") 
                         (conapp_ "AddExpr" (utuple_ [(conapp_ "IncrExpr" (conapp_ "IntExpr" (int_ 21))),
                                                      (conapp_ "IntExpr" (int_ 1))])))
} in 
utest testEval p with int_ 23 using eqExpr in

-- Test semantic function with different paremeter names
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
          decl_sem_ "f" [("x", tyunknown_)] [(pint_ 0, var_ "x")]
        ],
        decl_langi_ "L1" ["L0"] [
          decl_sem_ "f" [("y", tyunknown_)] [(pint_ 1, muli_ (int_ -1) (var_ "y"))]
        ]
    ],
    expr = bind_ (use_ "L1")
                 (addi_ ((appf2_ (var_ "f") (int_ 10) (int_ 0)))
                        ((appf2_ (var_ "f") (int_ 10) (int_ 1))))
} in 
utest testEval p with int_ 0 using eqExpr in

-- Test language composition under quantified type variables
let p : MLangProgram = {
    decls = [
        decl_lang_ "L0" [
          decl_semty_cases_ 
            "f" 
            (tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")))
            [(pvar_ "x", bind_ (let_ "y" (tyvar_ "a") (var_ "x")) (var_ "y"))]
        ],
        decl_langi_ "L1" ["L0"] []
    ],
    expr = bind_ (use_ "L1") (appf1_ (var_ "f") (int_ 0))
} in 
utest testEval p with int_ 0 using eqExpr in

-- Test language composition is correctly renaming bound recursive functions.
let decls = [
  decl_lang_ "L0" [
    decl_sem_
      "isodd" 
      []
      [(pvar_ "x", if_ (eqi_ (int_ 0) (var_ "x")) false_ (appf1_ (var_ "iseven") (subi_ (var_ "x") (int_ 1))))],
    decl_sem_
      "iseven"
      []
      []
  ],
  decl_langi_ "L1" ["L0"] [
    decl_sem_
      "iseven" 
      []
      [(pvar_ "x", if_ (eqi_ (int_ 0) (var_ "x")) true_ (appf1_ (var_ "isodd") (subi_ (var_ "x") (int_ 1))))]
  ]
] in 
let p : MLangProgram = {
    decls = decls,
    expr = bind_ (use_ "L1") (appf1_ (var_ "iseven") (int_ 12))
} in 
utest testEval p with true_ using eqExpr in
let p : MLangProgram = {
    decls = decls,
    expr = bind_ (use_ "L1") (appf1_ (var_ "iseven") (int_ 11))
} in 
utest testEval p with false_ using eqExpr in
()