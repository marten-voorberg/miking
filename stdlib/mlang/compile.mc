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
include "mexpr/utils.mc"

include "common.mc"
include "option.mc"
include "map.mc"
include "bool.mc"
include "name.mc"
include "error.mc"
include "set.mc"
include "result.mc"

type CompilationContext = use MLangAst in {
  -- Accumulator of compilation result
  exprs: [Expr],

  compositionCheckEnv : CompositionCheckEnv,

  -- A map from identifier strings of semantic functions to the 
  -- symbolized names that the function has in different fragments.
  semSymbols : Map String [Name],

  conToExtType : Map Name Name,

  allBaseSyns : Set Name,

  baseToCons : Map Name (Set Name),

  baseMap : Map Name Name,

  globalFields : Map Name Type
}

let mergeRecordTypes = lam l. lam r. 
  use RecordTypeAst in 
  match (l, r) with (TyRecord left, TyRecord right) in 
  TyRecord {left with fields = mapUnion left.fields right.fields}

let _emptyCompilationContext : CompositionCheckEnv -> CompilationContext = lam env : CompositionCheckEnv. {
  exprs = [],
  compositionCheckEnv = env,
  semSymbols = mapEmpty cmpString,
  conToExtType = mapEmpty nameCmp,
  allBaseSyns = setEmpty nameCmp,
  baseToCons = mapEmpty nameCmp,
  baseMap = mapEmpty nameCmp,
  globalFields = mapEmpty nameCmp
}

let mapParamIdent = nameNoSym "m"
let baseExtIdent = nameSym "BaseExt"


let withExpr = lam ctx. lam expr. {ctx with exprs = snoc ctx.exprs expr}

let withSemSymbol = lam ctx : CompilationContext. lam n : Name.
  let s = nameGetStr n in 
  let newValue = match mapLookup s ctx.semSymbols with Some names 
                 then cons n names 
                 else [n]
  in
  {ctx with semSymbols = mapInsert s newValue ctx.semSymbols}

let createPairsForSubst = lam env. lam origLang. lam targetLang.  
  match mapLookup origLang env.compositionCheckEnv.langToSems with Some origNames in 
  match mapLookup targetLang env.compositionCheckEnv.langToSems with Some targetNames in 

  let origSet = setOfSeq nameCmp origNames in 
  let targetPairs = map (lam n. (nameGetStr n, n)) targetNames in 
  let targetMap = mapFromSeq cmpString targetPairs in 

  let origs = setToSeq origSet in 

  map (lam n. (n, match mapLookup (nameGetStr n) targetMap with Some x in x)) origs

type CompilationError
con FoundIncludeError : {info : Info, path: String} -> CompilationError

type CompilationWarning

type CompilationResult = Result CompilationWarning CompilationError CompilationContext 

let isTypeDecl = use MLangAst in 
  lam d. match d with DeclType _ then true else false
let isSynDecl = use MLangAst in 
  lam d. match d with DeclSyn _ then true else false
let isCosynDecl = use MLangAst in 
  lam d. match d with DeclCosyn _ then true else false
let isSemDecl = use MLangAst in 
  lam d. match d with DeclSem _ then true else false
let isCosemDecl = use MLangAst in 
  lam d. match d with DeclCosem _ then true else false
let isProdDecl = use MLangAst in 
  lam d. match d with SynDeclProdExt _ then true else false

lang DeclCompiler = DeclAst + Ast + MExprSubstitute
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
                        SynDeclAst + TypeDeclAst + SynProdExtDeclAst + 
                        ExtRecordAst + ExtRecordTypeAst + CosynDeclAst
                        + CosemDeclAst + RecordCopatAst
  sem compileDecl ctx = 
  | DeclLang l -> 
    let langStr = nameGetStr l.ident in

    let typeDecls = filter isTypeDecl l.decls in 
    let synDecls = filter isSynDecl l.decls in 
    let cosynDecls = filter isCosynDecl l.decls in 
    let semDecls = filter isSemDecl l.decls in 
    let cosemDecls = filter isCosemDecl l.decls in 
    let prodDecls = filter isProdDecl l.decls in 

    let nameSeq =  (map (lam s. match s with DeclSem s in (nameGetStr s.ident, s.ident)) semDecls) in 
    let semNames = mapFromSeq cmpString nameSeq in 

    let ctx = foldl withSemSymbol ctx (map (lam s. match s with DeclSem s in s.ident) semDecls) in 

    let res = result.foldlM compileDecl ctx typeDecls in 
    let res = result.map (lam ctx. foldl compileSynTypes ctx synDecls) res in 
    let res = result.map (lam ctx. foldl (compileCosyn langStr) ctx cosynDecls) res in 
    let res = result.map (lam ctx. foldl (compileSynConstructors langStr) ctx synDecls) res in 
    let res = result.map (lam ctx. foldl (compileSynProd langStr) ctx prodDecls) res in 

    let compileSemToResult : CompilationContext -> [Decl] -> [Decl] -> CompilationContext
      = lam ctx. lam sems. lam cosems.
        let semBindings = map (compileSem langStr ctx semNames) sems in 
        let cosemBindings = map (compileCosem langStr ctx semNames) cosems in 
        withExpr ctx (TmRecLets {bindings = concat semBindings cosemBindings,
                                 inexpr = uunit_, 
                                 ty = tyunknown_,
                                 info = l.info})
    in
    result.map (lam ctx. compileSemToResult ctx semDecls cosemDecls) res
  | DeclSyn s -> 
    error "Unexpected DeclSyn"
  | DeclSem s -> 
    error "Unexpected DeclSem!"

  sem compileCosyn : String -> CompilationContext -> Decl -> CompilationContext
  sem compileCosyn langStr ctx = 
  | DeclCosyn s -> 
    match mapLookup (langStr, nameGetStr s.ident) ctx.compositionCheckEnv.baseMap 
    with Some baseIdent in 

    let ctx = if s.isBase 
              then withExpr ctx (TmRecType {ident = s.ident,
                                            params = s.params,
                                            info = s.info,
                                            ty = tyunknown_,
                                            inexpr = uunit_}) 
              else ctx in 
    
    let compileField = lam ctx. lam sid. lam ty.
      let tyIdent = tyarrow_ (ntycon_ baseIdent) ty in  
      withExpr ctx (TmRecField {label = sidToString sid,
                                tyIdent = nstyall_ mapParamIdent (Poly ()) tyIdent,
                                inexpr = uunit_,
                                ty = tyunknown_,
                                info = s.info}) in 

    match s.ty with TyRecord rec then
      mapFoldWithKey compileField ctx rec.fields
    else
      errorSingle [s.info] (join [
        " * A cosyn can only have record types as their type!"
      ])
      
                                        

  sem compileSynTypes : CompilationContext -> Decl -> CompilationContext
  sem compileSynTypes ctx =
  | DeclSyn s ->
    -- We only include a type definition if this is the base declaration of
    -- a syntax type. To check that something is a base syn definition,
    -- we check that it does not include any other definitions.
    if null s.includes then
      withExpr ctx (TmType {ident = s.ident,
                            params = cons mapParamIdent s.params,
                            tyIdent = tyvariant_ [],
                            inexpr = uunit_,
                            ty = tyunknown_,
                            info = s.info})
    else
      ctx
  
  sem _insertImplicitTyVars : CompilationContext -> Type -> Type
  sem _insertImplicitTyVars ctx =
  | TyCon t & ty -> 
    if setMem t.ident ctx.allBaseSyns then
      TyApp {lhs = TyCon {t with data = ntyvar_ mapParamIdent}, 
             rhs = ntyvar_ mapParamIdent, info = t.info}
    else
      ty
  | ty -> smap_Type_Type (_insertImplicitTyVars ctx) ty

  sem compileSynConstructors : String -> CompilationContext -> Decl -> CompilationContext
  sem compileSynConstructors langStr ctx = 
  | DeclSyn s ->
    let baseIdent = (match mapLookup (langStr, nameGetStr s.ident) ctx.compositionCheckEnv.baseMap with Some ident in ident) in

    let params = cons mapParamIdent s.params in 

    recursive let makeForallWrapper = lam params. lam ty. 
      match params with [h] ++ t then
        ntyall_ h (makeForallWrapper t ty)
      else
        ty
    in 
    let forallWrapper = makeForallWrapper params in 
    let tyconApp = foldl (lam acc. lam n. tyapp_ acc (ntyvar_ n)) (ntycon_ baseIdent) params in 
    let compileDef = lam ctx. lam def : {ident : Name, tyIdent : Type}.
      match def.tyIdent with TyRecord _ then
        let tyIdent = mergeRecordTypes 
          def.tyIdent
          (mapLookupOrElse (lam. tyrecord_ []) baseIdent ctx.globalFields) in 
        match tyIdent with TyRecord rec in 
        -- TODO: Determine the proper symbol for this type.
        let recIdent = nameNoSym (concat (nameGetStr def.ident) "Type") in
        -- let recIdent = nameSym (concat (nameGetStr def.ident) "Type") in 
        let ctx = {ctx with conToExtType = mapInsert def.ident recIdent ctx.conToExtType} in 
        let ctx = withExpr ctx (TmRecType {ident = recIdent,
                                           params = [],
                                           ty = tyunknown_,
                                           inexpr = uunit_,
                                           info = infoTy def.tyIdent}) in 
        let work = lam acc. lam sid. lam ty. 
          let ty = _insertImplicitTyVars ctx ty in 
          let label = sidToString sid in 
          let tyIdent = tyarrow_ (ntycon_ recIdent) ty in 
          withExpr acc (TmRecField {label = label,
                                    tyIdent = nstyall_ mapParamIdent (Poly ()) tyIdent,
                                    inexpr = uunit_,
                                    ty = tyunknown_,
                                    info = infoTy ty}) in
        let ctx = mapFoldWithKey work ctx rec.fields in 
        let lhs = TyExtRec {info = infoTy def.tyIdent,
                                   ident = recIdent,
                                   ty = ntyvar_ mapParamIdent} in 
        withExpr ctx (TmConDef {ident = def.ident,
                                tyIdent = forallWrapper (tyarrow_ lhs tyconApp),
                                inexpr = uunit_,
                                ty = tyunknown_,
                                info = s.info})
      else 
        withExpr ctx (TmConDef {ident = def.ident,
                                tyIdent = forallWrapper (tyarrow_ def.tyIdent tyconApp),
                                inexpr = uunit_,
                                ty = tyunknown_,
                                info = s.info})
    in 
    let ctx = foldl compileDef ctx s.defs in 

    -- Update baseToCons map
    let newSet = foldr 
      setInsert
      (mapLookupOrElse (lam. setEmpty nameCmp) baseIdent ctx.baseToCons)
      (map (lam d. d.ident) s.defs) in 
    let ctx = {ctx with baseToCons = mapInsert baseIdent newSet ctx.baseToCons} in 

    ctx

  sem compileSynProd : String -> CompilationContext -> Decl -> CompilationContext
  sem compileSynProd langStr ctx =
  | SynDeclProdExt s ->
    -- Compile indiv ext
    let compileExt = lam ctx. lam ext. 
      match ext with {ident = ident, tyIdent = tyIdent} in 
      match mapLookup ident ctx.conToExtType with Some recIdent in 
      match tyIdent with TyRecord rec in 
      let work = lam acc. lam sid. lam ty. 
          let label = sidToString sid in 
          let tyIdent = tyarrow_ (ntycon_ recIdent) ty in 
          withExpr acc (TmRecField {label = label,
                                    tyIdent = nstyall_ mapParamIdent (Poly ()) tyIdent,
                                    inexpr = uunit_,
                                    ty = tyunknown_,
                                    info = infoTy ty}) 
      in
      mapFoldWithKey work ctx rec.fields 
    in 
    let ctx = foldl compileExt ctx s.individualExts in 

    -- Compile global ext
    match s.globalExt with Some globalExt then
      match mapLookup s.ident ctx.baseMap with Some baseIdent in 
      match mapLookup baseIdent ctx.baseToCons with Some allConstructors in 
      let explicitConstructors = setOfSeq nameCmp (map (lam e. e.ident) s.individualExts) in 
    
      let relevantCons = setSubtract allConstructors explicitConstructors in 

      match globalExt with TyRecord rec in 

      let compileGlobalExt = lam ctx. lam ident.
        match mapLookup ident ctx.conToExtType with Some recIdent in 
        let work = lam acc. lam sid. lam ty. 
          let label = sidToString sid in 
          let tyIdent = tyarrow_ (ntycon_ recIdent) ty in 
            withExpr acc (TmRecField {label = label,
                                      tyIdent = nstyall_ mapParamIdent (Poly ()) tyIdent,
                                      inexpr = uunit_,
                                      ty = tyunknown_,
                                      info = infoTy ty}) 
        in
        mapFoldWithKey work ctx rec.fields
      in 

      let ctx = setFold compileGlobalExt ctx relevantCons in 

      let newGlobalExt = mergeRecordTypes 
        (mapLookupOrElse (lam. tyrecord_ []) baseIdent ctx.globalFields)
        globalExt in 

      {ctx with globalFields = mapInsert baseIdent newGlobalExt ctx.globalFields}
    else 
      ctx

  sem compileCosem langStr ctx cosemNames = 
  | DeclCosem d -> 
    -- TODO: gather cases from includes
    match mapLookup (langStr, nameGetStr d.ident) ctx.compositionCheckEnv.cosemCaseMap 
    with Some cases in 

    if setIsEmpty cases then 
      let body = foldl (lam acc. lam arg. nulam_ arg.ident acc) (inever_ d.info) d.args in 
      {ident = d.ident,
      tyAnnot = tyunknown_,
      tyBody = tyunknown_,
      body = body,
      info = d.info}
    else 
      let cases = setToSeq cases in 

      let syms = mapi (lam i. lam. (nameSym (concat "cosemResult" (int2string i)))) cases in

      let argsIdents = map (lam a. a.ident) d.args in 

      let pairs = mapi (lam i. lam c. (get syms i, c)) cases in 
      
      let compileThn = lam acc : Expr. lam pair : (Name, ExtendedCopat). 
        match pair with (ident, c) in

        match mapLookup c.orig ctx.compositionCheckEnv.semArgsMap with Some (Some origArgs) in 
        let pairs = join [zip origArgs argsIdents,
                          createPairsForSubst ctx c.orig.0 langStr] in 
        let subst = mapFromSeq nameCmp pairs in
        let thn = substituteIdentifiersExpr subst c.thn in 
        bind_ (nulet_ ident thn) acc in 
    
      match head cases with {copat = RecordCopat {ident = ident}} in 

      let f = lam acc. lam i. lam c.
        match c with {copat = RecordCopat {fields = fields}} in
        let g = lam acc. lam str. 
          mapInsert str (recordproj_ str (nvar_ (get syms i))) acc in 
        foldl g acc fields
      in 
      let bindings = foldli f (mapEmpty cmpString) cases in
      let creator = TmExtRecord {ident = ident,
                                bindings = bindings,
                                info = d.info,
                                ty = tyunknown_} in 

      let expr = foldl compileThn creator pairs in 
      let expr = foldl (lam acc. lam arg. nulam_ arg.ident acc) expr (reverse d.args) in 

      {ident = d.ident,
      tyAnnot = tyunknown_,
      tyBody = tyunknown_,
      body = expr,
      info = d.info}

  sem compileSem langStr ctx semNames = 
  | DeclSem d -> 
    -- If this semantic function does not have a type annotation, copy the 
    -- type annotation from the base semantic function.
    let baseIdent = (match mapLookup (langStr, nameGetStr d.ident) ctx.compositionCheckEnv.baseMap with Some ident in ident) in
    let baseTyAnnot = match mapLookup baseIdent ctx.compositionCheckEnv.semBaseToTyAnnot with Some ty in ty in 
    let tyAnnot = match d.tyAnnot with TyUnknown _ then baseTyAnnot else d.tyAnnot in 

    -- Create substitution function for param aliasing
    let args = match d.args with Some args then args else [] in 
    let argsIdents : [Name] = map (lam a. a.ident) args in 

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

    let curTyVarSymbols = match mapLookup (langStr, nameGetStr d.ident) ctx.compositionCheckEnv.semTyVarMap with Some ns in ns in  

    -- Substitute parameters, sem symbols and type variables.
    -- 
    -- We substitute the parameters because semantic functions are allowed
    -- to have different parameter names than the sems they include as long 
    -- as the amount of parameters is the same (this is checked by 
    -- composition-check.mc). To handle the case in which the parameter names
    -- are different, we must perform a substitution.
    -- 
    -- For any included cases, we look at the origin language of this case. Any
    -- sem names belonging to the origin language are substituted to the name
    -- of the language fragment we are compiling. We do not just substitute the
    -- name of the current sem, but of all sems in the langauge fragment in order
    -- to properly handle mutual recursion. 
    --
    -- Since semantic funtions can have different type annotations introducing
    -- different symbols, and these symbols may be used in the case bodies,
    -- we also substitute these symbols.
    let work = lam c.
      let origArgs : Option [Name] = match mapLookup c.orig ctx.compositionCheckEnv.semArgsMap with Some args in args in 
      let origArgs : [Name] = match origArgs with Some args then args else [] in

      let origTyVarSymbols = match mapLookup c.orig ctx.compositionCheckEnv.semTyVarMap with Some ns in ns in 

      let pairs = join [
        zip origArgs argsIdents,
        createPairsForSubst ctx c.orig.0 langStr,
        zip origTyVarSymbols curTyVarSymbols
      ] in 

      let subst = mapFromSeq nameCmp pairs in 
      {c with thn = substituteIdentifiersExpr subst c.thn} in 
    let cases = map work cases in

    let cases = map (lam c. {thn = c.thn, pat = c.pat}) cases in
    let body = compileBody cases in 
    recursive let compileArgs = lam args. 
          match args with [h] ++ t then
            TmLam {ident = h.ident,
                   tyAnnot = h.tyAnnot,
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

lang MLangTopLevelCompiler = MLangTopLevel + DeclCompiler + LangDeclAst + SynDeclAst
  sem _gatherBaseSemNames : Set Name -> Decl -> Set Name
  sem _gatherBaseSemNames acc =
  | DeclLang d -> 
    foldl _gatherBaseSemNames acc d.decls 
  | DeclSyn {includes = [], ident = ident} -> 
    setInsert ident acc
  | _ -> acc
  

  sem compileProg : CompilationContext -> MLangProgram -> CompilationResult
  sem compileProg ctx = 
  | prog -> 
    let ctx = {ctx with allBaseSyns = foldl _gatherBaseSemNames (setEmpty nameCmp) prog.decls} in 

    let res = result.foldlM compileDecl ctx prog.decls in
    result.map (lam ctx. withExpr ctx prog.expr) res
end

lang MLangCompiler = MLangAst + MExprAst +
                     MLangTopLevelCompiler + LangDeclCompiler + ExtDeclCompiler +
                     ConDefDeclCompiler + TypeDeclCompiler + UtestDeclCompiler +
                     RecletsDeclCompiler + LetDeclCompiler
  sem compile : CompilationContext -> MLangProgram -> Result CompilationWarning CompilationError Expr
  sem compile ctx =| prog -> 
    match result.consume (compileProg ctx prog) with (_, res) in
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
  match result.consume (checkComposition p) with (_, res) in 
  match res with Right env in
  let ctx = _emptyCompilationContext env in 
  let res = result.consume (compile ctx p) in 
  match res with (_, rhs) in 
  match rhs with Right expr in expr
in

let testError = lam p. 
  match symbolizeMLang symEnvDefault p with (_, p) in 
  match result.consume (checkComposition p) with (_, res) in 
  match res with Right env in
  let ctx = _emptyCompilationContext env in 
  let res = result.consume (compile ctx p) in 
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