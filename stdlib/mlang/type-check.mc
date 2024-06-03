include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"

include "mexpr/type-check.mc"

include "seq.mc"
include "option.mc"

lang DeclTypeCheck = TypeCheck + DeclAst

  sem typeCheckDecl : TCEnv -> Decl -> (TCEnv, Decl)
end

lang DeclLetTypeCheck = DeclTypeCheck + LetDeclAst + LamAst + FunTypeAst + 
                        ResolveType + SubstituteUnknown +
                        NonExpansive + MetaVarDisableGeneralize + 
                        PropagateTypeAnnot + SubstituteNewReprs
  sem typeCheckDecl env =
  | DeclLet d -> 
    -- A DeclLet is treated exactly as a TmLet in the MExpr type checker.
    let newLvl = addi 1 env.currentLvl in
    let tyAnnot = resolveType d.info env false d.tyAnnot in
    let tyAnnot = substituteNewReprs env tyAnnot in
    let tyBody = substituteUnknown d.info {env with currentLvl = newLvl} (Poly ()) tyAnnot in
    match
      if nonExpansive true d.body then
        match stripTyAll tyBody with (vars, stripped) in
        let newTyVarEnv =
          foldr (lam v. mapInsert v.0 (newLvl, v.1)) env.tyVarEnv vars in
        let newEnv = {env with currentLvl = newLvl, tyVarEnv = newTyVarEnv} in
        let body = typeCheckExpr newEnv (propagateTyAnnot (d.body, tyAnnot)) in
        -- Unify the annotated type with the inferred one and generalize
        unify newEnv [infoTy d.tyAnnot, infoTm body] stripped (tyTm body);
        (if env.disableRecordPolymorphism then
           disableRecordGeneralize env.currentLvl tyBody else ());
        match gen env.currentLvl (mapEmpty nameCmp) tyBody with (tyBody, _) in
        (body, tyBody)
      else
        let body = typeCheckExpr {env with currentLvl = newLvl} d.body in
        unify env [infoTy d.tyAnnot, infoTm body] tyBody (tyTm body);
        -- TODO(aathn, 2023-05-07): Relax value restriction
        weakenMetaVars env.currentLvl tyBody;
        (body, tyBody)
    with (body, tyBody) in

    let env = _insertVar d.ident tyBody env in 

    (env, DeclLet {d with body = body,
                          tyAnnot = tyAnnot,
                          tyBody = tyBody})
end

lang DeclLangTypeCheck = DeclTypeCheck + LangDeclAst + SemDeclAst + SynDeclAst +
                         TypeDeclAst 
  sem typeCheckDecl env = 
  | DeclLang d -> 
    let typeDecls = mapOption (lam d. match d with DeclType d then Some (DeclType d) else None ()) d.decls in 
    let synDecls = mapOption (lam d. match d with DeclSyn d then Some (DeclSyn d) else None ()) d.decls in 
    let semDecls = mapOption (lam d. match d with DeclSem d then Some (DeclSem d) else None ()) d.decls in 

    match mapAccumL typeCheckDecl env typeDecls with (env, typeDecls) in 
    match mapAccumL typeCheckDecl env synDecls with (env, synDecls) in

    (env, DeclLang {d with decls = join [typeDecls, synDecls, semDecls]})
end

lang DeclTypeTypeCheck = DeclTypeCheck + TypeDeclAst + VariantTypeAst + ResolveType
  sem typeCheckDecl env =
  | DeclType d ->   
    -- A DeclType is treated exactly as a TmType in the MExpr type checker.
    let tyIdent = resolveType d.info env false d.tyIdent in
    let newLvl = match tyIdent with !TyVariant _ then addi 1 env.currentLvl else 0 in
    let newTyConEnv = mapInsert d.ident (newLvl, d.params, tyIdent) env.tyConEnv in

    let env = {env with tyConEnv = newTyConEnv} in 

    (env, DeclType {d with tyIdent = tyIdent})
end

lang DeclSynTypeCheck = DeclTypeCheck + SynDeclAst + ResolveType
  sem typeCheckDecl env = 
  | DeclSyn d ->
    -- We add a tyConEnv to the env if this is the base syn definition. 
    let env = if null d.includes then
      {env with tyConEnv = mapInsert d.ident (0, d.params, tyvariant_ []) env.tyConEnv}
    else
      env
    in 

    let typeCheckDef = lam env. lam def.
      let tyIdent = resolveType d.info env false def.tyIdent in 
      let tyArrow = TyArrow {from = tyIdent, to = ntycon_ d.ident, info = d.info} in 
      let env = {env with conEnv = mapInsert def.ident (0, tyArrow) env.conEnv} in 
      (env, {def with tyIdent = tyIdent})
    in 

    match mapAccumL typeCheckDef env d.defs with (env, defs) in 
    (env, DeclSyn {d with defs = defs})
end

lang ProgramTypeCheck = DeclTypeCheck + MLangTopLevel
  sem typeCheckProgram : MLangProgram -> MLangProgram
  sem typeCheckProgram =
  | program -> 
    match mapAccumL typeCheckDecl typcheckEnvDefault program.decls with (env, decls) in 
    let expr = typeCheckExpr env program.expr in 
    {decls = decls, expr = expr}
end

lang MLangTypeCheck = ProgramTypeCheck + MExprTypeCheck + MLangPrettyPrint + 
                      DeclLetTypeCheck + DeclTypeTypeCheck + DeclSynTypeCheck +
                      DeclLangTypeCheck
end

mexpr
use MLangTypeCheck in 
let p : MLangProgram = {
  decls = [(decl_ulet_ "x" (int_ 10))],
  expr = addi_ (var_ "x") (int_ 1)
} in 

typeCheckProgram p ; 

let p : MLangProgram = {
  decls = [
    decl_type_ "Foo" [] tyint_,
    decl_let_ "x" (tycon_ "Foo") (int_ 50)
  ],
  expr = (var_ "x")
} in 

typeCheckProgram p ; 

let p : MLangProgram = {
  decls = [
    decl_lang_ "L0" [
      decl_syn_ "SomeSyn" [("Foo", tyint_), ("Bar", tystr_)]
    ],
    decl_let_ "x" (tycon_ "SomeSyn") (conapp_ "Foo" (int_ 10))
  ],
  expr = matchex_ 
      (var_ "x")
      (pcon_ "Foo" (pvar_ "x"))
      (addi_ (var_ "x") (int_ 1))
} in 

typeCheckProgram p ; 

()