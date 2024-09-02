include "mlang/ast.mc"

include "map.mc"
include "name.mc"
include "digraph.mc"
include "set.mc"

type ResolveStaticEnv = {
  tydeps : Map Name (Set Name)
}
type ResolveLangEnv = {
  prodFields : Map Name (Set Name),
  sumFields : Map Name (Set Name)
}
type ResolveQualifiedNameEnv = {
  langEnvs : Map Name ResolveLangEnv
}

lang ResolveQualifiedName = MLangAst + RecordTypeAst + QualifiedTypeAst + 
                            MLangPrettyPrint + ExtRecordTypeAst
                            
  sem resolveQualifiedNameProgram tydeps = 
  | prog -> 
    let staticEnv = {tydeps = tydeps} in 
    let accEnv = {langEnvs = mapEmpty nameCmp} in 

    match smap_Prog_Decl (resolveQualifiedNames staticEnv) accEnv prog
    with (accEnv, prog) in 

    let resolver = resolveTy staticEnv accEnv in 
    recursive let worker = lam expr.
      let expr = smap_Expr_Type resolver expr in 
      smap_Expr_Expr worker expr
    in 

    {prog with expr = worker prog.expr}

  sem resolveQualifiedNames : ResolveStaticEnv -> 
                              ResolveQualifiedNameEnv -> 
                              Decl -> 
                              (ResolveQualifiedNameEnv, Decl)
  sem resolveQualifiedNames staticEnv accEnv =
  | DeclLang d & decl ->
    let emptyLangEnv : ResolveLangEnv = {prodFields = mapEmpty nameCmp,
                                         sumFields = mapEmpty nameCmp} in 

    let includedLangEnvs : [ResolveLangEnv] = map
      (lam n. match mapLookup n accEnv.langEnvs with Some env in env)
      d.includes in 

    let f = lam lhs. lam rhs. 
      let lhs = optionGetOrElse (lam. mapEmpty nameCmp) lhs in 
      let rhs = optionGetOrElse (lam. mapEmpty nameCmp) rhs in 
      Some (mapUnion lhs rhs) in 

    let merger : ResolveLangEnv -> ResolveLangEnv -> ResolveLangEnv = lam lhs. lam rhs.
      {sumFields = mapMerge f lhs.sumFields rhs.sumFields,
       prodFields = mapMerge f lhs.prodFields rhs.prodFields} in 

    let newLangEnv : ResolveLangEnv = foldl merger emptyLangEnv includedLangEnvs in 

    let accEnv : ResolveQualifiedNameEnv = {accEnv with langEnvs = mapInsert d.ident newLangEnv accEnv.langEnvs} in

    match smapAccumL_Decl_Decl (resolveQualifiedNamesWithinLang d.ident staticEnv) accEnv decl with
    (accEnv, decl) in 

    match decl with DeclLang d in 

    (accEnv, DeclLang {d with decls = d.decls})
  | other -> 
    let worker = resolveTy staticEnv accEnv in 
    let other = smap_Decl_Type worker other in 
    let other = smap_Decl_Expr (lam e. smap_Expr_Type worker e) other in 
    (accEnv, other)

  sem _updateProdFields langIdent accEnv =
  | {ident = ident, tyIdent = TyRecord r} -> 
    match mapLookup langIdent accEnv.langEnvs with Some innerEnv in 

    let ident = nameNoSym (concat (nameGetStr ident) "Type") in 

    let labels : [SID] = mapKeys r.fields in 
    let labels : [Name] = map (lam sid. nameNoSym (sidToString sid)) labels in 
    
    let oldSet = mapLookupOr
      (mapEmpty nameCmp) 
      (nameRemoveSym ident)
      innerEnv.prodFields in 
    let newSet = foldr setInsert oldSet labels in 
    let innerEnv = {innerEnv with prodFields = mapInsert (nameRemoveSym ident) newSet innerEnv.prodFields} in 
  
    {accEnv with langEnvs = mapInsert langIdent innerEnv accEnv.langEnvs}
  | other -> 
    accEnv
  
  sem resolveQualifiedNamesWithinLang langIdent staticEnv accEnv = 
  | DeclSyn d & decl -> 
    match mapLookup langIdent accEnv.langEnvs with Some innerEnv in 

    let s = mapLookupOr
      (setEmpty nameCmp)
      (nameRemoveSym d.ident)
      innerEnv.sumFields in 
    let addedConstructors = map (lam d. d.ident) d.defs in
    let newS = foldr setInsert s addedConstructors in 

    let innerEnv = {innerEnv with sumFields = mapInsert (nameRemoveSym d.ident) newS innerEnv.sumFields} in 
    let accEnv = {accEnv with langEnvs = mapInsert langIdent innerEnv accEnv.langEnvs} in 

    let accEnv = foldl (_updateProdFields langIdent) accEnv d.defs in 

    let decl = smap_Decl_Type (resolveTy staticEnv accEnv) decl in 
    (accEnv, decl)
  | SynDeclProdExt d & decl -> 
    let accEnv = foldl (_updateProdFields langIdent) accEnv d.individualExts in 
    let decl = smap_Decl_Type (resolveTy staticEnv accEnv) decl in 
    (accEnv, decl)
  | decl ->
    -- todo: make this non-shallow...
    let decl = smap_Decl_Type (resolveTy staticEnv accEnv) decl in 
    (accEnv, decl)

  sem resolveTy : ResolveStaticEnv -> ResolveQualifiedNameEnv -> Type -> Type
  sem resolveTy staticEnv accEnv =
  | ty -> 
    match resolveTyHelper staticEnv accEnv [] ty with (acc, ty) in 

    let worker = lam tyAcc. lam pair. 
      match pair with (ident, kind) in 
      nstyall_ ident kind tyAcc 
    in 
    foldl worker ty acc 

  sem resolveTyHelper : ResolveStaticEnv -> ResolveQualifiedNameEnv -> [(Name, Kind)] -> Type -> ([(Name, Kind)], Type)
  sem resolveTyHelper staticEnv accEnv acc = 
  | TyQualifiedName t ->
    let env : ResolveLangEnv = mapLookupOrElse 
      (lam. errorSingle [t.info] " * Langauge on lhs does not exist!") 
      t.lhs 
      accEnv.langEnvs
    in
    
    match mapLookup t.rhs env.prodFields with Some prodFields then
      let prodFiels = setMap nameCmp nameRemoveSym prodFields in 
      let kindMap = mapFromSeq nameCmp [(t.rhs, {lower = prodFields, upper = None ()})] in 
      let kind = Data {types = kindMap} in 
      printLn (kind2str kind);
      let ident = nameSym "ss" in 
      (cons (ident, kind) acc, TyExtRec {info = t.info, ident = t.rhs, ty = ntyvar_ ident}) 
    else match mapLookup t.rhs env.sumFields with Some sumFields then
      error "TODO: CREATE A SUM TYPE"
    else 
      errorSingle [t.info] "* Unknown rhs of qualified type!"

  | ty -> 
    smapAccumL_Type_Type (resolveTyHelper staticEnv accEnv) acc ty 
end