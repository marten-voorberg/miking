include "mexpr/type-check.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

include "mlang/compile.mc"

include "map.mc"
include "stringid.mc"
include "set.mc"

lang ExtRecMonomorphise = RecordAst + ExtRecordAst + MatchAst + 
                          MExprAst + MExprPrettyPrint +
                          TypeAbsAst

  sem monomorphiseExpr : ExtRecEnvType -> Set Name -> Expr -> Expr
  sem monomorphiseExpr env names = 
  | TmRecType t -> 
    match mapLookup t.ident env.defs with Some labelToType in 

    let fields = mapFoldWithKey 
      (lam acc. lam label. lam pair.
        match pair with (_, TyAbs {body = ty}) in 
        let ty = removeExtRecTypes_Type () ty in 
        let ty = TyArrow {info = NoInfo (),
                          from = tyunit_,
                          to = ty} in 
        mapInsert (stringToSid label) ty acc) 
      (mapEmpty cmpSID)
      labelToType
    in 

    TmType {ident = t.ident,
             -- params = cons mapParamIdent t.params,
            params = t.params,
            tyIdent = TyRecord {info = NoInfo (), fields = fields},
            inexpr = monomorphiseExpr env names t.inexpr,
            ty = t.ty,
            info = t.info}
  | TmRecField t -> monomorphiseExpr env names t.inexpr 
  | TmRecordUpdate t & tm -> 
    match tyTm t.rec with TyCon tyCon then 
      TmRecordUpdate {t with value = nulam_ (nameNoSym "") t.value,
                             rec = monomorphiseExpr env names t.rec}
    else 
      tm 
  | TmExtRecord t -> 
    match mapLookup t.ident env.defs with Some labelToType in 

    let allLabels = mapKeys labelToType in 
    let presentLabels = setOfKeys t.bindings in 

    let f = lam label.
      if setMem label presentLabels then 
        match mapLookup label t.bindings with Some e in (stringToSid label, ulam_ "" e)
      else 
        (stringToSid label, ulam_ "" never_)
    in 

    let bindings = map f allLabels in 
    let bindings = mapFromSeq cmpSID bindings in 

    let bindings = mapMap (monomorphiseExpr env names) bindings in 

    TmRecord {bindings = bindings,
              ty = tyunknown_,
              info = t.info}
  | TmExtExtend t -> 
    let work = lam acc. lam label. lam expr. 
      TmRecordUpdate {rec = acc, 
                      key = stringToSid label, 
                      value = nulam_ (nameNoSym "") expr, 
                      ty = tyunknown_,
                      info = t.info} in 
    mapFoldWithKey work t.e t.bindings
  | TmVar t & tm -> 
    if setMem t.ident names then 
      appf1_ tm (uunit_)
    else 
      tm
  -- | TmMatch t & tm ->
  --   printLn "Encountered match!";
  --   printLn (type2str (_inspectTyWithinAlias2 (tyTm t.target)));
  --   match _inspectTyWithinAlias2 (tyTm t.target) with TyExtRec extRec then
  --     printLn "\tEncountered correct Target!";
  --     match t.pat with PatRecord patRec & p then
  --       printLn "\t\tEncountered correct pattern!";
  --       recursive let collectBoundNames = lam acc. lam pat. 
  --         match pat with PatNamed {ident = PName ident} then setInsert ident acc 
  --         else sfold_Pat_Pat collectBoundNames acc pat
  --       in
  --       let boundNames = collectBoundNames (setEmpty nameCmp) p in 
  --       iter (lam n. printLn (nameGetStr n)) (setToSeq boundNames) ;
  --       tm
  --     else
  --       errorSingle [t.info] " * This match is too complicated for crude monomorhpization."
  --   else
  --     tm
  | expr -> 
    smap_Expr_Expr (monomorphiseExpr env names) expr
  
  sem _inspectTyWithinAlias2 : Type -> Type
  sem _inspectTyWithinAlias2 = 
  | TyAlias {content = content} -> _inspectTyWithinAlias2 content
  | TyApp t -> _inspectTyWithinAlias2 t.rhs
  | ty -> ty


  sem removeExtRecTypes_Expr env = 
  | TmType t ->
    TmType {t with params = filter (lam n. not (nameEq mapParamIdent n)) t.params,
                   tyIdent = removeExtRecTypes_Type env t.tyIdent,
                   ty = removeExtRecTypes_Type env t.ty,
                   inexpr = removeExtRecTypes_Expr env t.inexpr}
  | expr -> 
    let expr = smap_Expr_Type (removeExtRecTypes_Type env) expr in  
    let expr = smap_Expr_TypeLabel (removeExtRecTypes_Type env) expr in 
    smap_Expr_Expr (removeExtRecTypes_Expr env) expr
    
  sem removeExtRecTypes_Type env = 
  | TyQualifiedName t -> 
    TyCon {ident = t.rhs, info = t.info, data = tyunknown_}
  | TyCon t -> TyCon {t with data = tyunknown_}
  | TyApp {rhs = TyVar tyVar} & TyApp t ->
    if nameEq tyVar.ident mapParamIdent then 
      removeExtRecTypes_Type env t.lhs 
    else if eqString (nameGetStr tyVar.ident) "m" then
      removeExtRecTypes_Type env t.lhs 
    else if eqString (nameGetStr tyVar.ident) "ss" then
      removeExtRecTypes_Type env t.lhs 
    else 
      TyApp {t with lhs = removeExtRecTypes_Type env t.lhs,
                    rhs = removeExtRecTypes_Type env t.rhs}
  | TyAll t & ty ->
    match t.kind with Data _ then
      removeExtRecTypes_Type env t.ty
    else if nameEq t.ident mapParamIdent then
      removeExtRecTypes_Type env t.ty
    else 
      TyAll {t with ty = removeExtRecTypes_Type env t.ty,
                    kind = removeExtRecTypes_Kind env t.kind}
  | ty -> 
    smap_Type_Type (removeExtRecTypes_Type env) ty 

  sem removeExtRecTypes_Kind env = 
  sem removeExtRecTypes_Kind =
  | Data k & kind -> 
    -- printLn (kind2str kind);
    let pred = lam n. not (strEndsWith (nameGetStr n) "Type") in 
    let kind = Data {k with types = mapFilterWithKey (lam k. lam. pred k) k.types} in 
    -- printLn (kind2str kind);
    kind
  | kind -> 
    smap_Kind_Type (removeExtRecTypes_Type env) kind



end