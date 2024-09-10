include "mexpr/type-check.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

include "map.mc"
include "stringid.mc"
include "set.mc"

lang ExtRecMonomorphise = RecordAst + ExtRecordAst + MatchAst + ExtRecordTypeAst + MExprAst + MExprPrettyPrint
  sem monomorphiseExpr : ExtRecEnvType -> Set Name -> Expr -> Expr
  sem monomorphiseExpr env names = 
  | TmRecType t -> monomorphiseExpr env names t.inexpr
  | TmRecField t -> monomorphiseExpr env names t.inexpr 
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
                      value = ulam_ "" expr, 
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


  sem monomorphiseType : ExtRecEnvType -> Type -> Type
end