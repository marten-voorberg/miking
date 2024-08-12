include "mexpr/type-check.mc"
include "mexpr/ast.mc"

include "map.mc"
include "stringid.mc"
include "set.mc"

lang ExtRecMonomorphise = RecordAst + ExtRecordAst + MatchAst 
  sem monomorphiseExpr : ExtRecEnvType -> Expr -> Expr
  sem monomorphiseExpr env = 
  | TmRecType t -> monomorphiseExpr env t.inexpr
  | TmRecField t -> monomorphiseExpr env t.inexpr 
  | TmExtRecord t -> 
    match mapLookup t.ident env with Some labelToType in 

    let allLabels = mapKeys labelToType in 
    let presentLabels = setOfKeys t.bindings in 

    let f = lam label.
      if setMem label presentLabels then 
        match mapLookup label t.bindings with Some e in (stringToSid label, ulam_ "" e)
      else 
        (stringToSid label, ulam_ "" never_)
    in 

    let bindings = map f allLabels in 

    TmRecord {bindings = mapFromSeq cmpSID bindings,
              ty = tyunknown_,
              info = t.info}
  | TmExtProject t -> 
    let n = nameSym "x" in 
    TmMatch {target = t.e, 
             pat = prec_ [(t.label, npvar_ n)] ,
             thn = appf1_ (nvar_ n) uunit_,
             els = never_,
             ty = t.ty,
             info = t.info}
  | TmExtUpdate t -> 
    let work = lam acc. lam label. lam expr. 
      TmRecordUpdate {rec = acc, 
                      key = stringToSid label, 
                      value = ulam_ "" expr, 
                      ty = tyunknown_,
                      info = t.info} in 
    mapFoldWithKey work t.e t.bindings
  | TmExtExtend t -> 
    let work = lam acc. lam label. lam expr. 
      TmRecordUpdate {rec = acc, 
                      key = stringToSid label, 
                      value = ulam_ "" expr, 
                      ty = tyunknown_,
                      info = t.info} in 
    mapFoldWithKey work t.e t.bindings
  | expr -> 
    smap_Expr_Expr (monomorphiseExpr env) expr
    

  sem monomorphiseType : ExtRecEnvType -> Type -> Type
end