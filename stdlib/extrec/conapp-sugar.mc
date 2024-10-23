include "ast.mc"

include "mlang/ast.mc"

include "mexpr/ast.mc"

include "name.mc"
include "map.mc"

lang ExtrecConappSugar = MLangAst + MExprAst + ExtRecordAst 
  sem handleConappSugar = 
  | prog -> 
    let ctx = foldl (sfold_Decl_Decl collectConappSugarEnv) (mapEmpty nameCmp) prog.decls in 
    let decls = map (handleConappSugar_Decl ctx) prog.decls in 
    let expr = handleConappSugar_Expr ctx prog.expr in 
    {decls = decls, expr = expr}

  sem collectConappSugarEnv acc = 
  | DeclSyn d -> 
    let work = lam acc. lam def.mapInsert def.ident def.tyName acc in 
    foldl work acc d.defs
  | other -> 
    sfold_Decl_Decl collectConappSugarEnv acc other

  sem handleConappSugar_Decl ctx =
  | decl -> 
    let decl = smap_Decl_Decl (handleConappSugar_Decl ctx) decl in
    smap_Decl_Expr (handleConappSugar_Expr ctx) decl

  sem handleConappSugar_Expr ctx =
  | TmConApp (app & {body = TmRecord rec}) -> 
    match mapLookup app.ident ctx with Some recIdent then
      let bindings = mapToSeq rec.bindings in 
      let work = lam p. (sidToString p.0, handleConappSugar_Expr ctx p.1) in 
      let bindings = map work bindings in 
      let bindings = mapFromSeq cmpString bindings in 
      let r = TmExtRecord {bindings = bindings,
                           ident = recIdent,
                           ty = rec.ty, 
                           info = rec.info} in 
      TmConApp {app with body = r}
    else 
      TmConApp app 
  | other -> 
    smap_Expr_Expr (handleConappSugar_Expr ctx) other
end