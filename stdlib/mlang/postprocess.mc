include "name.mc"
include "map.mc"
include "option.mc"

include "mexpr/ast.mc"

let createSubst : Map (String, String) Name -> (Name -> Name) = lam m.
  let pairs = mapToSeq m in 
  let finder = lam n1. lam p.
    match p with (_, n2) in 
    nameEqSym n1 n2
  in

  lam n.
    match find (finder n) pairs with Some ((origLang, semName), sym) then
      nameSetStr sym (join [origLang, "_", semName])
    else 
      n


lang PostProcess = MExprAst 
  sem postprocess : Map (String, String) Name -> Expr -> Expr
  sem postprocess m =| e ->
    let sub = createSubst m in 
    worker sub e

  sem worker : (Name -> Name) -> Expr -> Expr
  sem worker sub = 
  | TmVar t -> TmVar {t with ident = sub t.ident}
  | TmLet t -> TmLet {t with ident = sub t.ident}
  | other -> smap_Expr_Expr (worker sub) other
end
