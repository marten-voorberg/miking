include "mexpr/ast.mc"
include "mexpr/type-check.mc"

include "error.mc"
include "map.mc"

lang ExtRecCollectEnv = MExprAst + ExtRecordAst
  sem collectEnv : ExtRecEnvType -> Expr -> ExtRecEnvType
  sem collectEnv env = 
  | TmRecType t -> 
    match mapLookup t.ident env with Some _ then
      errorMulti 
        [(t.info, nameGetStr t.ident)]
        "An extensible record type with this Name already exists!"
    else 
      let env = mapInsert t.ident (mapEmpty cmpString) env in 
      collectEnv env t.inexpr
  | TmRecField t -> 
    match t.tyIdent with TyArrow {from = lhs, to = rhs} then
      match lhs with TyCon {ident = ident} then 
        match mapLookup ident env with Some labelTypeMap then
          let labelTypeMap = mapInsert t.label rhs labelTypeMap in 
          let env = mapInsert ident labelTypeMap env in 
          collectEnv env t.inexpr
        else 
          errorMulti 
            [(t.info, "")]
            "The yyCon on rhs must be an extensible record type!"
      else
        errorMulti 
          [(t.info, "")]
          "The type of a record field must have TyCon on rhs!"
    else  
      errorMulti 
        [(t.info, "")]
        "The type of a record field must be an arrow type!"
  | expr -> 
    sfold_Expr_Expr collectEnv env expr
end
