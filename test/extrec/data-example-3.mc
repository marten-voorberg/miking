-- mexpr
-- type Expr in 
-- con TmInt : Int -> Expr in 
-- con TmAdd : (Expr, Expr) -> Expr in 

-- recursive let eval : all m :: {Expr [< TmInt TmAdd]}.
--                      Expr{m} -> Int = 
--   lam expr.
--     switch expr
--       case TmInt val then val
--       case TmAdd (l, r) then addi (eval l) (eval r)
--     end 
-- in 
-- utest eval (TmAdd (TmInt 5, TmInt -1)) with 4 in ()