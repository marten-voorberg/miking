lang BaseLang 
  syn Expr =
  sem eval =
end

lang ArithLang = BaseLang
  syn Expr += 
  | TmInt {val : Int}
  | TmAdd {lhs : Expr, rhs : Expr} 

  sem eval : < ArithLang::Expr -> Int
  sem eval +=
  | TmInt t -> t.val 
  | TmAdd t -> addi (eval t.lhs) (eval t.rhs)
end

lang ConditionalLang = BaseLang
  syn Expr +=
  | TmIfThenElse {cond : Expr, thn : Expr, els : Expr}

  -- sem eval : < ConditionalLang::Expr -> Int
  sem eval += 
  | TmIfThenElse t ->
    if eqi (eval t.cond) 0 then
      eval t.thn
    else 
      eval t.els
end 

lang BigLang = ConditionalLang + ArithLang end

mexpr
use BigLang in 
let e0 = TmInt {TmIntType of val = 0} in 
let e1 = TmInt {TmIntType of val = 1} in 
let e42 = TmInt {TmIntType of val = 42} in 
let eAdd = TmAdd {TmAddType of lhs = TmInt {TmIntType of val = 23},
                                rhs = TmInt {TmIntType of val = 42}} in 

let ite1 = TmIfThenElse {TmIfThenElseType of cond = e0, thn = e42, els = eAdd} in 
let ite2 = TmIfThenElse {TmIfThenElseType of cond = e1, thn = e42, els = eAdd} in 

utest eval ite1 with 42 using eqi in 
utest eval ite2 with 65 using eqi in 
()