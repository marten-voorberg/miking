include "stdlib/string.mc"

let and = lam b1. lam b2.
  if b1 then b2 else false

lang LC 
  syn Ty = 
  syn Term = 
  | TmApp {lhs : Term, rhs : Term}
  | TmAbs {ident : String, body : Term}
  | TmVar {ident : String}
end
lang IntArith = LC
  syn Term += 
  | TmAdd {lhs : Term, rhs : Term}
  | TmInt {val : Int}
end

lang STLC = LC + IntArith
  syn Ty += 
  | TyArrow {lhs : Ty, rhs : Ty}
  | TyInt {dummy : ()}

  syn Term *= 
  | TmAbs {tyAnnot : Ty}

  sem eqType =
  | (TyInt _, TyInt _) -> true
  | (TyArrow t1, TyArrow t2) -> and (eqType (t1.lhs, t2.lhs)) (eqType (t1.rhs, t2.rhs))
  | _ -> false

  sem getFromEnv ident = 
  | [(h, ty)] ++ t ->
    if eqString h ident then
      ty
    else 
      getFromEnv ident t
  | [] -> error "Ident not found in env!"

  sem typeCheck env = 
  | TmVar t -> getFromEnv t.ident env
  | TmAbs t -> TyArrow {TyArrowType of lhs = t.tyAnnot, rhs = typeCheck (cons (t.ident, t.tyAnnot) env) t.body}
  | TmApp t -> 
    match typeCheck env t.lhs with TyArrow inner then
      match inner with {lhs = lhs, rhs = rhs} in 
      if eqType (lhs, (typeCheck env t.rhs)) then rhs
      else error "..."
    else error "..."
  | TmInt _ -> TyInt {TyIntType of dummy = ()}
  | TmAdd _ -> TyInt {TyIntType of dummy = ()}
end

mexpr 
use STLC in 
print "\nSTLC tests:\n";
let tyInt = TyInt {TyIntType of dummy = ()} in 
let add = TmAdd {TmAddType of lhs = TmVar {TmVarType of ident = "x"}, 
                              rhs = TmInt {TmIntType of val = 1}} in 
let add1 = TmAbs {TmAbsType of ident = "x", tyAnnot = tyInt, body = add} in 

let actualTy = typeCheck [] add1 in 
let expectedType = TyArrow {TyArrowType of lhs = tyInt, rhs = tyInt} in 
utest actualTy with expectedType using (lam l. lam r. eqType (l, r)) in 

-- (match actualTy with TyArrow t then  
--   print ".";
--   match t.lhs with TyInt _ then
--     print ".";
--     match t.rhs with TyInt _ then 
--       print "."
--     else
--       error "Failure, expected int type"
--   else 
--     error "Failure, expected int type"
-- else 
--   error "Failure, expected arrow type!" ); 
-- ()
()