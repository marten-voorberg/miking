include "stdlib/string.mc"

let and = lam b1. lam b2.
  if b1 then b2 else false

lang LC 
  syn Ty = 

  syn Term = 
  | TmApp {lhs : Term, rhs : Term}
  | TmAbs {ident : String, body : Term}
  | TmVar {ident : String}

  sem eval = 
  | TmApp outer -> 
    match outer.lhs with TmAbs t then
      eval (subst t.ident outer.rhs t.body)
    else 
      eval (TmApp {TmAppType of lhs = eval outer.lhs, rhs = outer.rhs})

  sem subst ident term =
  | TmVar t -> if eqString ident t.ident then term else TmVar t
  | TmApp t -> TmApp {TmAppType of lhs = subst ident term t.lhs, 
                                   rhs = subst ident term t.rhs}
  | TmAbs t -> if eqString ident t.ident then TmAbs t 
               else TmAbs {TmAbsType of ident = t.ident, 
                                        body = subst ident term t.body}
end

lang IntArith = LC
  syn Term += 
  | TmAdd {lhs : Term, rhs : Term}
  | TmInt {val : Int}

  sem eval +=
  | TmInt t -> TmInt t 
  | TmAdd t -> 
    match eval t.lhs with TmInt l then 
      match eval t.rhs with TmInt r then
        TmInt {TmIntType of val = addi l.val r.val}
      else 
        error "..."
    else 
      error "..."

  sem subst ident tm +=
  | TmInt t -> TmInt t
  | TmAdd t -> TmAdd {TmAddType of lhs = subst ident tm t.lhs, 
                                   rhs = subst ident tm t.rhs}
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

let expr = TmApp {TmAppType of lhs = add1, rhs = TmInt {TmIntType of val = 22}} in
let result = eval expr in 
(match result with TmInt t then
  (utest t.val with 23 in ())
else 
  error "Test failed, result is not int!");

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