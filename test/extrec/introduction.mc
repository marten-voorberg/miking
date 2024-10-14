let and = lam b1. lam b2.
  if b1 then b2 else false
  
recursive let eqString = lam s1. lam s2.
  match (s1, s2) with ([], []) then 
    true
  else match (s1, s2) with ([h1] ++ t1, [h2] ++ t2) then
    and (eqc h1 h2) (eqString t1 t2)
  else 
    false
end

lang Base
  syn Term = 

  sem isValue = 
  | _ -> false

  sem step = 

  sem subst ident term =
end

lang LambdaCalculus = Base
  syn Term += 
  | TmApp {lhs : Term, rhs : Term}
  | TmAbs {ident : String, body : Term}
  | TmVar {ident : String}

  sem step += 
  | TmApp t -> 
    match t.lhs with TmAbs t2 then
      subst t2.ident t2.body t.rhs  
    else if isValue t.lhs then 
      TmApp {TmAppType of lhs = t.lhs, rhs = step t.rhs} 
    else 
      TmApp {TmAppType of lhs = step t.lhs, rhs = t.rhs} 
  | TmVar _ -> error "Stuck!"
  | TmAbs _ -> error "Stuck!"

  sem subst ident term +=
  | TmVar t -> if eqString ident t.ident then term 
               else TmVar t
  | TmApp t -> TmApp {TmAppType of lhs = subst ident term t.lhs, 
                                   rhs = subst ident term t.rhs}
  | TmAbs t -> if eqString ident t.ident then TmAbs t else
               TmAbs {TmAbsType of ident = t.ident, 
                                   body = subst ident term t.body}

  sem isValue +=
  | TmAbs _ -> true
end

lang Arith = Base
  syn Term += 
  | TmInt {val : Int}
  | TmAdd {lhs : Term, rhs : Term}

  sem step +=
  | TmAdd t ->
    match (t.lhs, t.rhs) with (TmInt t1, TmInt t2) then
      TmInt {TmIntType of val = addi t1.val t2.val}
    else match t.lhs with TmInt _ then
      TmAdd {TmAddType of lhs = t.lhs, rhs = step t.rhs}
    else 
      TmAdd {TmAddType of lhs = step t.lhs, rhs = t.rhs}
  | TmInt _ -> error "Stuck!"

  sem isValue +=
  | TmInt _ -> true

  sem subst ident term += 
  | TmInt t -> TmInt t
  | TmAdd t -> TmAdd {TmAddType of lhs = subst ident term t.lhs, 
                                   rhs = subst ident term t.rhs}
end

lang LambdaCalculusArith =  LambdaCalculus + Arith
end

mexpr
use Arith in 

let pprint = lam tm.  match tm with TmInt t then print "int" else print "not int" in

let int_ = lam v. TmInt {TmIntType of val = v} in 
let add_ = lam l. lam r. TmAdd {TmAddType of lhs = l, rhs = r} in 

let tm = add_ (int_ 1) (int_ 2) in 

let result = step tm in 

pprint result ;

()
            