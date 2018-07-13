

(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   boot.ml is the main entry point for first stage of the
   bootstrapped Miking compiler. The bootstapper is interpreted and
   implemented in OCaml. Note that the Miking bootstrapper
   only implements a subset of the Ragnar language.
*)

open Utils
open Ustring.Op
open Printf
open Ast
open Msg
open Pprint
open Errors

(* Debug options *)
let enable_debug_type_checking = false


(* Generic type checking function *)
let tydebug desc strlst tmlst tylst =
  if not enable_debug_type_checking then () else (
  printf "------------ %s START ------- \n" desc;
  List.iter (fun (x,xs) -> uprint_endline (us x ^. us": " ^. xs)) strlst;
  List.iter (fun (x,t) -> uprint_endline (us x ^. us": " ^. (pprint true t))) tmlst;
  List.iter (fun (x,ty) -> uprint_endline (us x ^. us": " ^. (pprint_ty ty))) tylst;
  printf "------------- %s END -------- \n" desc)

(* Perform index shifting, as part of the capture free type substitution *)
let rec tyShift d c ty =
  match ty with
  | TyGround(fi,gt) -> ty
  | TyArrow(fi,ty1,ty2) -> TyArrow(fi,tyShift d c ty1, tyShift d c ty2)
  | TyVar(fi,x,k) -> TyVar(fi,x,if k < c then k else k + d)
  | TyAll(fi,x,kind,ty2) -> TyAll(fi,x,kind, tyShift d (c+1) ty2)
  | TyLam(fi,x,kind,ty1) -> TyLam(fi,x,kind, tyShift d (c+1) ty1)
  | TyApp(fi,ty1,ty2) -> TyApp(fi, tyShift d c ty1, tyShift d c ty2)
  | TyDyn -> TyDyn


(* Substitutes type [tys] in ty *)
let tySubst tys ty =
  let rec subst j s ty =
    (match ty with
    | TyGround(fi,gt) -> ty
    | TyArrow(fi,ty1,ty2) -> TyArrow(fi, subst j s ty1, subst j s ty2)
    | TyVar(fi,x,k) -> if k = j then s else TyVar(fi,x,k)
    | TyAll(fi,x,kind,ty2) -> TyAll(fi,x,kind, subst (j+1) (tyShift 1 0 s) ty2)
    | TyLam(fi,x,kind,ty1) -> TyLam(fi,x,kind, subst (j+1) (tyShift 1 0 s) ty1)
    | TyApp(fi,ty1,ty2) -> TyApp(fi, subst j s ty1, subst j s ty2)
    | TyDyn -> TyDyn)
  in
    subst 0 tys ty


let tySubstTop tys ty =
  tyShift (-1) 0 (tySubst (tyShift 1 0 tys) ty)

(* Checks if two kinds are equal *)
let rec kindEqual ki1 ki2 =
  match ki1,ki2 with
  | KindStar(_),KindStar(_) -> true
  | KindArrow(_,ki11,ki12),KindArrow(_,ki21,ki22) ->
      (kindEqual ki11 ki21) && (kindEqual ki12 ki22)
  | KindArrow(_,_,_),_ | _,KindArrow(_,_,_) -> false


(* Parallel reduction. Reduce types into normal form.
   Used for checking type equivalence *)
let normTy ty =
  let rec reduce ty =
    match ty with
    | TyGround(fi,gt) -> ty
    | TyArrow(fi,ty1,ty2) -> TyArrow(fi,reduce ty1,reduce ty2)
    | TyVar(fi,x,n) -> TyVar(fi,x,n)
    | TyAll(fi,x,ki1,ty1) -> TyAll(fi,x,ki1,reduce ty1)
    | TyLam(fi,x,ki1,ty1) -> TyLam(fi,x,ki1,reduce ty1)
    | TyApp(fi,ty1,ty2) ->
      (match reduce ty1, reduce ty2 with
       | TyLam(fi3,x,ki3,ty3),ty4 -> reduce (tySubstTop ty4 ty3)
       | ty1',ty2' -> TyApp(fi,ty1',ty2'))
    | TyDyn -> TyDyn
  in
    reduce ty


(* Checks if two types are equal *)
let tyequal ty1 ty2 =
  let rec tyrec ty1 ty2 =
    match ty1,ty2 with
    | TyGround(_,g1),TyGround(_,g2) -> g1 = g2
    | TyArrow(_,ty11,ty12),TyArrow(_,ty21,ty22) ->
      tyrec ty11 ty21 &&  tyrec ty21 ty22
    | TyVar(_,_,n1),TyVar(_,_,n2) -> n1 = n2
    | TyAll(_,x1,_,ty1),TyAll(_,x2,_,ty2) -> tyrec ty1 ty2
    | TyLam(fi1,x1,kind1,ty1), TyLam(fi2,x2,kind2,ty2) ->
      tyrec ty1 ty2 && kindEqual kind1 kind2
    | TyApp(fi1,ty11,ty12), TyApp(fi2,ty21,ty22)->
      tyrec ty11 ty21 && tyrec ty12 ty22
    | TyDyn,TyDyn -> true
    | TyGround(_,_), _ | _,TyGround(_,_) -> false
    | TyArrow(_,_,_), _ | _,TyArrow(_,_,_) -> false
    | TyVar(_,_,_), _ | _,TyVar(_,_,_) -> false
    | TyAll(_,_,_,_), _ | _,TyAll(_,_,_,_) -> false
    | TyLam(fi,x,kind,ty1),_ | _,TyLam(fi,x,kind,ty1) -> false
    | TyApp(fi,ty1,ty2),_ | _,TyApp(fi,ty1,ty2)-> false
  in
    tyrec ty1 ty2


(* Returns the type of a constant value *)
let type_const c =
  let tyarr t1 t2 = TyArrow(NoInfo,t1,t2) in
  let tybool = TyGround(NoInfo,GBool) in
  let tyint =  TyGround(NoInfo,GInt) in
  let tyfloat =  TyGround(NoInfo,GFloat) in
  match c with
  (* MCore intrinsic: Boolean constant and operations *)
  | CBool(_) -> tybool
  | Cnot -> tyarr tybool tybool
  | Cand(None) | Cor(None) -> tyarr tybool (tyarr tybool tybool)
  | Cand(_) | Cor(_) -> tyarr tybool tybool
(* MCore intrinsic: Integer constant and operations *)
  | CInt(_) -> tyint
  | Caddi(None) | Csubi(None) | Cmuli(None)| Cdivi(None) | Cmodi(None)
      -> tyarr tyint (tyarr tyint tyint)
  | Caddi(_) | Csubi(_) | Cmuli(_)| Cdivi(_) | Cmodi(_) | Cnegi
      -> tyarr tyint tyint
  | Clti(None) | Cleqi(None) | Cgti(None)  | Cgeqi(None) | Ceqi(None)
               | Cneqi(None) | Cslli(None) | Csrli(None) | Csrai(None)
      -> tyarr tyint (tyarr tyint tybool)
  | Clti(_) | Cleqi(_) | Cgti(_)  | Cgeqi(_) | Ceqi(_)
            | Cneqi(_) | Cslli(_) | Csrli(_) | Csrai(_)
      -> tyarr tyint tybool
(* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(_) -> tyfloat
  | Caddf(None) | Csubf(None) | Cmulf(None) | Cdivf(None)
      -> tyarr tyfloat (tyarr tyfloat tyfloat)
  | Caddf(_) | Csubf(_) | Cmulf(_) | Cdivf(_) | Cnegf
      -> tyarr tyfloat tyfloat
(* Mcore intrinsic: Polymorphic integer and floating-point numbers *)
  | Cadd(_) | Csub(_) | Cmul(_) | Cdiv(_) | Cneg
(* MCore debug and I/O intrinsics *)
  | CDStr | CDPrint | CPrint | CArgv
(* MCore unified collection type (UCT) intrinsics *)
  | CConcat(_)
(* Ragnar temp functions for handling polymorphic arguments *)
  | CPolyEq(_)
  | CPolyNeq(_)
(* Atom - an untyped lable that can be used to implement domain specific constructs *)
  | CAtom(_,_)
    -> error NoInfo (us"The constant is not supported in the current type system")




(* Returns the kind of a specific type *)
let rec kindof env ty =
  match ty with
  | TyGround(fi,gt) -> KindStar(fi)
  | TyArrow(fi,ty1,ty2) ->
    let kcheck ki fi  =
      match ki with
      | KindStar(_) -> ()
      | _ -> error fi (us"Type has kind " ^.
             pprint_kind ki ^. us", but kind * was expected")
    in kcheck (kindof env ty1) (ty_info ty1);
       kcheck (kindof env ty2) (ty_info ty2);
       KindStar(fi)
  | TyVar(fi,x,n) ->
      (match List.nth_opt env n with
       | Some(TyenvTyvar(y,_,ki1,_)) -> ki1
       | _ -> error fi (us"Variable '" ^. x ^. us"' cannot be found."))
  | TyAll(fi,x,ki1,ty1) ->
      (match kindof (TyenvTyvar(x,TyDyn,ki1,true)::env) ty1 with
       | KindStar(_) as ki2 -> ki2
       | ki3 -> error fi (us"The type is of kind " ^. pprint_kind ki3 ^.
                          us", but kind * was expected"))
  | TyLam(fi,x,ki1,ty1) ->
      let ki2 =  kindof (TyenvTyvar(x,TyDyn,ki1,false)::env) ty1 in
      KindArrow(fi,ki1,ki2)
  | TyApp(fi,ty1,ty2) ->
      (match kindof env ty1, kindof env ty2 with
       | KindArrow(fi2,k11,k12),k11' ->
         if kindEqual k11 k11' then k12
         else error (ty_info ty2) (us"Incorrect type-level application. " ^.
           us"The type argument is of kind " ^. pprint_kind k11' ^.
           us", but kind " ^. pprint_kind k11 ^. us" was expected.")
       | k1,_ -> error (ty_info ty1) (us"Incorrect type-level application. " ^.
           us"Kind " ^. pprint_kind k1 ^.us" is not a kind of a type-level function"))
  | TyDyn -> KindStar(NoInfo)




(* Returns the type of term [t]
   The type environment [tyenv] is list with elements of type [tyenvVar] *)
let rec typeof tyenv t =
  match t with
  | TmVar(fi,x,n,pe) ->
      (match List.nth_opt tyenv n with
       | Some(TyenvTmvar(y,ty1)) ->
         let ty1shift = tyShift (n+1) 0 ty1 in
         tydebug "TmVar" ["variable",x] [] [("ty1",ty1);("ty1shift",ty1shift)];
         ty1shift
       | _ -> error fi (us"Variable '" ^. x ^. us"' cannot be found."))
  | TmLam(fi,x,ty1,t1) ->
    let ty2 = typeof (TyenvTmvar(x,ty1)::tyenv) t1 in
    let ty2shift = tyShift (-1) 0 ty2 in
      tydebug "TmLam" [] [] [("ty1",ty1);("ty2",ty2);("ty2shift",ty2shift)];
      TyArrow(fi,ty1,ty2shift)
  | TmClos(fi,s,ty,t1,env1,pe) -> failwith "Closure cannot happen"
  | TmApp(fi,TmLam(fi2,x,TyDyn,t1),t2) ->
      let ty2 = typeof tyenv t2 in
      typeof (TyenvTmvar(x,ty2)::tyenv) t1
  | TmApp(fi,t1,t2) -> (
    match normTy (typeof tyenv t1), normTy (typeof tyenv t2) with
    | TyArrow(fi2,ty11,ty12) as ty1,ty11' ->
        tydebug "TmApp" [] [] [("ty1",ty1);("ty11'",ty11')];
        if tyequal ty11 ty11' then ty12
        else error (tm_info t2)
          (us"Function application type mismatch. Applied an expression of type " ^.
           pprint_ty ty11' ^. us", but expected an expression of type " ^.
           pprint_ty ty11 ^. us".")
    | ty1,ty2 -> error (tm_info t1)
          (us"Type application mismatch. Cannot apply an expression of " ^.
           us"type " ^. pprint_ty ty2 ^. us" to an expression of type " ^.
           pprint_ty ty1 ^. us".")
  )
  | TmConst(fi,c) -> type_const c
  | TmPEval(fi) -> failwith "TODO5"
  | TmIfexp(fi,t1op,t2op) -> failwith "TODO6"
  | TmFix(fi) -> failwith "TODO7"
  | TmTyLam(fi,x,kind,t1) ->
      let ty2 = typeof (TyenvTyvar(x,TyDyn,kind,false)::tyenv) t1 in
      TyAll(fi,x,kind,ty2)
  | TmTyApp(fi,t1,ty2) ->
     (match typeof (tyenv) t1 with
      | TyAll(fi2,x,ki11,ty1) ->
          let ki12 = kindof tyenv ty2 in
          if kindEqual ki11 ki12 then
            let ty1subst = tySubstTop ty2 ty1 in
            tydebug "TmTyApp" [] [("t1",t1)]
                   [("ty1",ty1);("ty2",ty2);("ty1subst",ty1subst)];
            ty1subst
          else error (ty_info ty2) (us"The type argument is of kind " ^.
             pprint_kind ki12 ^. us", but a type of kind " ^. pprint_kind ki11 ^.
             us" was expected.")
      | ty -> error (tm_info t1)
             (us"Type application expects an universal type, but found " ^.
              pprint_ty ty ^. us"."))
  | TmChar(fi,x) -> failwith "TODO8"
  | TmExprSeq(fi,t1,t2) -> failwith "TODO9"
  | TmUC(fi,tree,ord,unique) -> failwith "TODO10"
  | TmUtest(fi,t1,t2,t3) ->
      let (ty1,ty2) = (normTy (typeof tyenv t1),normTy (typeof tyenv t2)) in
      if tyequal ty1 ty2
      then typeof tyenv t3
      else error fi  (us"The two test expressions have differnt types: " ^.
                        pprint_ty ty1 ^. us" and " ^.
                        pprint_ty ty2 ^. us".")
  | TmMatch(fi,t1,cases) -> failwith "TODO12"
  | TmNop -> TyGround(NoInfo,GVoid)

(* Returns true of the type contains at least one TyDyn *)
let rec containsTyDyn ty =
  match ty with
  | TyGround(fi,gt) -> false
  | TyArrow(fi,ty1,ty2) -> containsTyDyn ty1 || containsTyDyn ty2
  | TyVar(fi,x,n) -> false
  | TyAll(fi,x,ki1,ty1) -> containsTyDyn ty1
  | TyLam(fi,x,ki1,ty1) -> containsTyDyn ty1
  | TyApp(fi,ty1,ty2) -> containsTyDyn ty1 || containsTyDyn ty2
  | TyDyn -> true


(* Returns true of the type contains at least one TyVar *)
let containsFreeTyVar ty =
  let rec work c ty =
  match ty with
  | TyGround(fi,gt) -> false
  | TyArrow(fi,ty1,ty2) -> work c ty1 || work c ty2
  | TyVar(fi,x,n) -> (n >= c)
  | TyAll(fi,x,ki1,ty1) -> work (c+1) ty1
  | TyLam(fi,x,ki1,ty1) -> work (c+1) ty1
  | TyApp(fi,ty1,ty2) -> work c ty1 || work c ty2
  | TyDyn -> false
  in work 0 ty


(* Merge two types. Assumes that the input types are normalized.
   Returns None if they do not match.
   Returns Some(ty',env') if match, where ty' is the merged new
   type, and env' the environment filled in with new type variable bindings. *)
let tymerge ty1 ty2 env =
  let varUpdate env fi x n =
      (match List.nth_opt env n with
       | Some(TyenvTyvar(y,TyDyn,_,_)) -> (TyVar(fi,x,n),env)
       | Some(TyenvTyvar(y,ty1,ki1,_)) -> (ty1,env)
       | _ -> failwith "Should not happen")
  in
  let rec tyrec ty1 ty2 env =
    match ty1,ty2 with
    | TyGround(_,g1),TyGround(_,g2) ->
        if g1 = g2 then (ty1,env) else raise Not_found
    | (TyGround(_,_) as ty), TyDyn | TyDyn,(TyGround(_,_) as ty) -> (ty,env)
    | TyArrow(fi,ty11,ty12),TyArrow(_,ty21,ty22) ->
        let (ty1,env1) = tyrec ty11 ty21 env in
        let (ty2,env2) = tyrec ty12 ty22 env1 in
        (TyArrow(fi,ty1,ty2),env2)
    | TyArrow(fi,ty1,ty2),TyDyn | TyDyn,TyArrow(fi,ty1,ty2) ->
        let (ty1',env1) = tyrec ty1 TyDyn env in
        let (ty2',env2) = tyrec ty2 TyDyn env1 in
        (TyArrow(fi,ty1',ty2'),env2)
    | TyVar(fi,x,n1),TyVar(_,_,n2) ->
      if n1 <> n2 then raise Not_found else varUpdate env fi x n1
    | TyVar(fi,x,n),TyDyn | TyDyn,TyVar(fi,x,n) -> varUpdate env fi x n
    | TyVar(fi,x,n),ty2 | ty2,TyVar(fi,x,n) ->
        if containsFreeTyVar ty2 then raise Not_found else
        let rec updateEnv env n =
          (match env with
           | TyenvTyvar(y,ty1,ki1,false)::rest when n = 0 ->
               let (ty',_) = tyrec ty1 ty2 [] in (* Safe. ty1 has no free type vars *)
               TyenvTyvar(y,ty',ki1,false)::rest
           | TyenvTyvar(y,_,_,true)::rest when n = 0 -> raise Not_found
           | x::rest when n = 0 -> failwith "Should not happen"
           | x::rest -> x::(updateEnv rest (n-1))
           | [] -> failwith "Should not happen")
        in
        varUpdate (updateEnv env n) fi x n
    | TyAll(fi1,x,ki1,ty1),TyAll(fi2,_,ki2,ty2) ->
        if not (kindEqual ki1 ki2) then raise Not_found else
          (match tyrec ty1 ty2 (TyenvTyvar(x,TyDyn,ki1,true)::env) with
           | (ty3,remove::env1) -> (TyAll(fi1,x,ki1,ty3),env1)
           | _ -> failwith "Should not happen")
    | TyAll(fi1,x,ki1,ty1),TyDyn | TyDyn,TyAll(fi1,x,ki1,ty1) ->
        (match tyrec ty1 TyDyn (TyenvTyvar(x,TyDyn,ki1,true)::env) with
         | (ty1',remove::env1) -> (TyAll(fi1,x,ki1,ty1'),env1)
         | _ -> failwith "Should not happen")
    | TyLam(fi1,x1,kind1,ty1), TyLam(fi2,x2,kind2,ty2) -> failwith "TODO TyLam"
    | TyApp(fi1,ty11,ty12), TyApp(fi2,ty21,ty22)-> failwith "TODO TyApp"
    | TyDyn,TyDyn -> (TyDyn,env)
    | TyArrow(_,_,_), _ | _,TyArrow(_,_,_) -> raise Not_found
    | TyAll(_,_,_,_), _ | _,TyAll(_,_,_,_) -> raise Not_found
    | TyLam(fi,x,kind,ty1),_ | _,TyLam(fi,x,kind,ty1) -> failwith "TODO TyLam"
    | TyApp(fi,ty1,ty2),_ | _,TyApp(fi,ty1,ty2)-> failwith "TODO TyApp"
  in
  try
    let (ty',env1) = tyrec ty1 ty2 env in
    let (ty'',env2) = tyrec ty' TyDyn env1 in  (* Makes sure all variables are *)
    Some(ty'',env2)                            (* substituted *)
  with _ -> None




(* Type reconstruction using bidirectional type checking.
   Main idea: propagate both types and type environment (filled will
     bindings of type vars) in both directions, merging partially filled in
     types. The 'holes' in the types are marked using type TyDyn. If
     type reconstruction is complete, the TyDyn does not exist anywhere.
   Future: we can combine let-polymorphism, gradual typing, and this
     reconstruction of for type applications in system F using bidirectional
     type checking. Should in such case mark code as gradually typed, that
     allows TyDyn to be left, but still generates System F code.
*)
let rec typerecon tyenv tyinher t =
  match t with
  | TmVar(fi,x,n,pe) ->
    (match List.nth_opt tyenv n with
    | Some(TyenvTmvar(y,ty1)) ->
      let ty1shift = tyShift (n+1) 0 ty1 in
      (TmVar(fi,x,n,pe), ty1shift, tyenv)
    | _ -> errorVarNotFound fi x)
  | TmLam(fi,x,ty1,t1) -> failwith "TODO TmLam"
  (*
    let ty2 = typeof (TyenvTmvar(x,ty1)::tyenv) t1 in
    let ty2shift = tyShift (-1) 0 ty2 in
    tydebug "TmLam" [] [] [("ty1",ty1);("ty2",ty2);("ty2shift",ty2shift)];
    TyArrow(fi,ty1,ty2shift)
  *)
  | TmClos(fi,s,ty,t1,env1,pe) -> errorImpossible fi
  | TmApp(fi,t1,t2) ->
    let (t2',ty2',env2) = typerecon tyenv TyDyn t2 in
    let (t1',ty1',env3) = typerecon env2 (TyArrow(fi,ty2',tyinher)) t1 in
    if containsTyDyn ty1' then errorCannotInferType (tm_info t1) ty1'
    else failwith "temp"
      (*
      let rec dive t1' ty1' t2' ty2' env3 =
        (match ty1' with
        | TyArrow(fi3,ty11,ty12) ->
          let (t22,ty22,env4) =
            if containsTyDyn ty2' then typerecon env3 ty11 t2 else (t2',ty2',env3) in
          if containsTyDyn ty22 then errorCannotInferType (tm_info t2) ty22 else
            if not (tyequal ty11 ty22) then errorFuncAppMismatch (tm_info t2) ty11 ty22
            else (TmApp(fi,t1',t22),ty12,env4)
        | TyAll(fi,x,ki,ty4) ->
        | _ -> errorNotFunctionType (tm_info t1) ty1')
        in dive t1' ty1' t2' ty2' env3 *)
  | TmConst(fi,c) -> (TmConst(fi,c),type_const c, tyenv)
  | TmPEval(fi) -> failwith "TODO TmPEval (later)"
  | TmIfexp(fi,t1op,t2op) -> failwith "TODO TmIfexp (later)"
  | TmFix(fi) -> failwith "TODO TmFix (later)"
  | TmTyLam(fi,x,kind,t1) -> failwith "TODO TmTyLam"
  (*
    let ty2 = typeof (TyenvTyvar(x,TyDyn,kind)::tyenv) t1 in
    TyAll(fi,x,kind,ty2)
  *)
  | TmTyApp(fi,t1,ty2) -> failwith "TODO TmTyApp"
  (*
    (match typeof (tyenv) t1 with
    | TyAll(fi2,x,ki11,ty1) ->
    let ki12 = kindof tyenv ty2 in
    if kindEqual ki11 ki12 then
    let ty1subst = tySubstTop ty2 ty1 in
    tydebug "TmTyApp" [] [("t1",t1)]
    [("ty1",ty1);("ty2",ty2);("ty1subst",ty1subst)];
    ty1subst
    else error (ty_info ty2) (us"The type argument is of kind " ^.
    pprint_kind ki12 ^. us", but a type of kind " ^. pprint_kind ki11 ^.
    us" was expected.")
    | ty -> error (tm_info t1)
    (us"Type application expects an universal type, but found " ^.
    pprint_ty ty ^. us"."))
  *)
  | TmChar(fi,x) -> failwith "TODO TmChar (later)"
  | TmExprSeq(fi,t1,t2) -> failwith "TODO TmExprSeq (later)"
  | TmUC(fi,tree,ord,unique) -> failwith "TmUC (later)"
  | TmUtest(fi,t1,t2,t3) ->
    let (t1',ty1,env1) = typerecon tyenv TyDyn t1 in
    let (t2',ty2,env2) = typerecon tyenv TyDyn t2 in
    let (nty1,nty2) = (normTy ty1,normTy ty2) in
    if tyequal nty1 nty2 then
      let (t3',ty3,env3) = typerecon tyenv TyDyn t3 in
      (TmUtest(fi,t1',t2',t3'),ty3, tyenv)
    else error fi  (us"The two test expressions have differnt types: " ^.
                      pprint_ty nty1 ^. us" and " ^.
                      pprint_ty nty2 ^. us".")
  (*
    let (ty1,ty2) = (normTy (typeof tyenv t1),normTy (typeof tyenv t2)) in
    if tyequal ty1 ty2
    then typeof tyenv t3
    else error fi  (us"The two test expressions have differnt types: " ^.
    pprint_ty ty1 ^. us" and " ^.
    pprint_ty ty2 ^. us".")
  *)
  | TmMatch(fi,t1,cases) -> failwith "TODO TmMatch (later)"
  | TmNop -> (TmNop,TyGround(NoInfo,GVoid), tyenv)






(* Erase type abstractions and applications *)
let rec erase t =
  let eraseOp op = match op with | None -> None | Some(t) -> Some(erase t) in
  match t with
  | TmVar(fi,x,n,pe) -> t
  | TmLam(fi,x,ty1,t1) -> TmLam(fi,x,ty1,erase t1)
  | TmClos(fi,s,ty,t1,env1,pe) -> failwith "Closer should not exist during erase."
  | TmApp(fi,t1,t2) -> TmApp(fi, erase t1, erase t2)
  | TmConst(fi,c) -> t
  | TmPEval(fi) -> t
  | TmIfexp(fi,op1,t2op) -> TmIfexp(fi, op1, eraseOp t2op)
  | TmFix(fi) -> t
  | TmTyLam(fi,x,kind,t1) -> TmLam(fi,us"_",TyGround(NoInfo,GVoid),erase t1)
  | TmTyApp(fi,t1,ty1) -> TmApp(fi,erase t1,TmNop)
  | TmChar(fi,x) -> t
  | TmExprSeq(fi,t1,t2) -> TmExprSeq(fi, erase t1, erase t2)
  | TmUC(fi,tree,ord,unique) -> t
  | TmUtest(fi,t1,t2,t3) -> TmUtest(fi, erase t1, erase t2, erase t3)
  | TmMatch(fi,t1,cases) -> t (* TODO if needed *)
  | TmNop -> t


(* Main external function for type checking *)
let typecheck builtin t =
  (* Remove constant that are not supported by the type system *)
  let lst = List.filter
    (fun (x,_) ->
      match x with
      | "add" | "sub" | "div" | "mul" | "neg" |
        "dstr" | "dprint" | "print" | "argv" | "concat" -> false
      | _ -> true) builtin in
  (* Create type environment for builtins *)
  let tyenv = List.map (fun (x,c) -> TyenvTmvar(us x, type_const c)) lst in

  (* Type reconstruct *)
  let (t,ty, env) = typerecon tyenv TyDyn t in

(*
  (* Testing merge function *)
  let int = TyGround(NoInfo,GInt) in
  let bool = TyGround(NoInfo,GBool) in
  let dyn = TyDyn in
  let arr t1 t2 = TyArrow(NoInfo,t1,t2) in
  let all t1 = TyAll(NoInfo,us"",KindStar(NoInfo),t1) in
  let var x n  = TyVar(NoInfo,us x,n) in
  let env = [TyenvTyvar(us"x",TyDyn,KindStar(NoInfo),false)] in
  let ty1 = all (arr dyn int) in
  let ty2 = all (arr int (var "x" 1))  in

  printf "\n------\n";
  (match tymerge ty1 ty2 env with
  | None -> printf "None\n"
  | Some(ty',env') ->
    uprint_endline (pprint_ty ty');
    uprint_endline (pprint_tyenv env')
  );
  printf "------\n";
*)

  (* Type check *)
  let _ = typeof tyenv t in
  t
