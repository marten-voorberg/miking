include "mexpr/unify.mc"

include "ast.mc"

lang PresenceKindAstUnify = Unify + PresenceKindAst
  sem unifyKinds u env = 
  | (Presence _, Presence _) -> u.empty

  sem addKinds u env = 
  | (Presence _, Presence _) -> (u.empty, Presence ())
end

lang ExtRowUnify = Unify + ExtRecordTypeAst 
  sem unifyBase u env = 
  | (TyPre _, TyPre _) | (TyAbsent _, TyAbsent _) -> 
    u.empty
  | (ty1, ty2) & ((TyPre _, TyAbsent _) | (TyAbsent _, TyPre _)) -> 
    u.err (Types (ty1, ty2))
  | (TyExtensionRow t1 & ty1, TyExtensionRow t2 & ty2) ->
    let labels = mapKeys t1.row in 

    let pairs = map (lam l. (
      match mapLookup l t1.row with Some p in p, 
      match mapLookup l t2.row with Some p in p)
    ) labels in 

    let up = lam p. unifyTypes u env p in 
    map up pairs ;
    u.empty
  | (TyExtRec t1, TyExtRec t2) & (ty1, ty2) ->
    if nameEq t1.ident t2.ident then 
      unifyTypes u env (t1.ty, t2.ty) ;
      u.empty
    else
      u.err (Types (ty1, ty2))
end