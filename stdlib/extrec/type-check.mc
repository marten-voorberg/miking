include "mexpr/type-check.mc"

include "unify.mc"
include "ast.mc"

lang GetPresenceKind = GetKind + PresenceKindAst + ExtRecordTypeAst
  -- sem getKind env = 
  -- | TyPre _ | TyAbsent _ -> Presence ()
end 

lang TypeAbsAppResolver = TypeAbsAppAst + TypeAbsAst + VarTypeAst
  sem _subst : Name -> Type -> Type -> Type
  sem _subst name replacement =
  | (TyVar t) & ty  ->
    if nameEq t.ident name then
      replacement
    else 
      ty
  | ty ->
    smap_Type_Type (_subst name replacement) ty

  sem resolveTyAbsApp =
  | TyAbsApp {lhs = TyAbs tyAbs, rhs = rhs} ->
    _subst tyAbs.ident rhs tyAbs.body
end

lang ExtRecordTypeCheck = TypeCheck + ExtRecordTypeAst + ExtRecordAst + 
                          PresenceKindAst + TypeAbsAppAst + GetKind + 
                          TypeAbsAppResolver + ResolveType
  sem _lookupTydeps : TCEnv -> Name -> Set Name
  sem _lookupTydeps env =
  | ident ->
    match mapLookup ident env.extRecordType.tyDeps with Some deps then deps
    else error "Tydeps not found!"

  sem _relevantExtensions : TCEnv -> Name -> Set Name
  sem _relevantExtensions env = 
  | ident ->
    let tydeps = _lookupTydeps env ident in 

    let f = lam extSet. lam tyIdent.
      match mapLookup tyIdent env.extRecordType.tyToExts with Some newExts in 
      setUnion extSet newExts
    in
    setFold f (setEmpty nameCmp) tydeps

  sem _get_bounds : Name -> Kind -> {lower : Set Name, upper : Option (Set Name)}
  sem _get_bounds name = 
  | Data {types = types} ->
    match mapLookup name types with Some bounds in bounds

  sem _update_bounds name bound =
  | Data k ->
    Data {k with types = mapInsert name bound k.types}

  sem _dump_datakind =
  | Data k ->
    let str = strJoin "\n" (map _dump_bounds (mapValues k.types)) in 
    printLn str

  sem _dump_bounds =
  | t ->
    let lowerStr = strJoin ", " (map nameGetStr (setToSeq t.lower)) in 
    let upperStr = match t.upper with Some s
                   then strJoin ", " (map nameGetStr (setToSeq s)) 
                   else "∅" in 
    join ["lower = ", lowerStr, "; upper = ", upperStr]

  sem _extend_upper_bound tyName fieldName =
  | Data k ->
    match mapLookup tyName k.types with Some {lower = lower, upper = upper} in 
    let newUpper = match upper with Some s 
                   then setInsert fieldName s 
                   else setSingleton nameCmp fieldName in 
    Data {k with types = mapInsert tyName {lower = lower, upper = Some newUpper} k.types}

  sem _extend_lower_bound tyName fieldName =
  | Data k ->
    match mapLookup tyName k.types with Some {lower = lower, upper = upper} in 
    let lower = setInsert fieldName lower in
    Data {k with types = mapInsert tyName {lower = lower, upper = upper} k.types}

  sem _clear_lower_bounds = 
  | Data k ->
    Data {k with 
      types = mapValues 
        (lam bounds. {bounds with lower = setEmpty nameCmp}) 
        k.types}

  sem _labeldep_lookup : ExtRecEnvType -> Name -> String -> Set Name
  sem _labeldep_lookup env n =
  | label ->
    match mapLookup n env.labelTyDeps with Some innerMap in 
    match mapLookup label innerMap with Some deps in 
    deps

  sem typeCheckExpr env =
  | TmRecField t -> 
    let newLvl = addi 1 env.currentLvl in 
    let tyIdent = tyunknown_ in
    let conEnv = mapInsert (nameNoSym t.label) (newLvl, tyIdent) env.conEnv in 
    let env = {env with conEnv = conEnv,
                        currentLvl = newLvl} in 

    let inexpr = typeCheckExpr env t.inexpr in
    TmRecField {t with inexpr = inexpr, ty = tyTm inexpr}
  | TmRecType t ->
    let newLvl = addi 1 env.currentLvl in 
    let newTyConEnv = mapInsert t.ident (newLvl, t.params, tyvariant_ []) env.tyConEnv in
    let env = {env with tyConEnv = newTyConEnv} in 
    let inexpr =
      typeCheckExpr {env with currentLvl = newLvl,
                              tyConEnv = newTyConEnv,
                              reptypes = env.reptypes} t.inexpr in
    unify env [t.info, infoTm inexpr] (newpolyvar env.currentLvl t.info) (tyTm inexpr);
    TmRecType {t with inexpr = typeCheckExpr env t.inexpr, 
                      ty =  tyTm inexpr}
  | TmExtRecord t ->
    match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    match mapLookup t.ident env.extRecordType.tyDeps with Some tydeps in 
    let boundLabels = setOfKeys t.bindings in 
    let boundLabelNameSet = setMap nameCmp nameNoSym boundLabels in 
    let allLabels = setOfKeys labelToType in 

    let universe = mapMap 
      (lam label2type. setMap nameCmp nameNoSym (setOfKeys labelToType))
      env.extRecordType.defs in 

    let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
    -- let kindMap = mapUpdate t.ident (lam. Some {lower = setMap nameCmp nameNoSym boundLabels, upper = None ()}) kindMap in 
    let kindMap = mapUpdate t.ident (lam. Some {upper = Some boundLabelNameSet, lower = boundLabelNameSet}) kindMap in 


    let kind = Data {types = kindMap} in 
    let r = newnmetavar "r" kind env.currentLvl (NoInfo ()) in 

    let typeCheckBinding = lam label. lam expr.
      let expr = typeCheckExpr env expr in 

      let tyAbs = match mapLookup label labelToType with Some ty then ty.1
                  else error "Illegal label!" in 
      let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = r}) in
      let expectedTy = resolveType t.info env false expectedTy in 

      unify env [t.info] (tyTm expr) expectedTy ;

      expr
    in 

    let bindings = mapMapWithKey typeCheckBinding t.bindings in 

    let ty = TyExtRec {info = NoInfo () ,
                       ident = t.ident,
                       ty = r} in 

    TmExtRecord {t with ty = ty,
                        bindings = bindings}
  | TmExtProject t -> 
    match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    match mapLookup t.ident env.extRecordType.tyDeps with Some tydeps in 


    let lhs = typeCheckExpr env t.e in 
    let actualTy = tyTm lhs in 

    (match mapLookup t.label labelToType with Some _ then 
       () 
     else 
       errorSingle [t.info] (join [
        "The label '",
        t.label,
        "' is not a defined field of the type '",
        nameGetStr t.ident,
        "'!"])) ;

    
    let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
    let kindMap = mapUpdate t.ident (lam. Some {lower = setSingleton nameCmp (nameNoSym t.label), upper = None ()}) kindMap in 
    -- let kindMap = mapUpdate t.ident (lam. Some {lower = setEmpty nameCmp, upper = Some (setSingleton nameCmp (nameNoSym t.label))}) kindMap in 

    let kind = Data {types = kindMap} in 
    let r = newnmetavar "r" kind env.currentLvl (NoInfo ()) in 

    let expectedTy = TyExtRec {ident = t.ident, ty = r, info = NoInfo ()} in


    unify env [t.info] expectedTy actualTy ;

    match mapLookup t.label labelToType with Some (_, tyAbs) in 

    let ty = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = r}) in 
    let ty = resolveType t.info env false ty in
    
    printLn (type2str ty) ;

    TmExtProject {t with ty = ty, e = lhs}
  | TmExtUpdate t -> 
    match mapLookup t.ident env.extRecordType.tyDeps with Some tydeps in 
    let boundLabels = setOfKeys t.bindings in  

    match mapLookup t.ident env.extRecordType.defs with Some labelToType in 

    let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
    let kindMap = mapUpdate t.ident (lam. Some {lower = setMap nameCmp nameNoSym boundLabels, upper = None ()}) kindMap in 

    let kind = Data {types = kindMap} in 
    let r = newnmetavar "r" kind env.currentLvl (NoInfo ()) in 

    let expectedTy = TyExtRec {ident = t.ident,
                               info = NoInfo (),
                               ty = r} in 

    let e = typeCheckExpr env t.e in 
    let actualTy = tyTm e in 

    unify env [infoTm e] expectedTy actualTy ;

    -- Ensure that the updated values have correct types
    let typeCheckBinding = lam label. lam expr. 
      match mapLookup label labelToType with Some (_, tyAbs) in 
      let expr = typeCheckExpr env expr in 
      let actualTy = tyTm expr in 

      let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = r}) in 
      let expectedTy = resolveType t.info env false expectedTy in 

      unify env [infoTm expr] expectedTy actualTy ; 

      expr
    in 
    let bindings = mapMapWithKey typeCheckBinding t.bindings in 

    -- printLn (type2str actualTy) ;

    TmExtUpdate {t with ty = actualTy, 
                        e = e,
                        bindings = bindings}
  | TmExtExtend t ->
    match mapLookup t.ident env.extRecordType.tyDeps with Some tydeps in 
    match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    let allLabels = map fst (mapToSeq labelToType) in 
    let boundLabels = mapKeys t.bindings in  
    let unboundLabels = setSubtract (setOfKeys labelToType) (setOfKeys t.bindings) in 

    -- Ensure that the type of t.e is {extrec t.ident of oldMapping}
    let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
    let oldKind = Data {types = kindMap} in 
    let oldR = newnmetavar "r" oldKind env.currentLvl (NoInfo ()) in

    let ty = TyExtRec {info = NoInfo (),
                       ident = t.ident,
                       ty = oldR} in 

    let e = typeCheckExpr env t.e in 
    unify env [infoTm e] ty (tyTm e) ;
    
    -- match tyTm e with TyExtRec {ty = foundTy} in 

    let oldKind = getKind env oldR in  

    -- Create a new "fresh" mapping.
    let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
    let newKind = Data {types = kindMap} in 

    -- Copy over the bounds belonging to this identifier
    let newKind = _update_bounds t.ident (_get_bounds t.ident oldKind) newKind in 

    -- Mark the extended fields as present
    let newKind = foldl 
      (lam k. lam l. _extend_upper_bound t.ident l k)
      newKind
      (map nameNoSym boundLabels) in 

    let newR = newnmetavar "r" newKind env.currentLvl (NoInfo ()) in

    -- Type check the binding expressions with newMapping
    let typeCheckBinding = lam label. lam expr. 
      match mapLookup label labelToType with Some (_, tyAbs) in 
      let expr = typeCheckExpr env expr in 
      let actualTy = tyTm expr in 

      let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = newR}) in 
      let expectedTy = resolveType t.info env false expectedTy in 

      unify env [infoTm expr] expectedTy actualTy ;

      expr
    in 
    let bindings = mapMapWithKey typeCheckBinding t.bindings in 

    let oldKind = getKind env oldR in 
    let newKind = getKind env newR in 

    let unchangedDeps = setFold
      (lam acc. lam label. 
        setUnion acc (_labeldep_lookup env.extRecordType t.ident label))
      (setEmpty nameCmp)
      unboundLabels in 
    
    let ensureCompatibleBounds = lam tyIdent. lam b1. lam b2.
      match b1.upper with None _ then
        () 
      else if (optionEq setEq) b1.upper b2.upper then 
        ()
      else
        errorSingle [infoTm e] (join [
          " * Encountered incompatible upper bounds during type checking.\n",
          " * Specifically, you are attempting to extend the type '",
          nameGetStr tyIdent,
          "',\n",
          " * but are not updating/extending all fields of this type."
        ])
    in 

    match (oldKind, newKind) with (Data {types = oldTypes}, 
                                   Data {types = newTypes}) in 

    let work = lam ty.
      match mapLookup ty oldTypes with Some b1 in 
      match mapLookup ty newTypes with Some b2 in 
      ensureCompatibleBounds ty b1 b2
    in 

    iter work (setToSeq unchangedDeps);

    let resultTy = TyExtRec {ident = t.ident,
                             info = NoInfo (),
                             ty = newR} in 

    -- printLn "===";
    -- print "\t";
    -- printLn (type2str resultTy);
    -- _dump_datakind (getKind env newR);
    -- printLn "===";

    TmExtExtend {t with e = e, 
                        bindings = bindings,
                        ty = resultTy}
end