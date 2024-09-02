include "mexpr/type-check.mc"
include "mexpr/pattern-analysis.mc"

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
                          TypeAbsAppResolver + ResolveType + RecordAst +
                          RecordTypeAst + MatchAst + RecordPat + 
                          MExprPatAnalysis + PatTypeCheck
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
  | TmExtExtend t ->
    let e = typeCheckExpr env t.e in 

    let ident = match tyTm e with TyExtRec {ident = ident} then ident
                else errorSingle [infoTm e] (join [
                  " * You are attempting to extend some other type!\n",
                  " * Or the type identifier of the extensible record can not be ",
                  "inferred\n",
                  " * Try adding a type annotation.\n",
                  " * The following type was inferred: '",
                  type2str (tyTm e),
                  "'."
                ]) in 

    match mapLookup ident env.extRecordType.tyDeps with Some tydeps in 
    match mapLookup ident env.extRecordType.defs with Some labelToType in 
    let allLabels = map fst (mapToSeq labelToType) in 
    let boundLabels = mapKeys t.bindings in  
    let unboundLabels = setSubtract (setOfKeys labelToType) (setOfKeys t.bindings) in 

    -- Ensure that the type of t.e is {extrec ident of oldMapping}
    let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
    let oldKind = Data {types = kindMap} in 
    let oldR = newnmetavar "r" oldKind env.currentLvl (NoInfo ()) in

    let ty = TyExtRec {info = NoInfo (),
                       ident = ident,
                       ty = oldR} in 

    unify env [infoTm e] ty (tyTm e) ;

    let oldKind = getKind env oldR in  

    -- Create a new "fresh" mapping.
    let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
    let newKind = Data {types = kindMap} in 

    -- Copy over the bounds belonging to this identifier
    let newKind = _update_bounds ident (_get_bounds ident oldKind) newKind in 

    -- Mark the extended fields as present
    let newKind = foldl 
      (lam k. lam l. _extend_upper_bound ident l k)
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
        setUnion acc (_labeldep_lookup env.extRecordType ident label))
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

    let resultTy = TyExtRec {ident = ident,
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
  | TmRecordUpdate t ->
    let rec = typeCheckExpr env t.rec in 

    match tyTm rec with TyExtRec extRec then
      match mapLookup extRec.ident env.extRecordType.defs with Some labelToType in 
      match mapLookup extRec.ident env.extRecordType.tyDeps with Some tydeps in 
      let label = sidToString t.key in 

      let actualTy = tyTm rec in 

      (match mapLookup label labelToType with Some _ then 
        () 
      else 
        errorSingle [t.info] (join [
          "The label '",
          label,
          "' is not a defined field of the type '",
          nameGetStr extRec.ident,
          "'!"])) ;

      
      let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
      let kindMap = mapUpdate extRec.ident (lam. Some {lower = setSingleton nameCmp (nameNoSym label), upper = None ()}) kindMap in 

      let kind = Data {types = kindMap} in 
      let r = newnmetavar "r" kind env.currentLvl (NoInfo ()) in 

      let expectedTy = TyExtRec {ident = extRec.ident, ty = r, info = NoInfo ()} in

      unify env [t.info] expectedTy actualTy ;

      match mapLookup label labelToType with Some (_, tyAbs) in 

      let ty = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = r}) in 
      let ty = resolveType t.info env false ty in
      
      let value = typeCheckExpr env t.value in 
      unify env [infoTm value] ty (tyTm value) ;
      -- printLn (type2str ty) ;

      TmRecordUpdate {t with rec = rec,
                             value = value,
                             ty = expectedTy}
    else 
      let value = typeCheckExpr env t.value in
      let fields = mapInsert t.key (tyTm value) (mapEmpty cmpSID) in
      unify env [infoTm rec] (newrecvar fields env.currentLvl (infoTm rec)) (tyTm rec);
      TmRecordUpdate {t with rec = rec, value = value, ty = tyTm rec}

  sem typeCheckExpr env =
  | TmMatch {pat = PatRecord p} & TmMatch t ->
    let target = typeCheckExpr env t.target in

    let res = match tyTm target with TyExtRec extRec then
      match mapLookup extRec.ident env.extRecordType.defs with Some labelToType in 
      match mapLookup extRec.ident env.extRecordType.tyDeps with Some tydeps in 

      let typeCheckBinding = lam patEnv. lam. lam pat. typeCheckPat env patEnv pat in 
      match mapMapAccum typeCheckBinding (mapEmpty nameCmp) p.bindings with (patEnv, bindings) in 

      let bindingPairs = mapToSeq bindings in 
      let tcPair = lam accBound. lam pair.
        match pair with (labelSid, pat) in 
        let ty = tyPat pat in 
        let tyAbs  = match mapLookup (sidToString labelSid) labelToType with Some (_, tyAbs) 
                     then tyAbs 
                     else errorSingle [p.info] (join [
                      "* The label '",
                      sidToString labelSid,
                      "' is not defined for the type '",
                      nameGetStr extRec.ident,
                      "'!"
                     ]) in 
        let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = extRec.ty}) in 
        let expectedTy = resolveType (NoInfo ()) env false expectedTy in 
        unify env [NoInfo ()] ty expectedTy ;

        setInsert (nameNoSym (sidToString labelSid)) accBound 
      in 
      let lowerBound = foldl tcPair (setEmpty nameCmp) bindingPairs in

      let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
      let kindMap = mapInsert extRec.ident {lower = lowerBound, upper = None ()} kindMap in 
      let kind = Data {types = kindMap} in 
      let r = newnmetavar "r" kind env.currentLvl (NoInfo ()) in 
      let ty = TyExtRec {info = NoInfo (), ident = extRec.ident, ty = r} in 
      (patEnv, PatRecord {p with bindings = bindings, ty = ty})
    else 
      match typeCheckPat env (mapEmpty nameCmp) t.pat with (patEnv, pat) in
      (patEnv, pat)
    in 

    match res with (patEnv, pat) in 
    unify env [infoTm target, infoPat pat] (tyPat pat) (tyTm target);

    let matchLvl = addi 1 env.matchLvl in
    match
      if env.disableConstructorTypes then ([], [])
      else
        let np = patToNormpat pat in
        (matchNormpat (t.target, np), matchNormpat (t.target, normpatComplement np))
    with
      (posMatches, negMatches)
    in

    let mkMatches =
      lam matches.
        joinMap (lam a.
          (joinMap (lam b.
            let m = mapUnionWith normpatIntersect a b in
            if mapAll (lam np. not (null np)) m then [m] else [])
             env.matches))
          matches
    in
    let mkMatchVars = lam matches.
      foldl
        (mapFoldWithKey (lam acc. lam n. lam. mapInsert n matchLvl acc))
        env.matchVars matches
    in

    let baseEnv = {env with varEnv = mapUnion env.varEnv patEnv,
                            matchLvl = matchLvl} in
    let thnEnv = if env.disableConstructorTypes then baseEnv
                 else {baseEnv with matches = mkMatches posMatches,
                                    matchVars = mkMatchVars posMatches} in
    let elsEnv = if env.disableConstructorTypes then baseEnv
                 else {baseEnv with matches = mkMatches negMatches,
                                    matchVars = mkMatchVars negMatches} in
    let thn = typeCheckExpr thnEnv t.thn in
    let els = typeCheckExpr elsEnv t.els in
    unify env [infoTm thn, infoTm els] (tyTm thn) (tyTm els);
    TmMatch {t with target = target
            , thn = thn
            , els = els
            , ty = tyTm thn
            , pat = pat}
end
