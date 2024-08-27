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
                          PresenceKindAst + TypeAbsAppAst +
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

  -- sem _polymorhpicRow : TCEnv -> Name -> Type
  -- sem _polymorhpicRow env =
  -- | ident -> 
  --   let relevantExtensions = _relevantExtensions env ident in 
  --   let extPresencePairs = map 
  --     (lam e. (e, newnmetavar "theta" (Presence ()) env.currentLvl (NoInfo ())))
  --     (setToSeq relevantExtensions) in 
  --   let row = mapFromSeq nameCmp extPresencePairs in 
  --   TyExtensionRow {row = row}

  -- -- sem _updateRow : Name -> Type -> Type -> Type
  -- sem _updateRow ext pre =
  -- | TyExtensionRow r ->
  --   TyExtensionRow {r with row = mapInsert ext pre r.row}

  -- sem _getPre ext = 
  -- | TyExtensionRow r -> 
  --   match mapLookup ext r.row with Some pre in 
  --   pre

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
    let allLabels = setOfKeys labelToType in 

    let universe = mapMap 
      (lam label2type. setMap nameCmp nameNoSym (setOfKeys labelToType))
      env.extRecordType.defs in 

    let kindMap = mapMap (lam. {lower = setEmpty nameCmp, upper = None ()}) tydeps in 
    -- let kindMap = mapUpdate t.ident (lam. Some {lower = setMap nameCmp nameNoSym boundLabels, upper = None ()}) kindMap in 
    let kindMap = mapUpdate t.ident (lam. Some {upper = Some (setMap nameCmp nameNoSym boundLabels), lower = setEmpty nameCmp}) kindMap in 


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

    TmExtUpdate {t with ty = actualTy, 
                        e = e,
                        bindings = bindings}
  | TmExtExtend t ->
    never
    -- match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    -- let allLabels = map fst (mapToSeq labelToType) in 
    -- let boundLabels = setOfKeys t.bindings in  
    -- let relevantExtensions : Set Name = setOfKeys (_relevantExtensions env t.ident) in 

    -- -- Ensure that the type of t.e is {extrec t.ident of M}
    -- let oldRow = _polymorhpicRow env t.ident in
    -- let ty = TyExtRec {ident = t.ident,
    --                    info = NoInfo (),
    --                    ty = oldRow} in 

    -- let e = typeCheckExpr env t.e in 
    -- unify env [infoTm e] ty (tyTm e) ;

    -- let newRow = _polymorhpicRow env t.ident in 

    -- let ext2presence = lam ext : Name. 
    --   let labels = mapLookupOrElse (lam. setEmpty cmpString) (t.ident, ext) env.extRecordType.tyExtToLabel in 
    --   let intersection = setIntersect boundLabels labels in

    --   -- The set of labels for this type/extension being empty, means
    --   -- that the presence var is unaffected by the tlabels at the top level
    --   -- thus, we can safely inroduce a metavar.
    --   if setIsEmpty labels then 
    --     let newTy = newnmetavar "theta" (Presence ()) env.currentLvl t.info in 
    --     let oldTy = _getPre ext oldRow in 
    --     unify env [infoTm e] newTy oldTy ;
    --     newTy
    --   else if setIsEmpty intersection then
    --     let newTy = newnmetavar "theta" (Presence ()) env.currentLvl t.info in 
    --     let oldTy = _getPre ext oldRow in 
    --     unify env [infoTm e] newTy oldTy ;
    --     newTy
    --   else if setEq labels intersection then
    --     TyPre () 
    --   else 
    --     -- TODO: allow this in some cases
    --     error (concat "Some labels are missing for: " (nameGetStr ext))
    -- in 
    -- let newRow = setFold 
    --   (lam r. lam e : Name. _updateRow e (ext2presence e) r) 
    --   newRow
    --   relevantExtensions in 

    -- -- Type check the binding expressions with newMapping
    -- let typeCheckBinding = lam label. lam expr. 
    --   match mapLookup label labelToType with Some (_, tyAbs) in 
    --   let expr = typeCheckExpr env expr in 
    --   let actualTy = tyTm expr in 

    --   let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = newRow}) in 
    --   let expectedTy = resolveType t.info env false expectedTy in 

    --   unify env [infoTm expr] expectedTy actualTy ;

    --   expr
    -- in 
    -- let bindings = mapMapWithKey typeCheckBinding t.bindings in 

    -- -- TODO: re-add sanity check!
    -- -- let unchangedDeps = setFold
    -- --   (lam acc. lam label. 
    -- --     setUnion acc (_labeldep_lookup env.extRecordType t.ident label))
    -- --   (setEmpty nameCmp)
    -- --   unboundLabels in 
    
    -- -- -- Unify to ensure that the tydeps that are unchanged by this extension,
    -- -- -- are unchanged by this extension. 
    -- -- let unifyRow = lam name.
    -- --   let oldRow = _get_row name oldMapping in
    -- --   let newRow = _get_row name newMapping in
    -- --   unify env [infoTm t.e] oldRow newRow
    -- -- in 
    -- -- iter unifyRow (setToSeq unchangedDeps);
    -- -- -- unifyRow t.ident;


    -- let resultTy = TyExtRec {ident = t.ident,
    --                          info = NoInfo (),
    --                          ty = newRow} in 

    -- TmExtExtend {t with e = e, 
    --                     bindings = bindings,
    --                     ty = resultTy}
end