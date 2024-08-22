include "mexpr/type-check.mc"

include "unify.mc"
include "ast.mc"

lang GetPresenceKind = GetKind + PresenceKindAst + ExtRecordTypeAst
  sem getKind env = 
  | TyPre _ | TyAbsent _ -> Presence ()
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

  sem _polymorhpicRow : TCEnv -> Name -> Type
  sem _polymorhpicRow env =
  | ident -> 
    let relevantExtensions = _relevantExtensions env ident in 
    let extPresencePairs = map 
      (lam e. (e, newnmetavar "theta" (Presence ()) env.currentLvl (NoInfo ())))
      (setToSeq relevantExtensions) in 
    let row = mapFromSeq nameCmp extPresencePairs in 
    TyExtensionRow {row = row}

  -- sem _updateRow : Name -> Type -> Type -> Type
  sem _updateRow ext pre =
  | TyExtensionRow r ->
    TyExtensionRow {r with row = mapInsert ext pre r.row}

  sem _getPre ext = 
  | TyExtensionRow r -> 
    match mapLookup ext r.row with Some pre in 
    pre

  sem typeCheckExpr env =
  | TmRecField t -> 
    TmRecField {t with inexpr = typeCheckExpr env t.inexpr}
  | TmRecType t ->
    TmRecType {t with inexpr = typeCheckExpr env t.inexpr}
  | TmExtRecord t ->
    match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    match mapLookup t.ident env.extRecordType.tyDeps with Some tydeps in 
    let boundLabels = setOfKeys t.bindings in 
    let allLabels = setOfKeys labelToType in 

    let f = lam extSet. lam tyIdent.
      match mapLookup tyIdent env.extRecordType.tyToExts with Some newExts in 
      setUnion extSet newExts
    in
    let relevantExtensions = setFold f (setEmpty nameCmp) tydeps in 
    iter (lam n. printLn (nameGetStr n)) (setToSeq relevantExtensions) ;

    let ext2presence = lam ext : Name. 
      let labels = mapLookupOrElse (lam. setEmpty cmpString) (t.ident, ext) env.extRecordType.tyExtToLabel in 
      let intersection = setIntersect boundLabels labels in

      -- The set of labels for this type/extension being empty, means
      -- that the presence var is unaffected by the tlabels at the top level
      -- thus, we can safely inroduce a metavar.
      if setIsEmpty labels then 
        newnmetavar "theta" (Presence ()) env.currentLvl t.info
      else if setIsEmpty intersection then
        TyAbsent ()
      else if setEq labels intersection then
        TyPre () 
      else 
        error (concat "Some labels are missing for: " (nameGetStr ext))
    in 

    let extPresencePair = map (lam e. (e, ext2presence e)) (setToSeq relevantExtensions) in 
    let row = TyExtensionRow {row = mapFromSeq nameCmp extPresencePair} in 

    let typeCheckBinding = lam label. lam expr.
      let expr = typeCheckExpr env expr in 

      let tyAbs = match mapLookup label labelToType with Some ty then ty.1
                  else error "Illegal label!" in 
      let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = row}) in
      let expectedTy = resolveType t.info env false expectedTy in 

      unify env [t.info] (tyTm expr) expectedTy ;

      expr
    in 

    let bindings = mapMapWithKey typeCheckBinding t.bindings in 

    let ty = TyExtRec {info = NoInfo () ,
                       ident = t.ident,
                       ty = row} in 

    TmExtRecord {t with ty = ty,
                        bindings = bindings}
  | TmExtProject t -> 
    match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    match mapLookup (t.ident, t.label) env.extRecordType.tyLabelToExt with Some ext in 
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

    let f = lam extSet. lam tyIdent.
      match mapLookup tyIdent env.extRecordType.tyToExts with Some newExts in 
      setUnion extSet newExts
    in
    let relevantExtensions = setFold f (setEmpty nameCmp) tydeps in 

    let extPresencePair = map (lam e. (e, newnmetavar "theta" (Presence ()) env.currentLvl t.info)) (setToSeq relevantExtensions) in 
    let rowMap = mapFromSeq nameCmp extPresencePair in 
    let rowMap = mapInsert ext (TyPre ()) rowMap in 
    let row = TyExtensionRow {row = rowMap} in 
    let expectedTy = TyExtRec {ident = t.ident, info = NoInfo (), ty = row} in 

    unify env [t.info] expectedTy actualTy ;

    match mapLookup t.label labelToType with Some (_, tyAbs) in 

    let ty = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = row}) in 
    let ty = resolveType t.info env false ty in

    TmExtProject {t with ty = ty, e = lhs}
  | TmExtUpdate t -> never
    -- let boundLabels = mapKeys t.bindings in  

    -- match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    -- let allLabels = _labelseq env.extRecordType t.ident in 

    -- let mapping = completePolyMapping env t.ident in
    -- let mapping = foldl 
    --   (lam mapping. lam label. _update_row_mapping t.ident label (TyPre ()) mapping)
    --   mapping
    --   boundLabels in 

    -- let expectedTy = TyExtRec {info = NoInfo (), 
    --                            ident = t.ident,
    --                            ty = mapping} in 

    -- let e = typeCheckExpr env t.e in 
    -- let actualTy = tyTm e in 

    -- unify env [t.info] expectedTy actualTy ;

    -- -- Ensure that the updated values have correct types
    -- let typeCheckBinding = lam label. lam expr. 
    --   match mapLookup label labelToType with Some (_, tyAbs) in 
    --   let expr = typeCheckExpr env expr in 
    --   let actualTy = tyTm expr in 

    --   let restrictedMapping = 
    --     _restrict_mapping (_labeldep_lookup env.extRecordType t.ident label) mapping in 
    --   let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = restrictedMapping}) in 
    --   let expectedTy = resolveType t.info env false expectedTy in 

    --   unify env [infoTm expr] expectedTy actualTy ; 

    --   expr
    -- in 
    -- let bindings = mapMapWithKey typeCheckBinding t.bindings in 

    -- TmExtUpdate {t with ty = actualTy, 
    --                     e = e,
    --                     bindings = bindings}
  | TmExtExtend t ->
    match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    let allLabels = map fst (mapToSeq labelToType) in 
    let boundLabels = setOfKeys t.bindings in  
    let relevantExtensions : Set Name = setOfKeys (_relevantExtensions env t.ident) in 

    -- Ensure that the type of t.e is {extrec t.ident of M}
    let oldRow = _polymorhpicRow env t.ident in
    let ty = TyExtRec {ident = t.ident,
                       info = NoInfo (),
                       ty = oldRow} in 

    let e = typeCheckExpr env t.e in 
    unify env [infoTm e] ty (tyTm e) ;

    let newRow = _polymorhpicRow env t.ident in 

    let ext2presence = lam ext : Name. 
      let labels = mapLookupOrElse (lam. setEmpty cmpString) (t.ident, ext) env.extRecordType.tyExtToLabel in 
      let intersection = setIntersect boundLabels labels in

      -- The set of labels for this type/extension being empty, means
      -- that the presence var is unaffected by the tlabels at the top level
      -- thus, we can safely inroduce a metavar.
      if setIsEmpty labels then 
        let newTy = newnmetavar "theta" (Presence ()) env.currentLvl t.info in 
        let oldTy = _getPre ext oldRow in 
        unify env [infoTm e] newTy oldTy ;
        newTy
      else if setIsEmpty intersection then
        let newTy = newnmetavar "theta" (Presence ()) env.currentLvl t.info in 
        let oldTy = _getPre ext oldRow in 
        unify env [infoTm e] newTy oldTy ;
        newTy
      else if setEq labels intersection then
        TyPre () 
      else 
        -- TODO: allow this in some cases
        error (concat "Some labels are missing for: " (nameGetStr ext))
    in 
    let newRow = setFold 
      (lam r. lam e : Name. _updateRow e (ext2presence e) r) 
      newRow
      relevantExtensions in 

    -- Type check the binding expressions with newMapping
    let typeCheckBinding = lam label. lam expr. 
      match mapLookup label labelToType with Some (_, tyAbs) in 
      let expr = typeCheckExpr env expr in 
      let actualTy = tyTm expr in 

      let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = newRow}) in 
      let expectedTy = resolveType t.info env false expectedTy in 

      unify env [infoTm expr] expectedTy actualTy ;

      expr
    in 
    let bindings = mapMapWithKey typeCheckBinding t.bindings in 

    -- TODO: re-add sanity check!
    -- let unchangedDeps = setFold
    --   (lam acc. lam label. 
    --     setUnion acc (_labeldep_lookup env.extRecordType t.ident label))
    --   (setEmpty nameCmp)
    --   unboundLabels in 
    
    -- -- Unify to ensure that the tydeps that are unchanged by this extension,
    -- -- are unchanged by this extension. 
    -- let unifyRow = lam name.
    --   let oldRow = _get_row name oldMapping in
    --   let newRow = _get_row name newMapping in
    --   unify env [infoTm t.e] oldRow newRow
    -- in 
    -- iter unifyRow (setToSeq unchangedDeps);
    -- -- unifyRow t.ident;


    let resultTy = TyExtRec {ident = t.ident,
                             info = NoInfo (),
                             ty = newRow} in 

    TmExtExtend {t with e = e, 
                        bindings = bindings,
                        ty = resultTy}
end