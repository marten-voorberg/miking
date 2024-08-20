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
  sem typeCheckExpr env =
  | TmRecField t -> 
    TmRecField {t with inexpr = typeCheckExpr env t.inexpr}
  | TmRecType t ->
    TmRecType {t with inexpr = typeCheckExpr env t.inexpr}
  | TmExtRecord t ->
    never
    -- match mapLookup t.ident env.extRecordType.defs with Some labelToType in 

    -- let allLabels = map (lam p. p.0) (mapToSeq labelToType) in 
    -- let labelPresence = lam l. 
    --   match mapLookup l t.bindings with Some _ 
    --   then (l, TyPre ())
    --   else (l, TyAbsent ())
    -- in 

    -- let presencePairs = map labelPresence allLabels in 
    -- let row = ExtRecordRow {ident = t.ident, row = mapFromSeq cmpString presencePairs} in 

    -- match completePolyMapping env t.ident with TyMapping {mapping = m} in
    -- let mapping = TyMapping {mapping = mapInsert t.ident row m} in 

    -- let typeCheckBinding = lam label. lam expr.
    --   let expr = typeCheckExpr env expr in 

    --   let tyAbs = match mapLookup label labelToType with Some ty then ty.1
    --               else error "Illegal label!" in 
    --   let restrictedMapping = 
    --     _restrict_mapping (_labeldep_lookup env.extRecordType t.ident label) mapping in 
    --   let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = restrictedMapping}) in
    --   let expectedTy = resolveType t.info env false expectedTy in 

    --   unify env [t.info] (tyTm expr) expectedTy ;

    --   expr
    -- in 

    -- let bindings = mapMapWithKey typeCheckBinding t.bindings in 

    -- let ty = TyExtRec {info = NoInfo () ,
    --                    ident = t.ident,
    --                    ty = mapping} in 

    -- TmExtRecord {t with ty = ty,
    --                     bindings = bindings}
  | TmExtProject t -> never
    -- match mapLookup t.ident env.extRecordType.defs with Some labelToType in 

    -- let lhs = typeCheckExpr env t.e in 
    -- let actualTy = tyTm lhs in 

    -- -- todo: check that the label being projected actually exists
    -- (match mapLookup t.label labelToType with Some _ then 
    --    () 
    --  else 
    --    errorSingle [t.info] (join [
    --     "The label '",
    --     t.label,
    --     "' is not a defined field of the type '",
    --     nameGetStr t.ident,
    --     "'!"])) ;

    -- let mapping = completePolyMapping env t.ident in 
    -- let row = _update_row t.label (TyPre ()) (_get_row t.ident mapping) in 
    -- let mapping = _update_mapping t.ident row mapping in 
    -- let expectedTy = TyExtRec {info = NoInfo (), 
    --                            ident = t.ident,
    --                            ty = mapping} in 

    -- unify env [t.info] expectedTy actualTy ;

    -- match mapLookup t.label labelToType with Some (_, tyAbs) in 

    -- -- Restrict the mapping to only contain values for the keys which are
    -- -- both in the keyset of mapping and tydeps (label)
    -- let restrictedMapping = 
    --   _restrict_mapping (_labeldep_lookup env.extRecordType t.ident t.label) mapping in 
    -- let ty = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = restrictedMapping}) in 
    -- let ty = resolveType t.info env false ty in

    -- TmExtProject {t with ty = ty, e = lhs}
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
  | TmExtExtend t -> never

    -- match mapLookup t.ident env.extRecordType.defs with Some labelToType in 
    -- let allLabels = map fst (mapToSeq labelToType) in 
    -- let boundLabels = mapKeys t.bindings in  
    -- let unboundLabels = setSubtract (setOfKeys labelToType) (setOfKeys t.bindings) in 

    -- -- Ensure that the type of t.e is {extrec t.ident of oldMapping}
    -- let oldMapping = completePolyMapping env t.ident in 
    -- let ty = TyExtRec {info = NoInfo (),
    --                    ident = t.ident,
    --                    ty = oldMapping} in 

    -- let e = typeCheckExpr env t.e in 
    -- unify env [infoTm e] ty (tyTm e) ;
    
    -- -- Create a new "fresh" mapping.
    -- let newMapping = completePolyMapping env t.ident in 

    -- -- Copy over the row belonging to this identifier
    -- let newMapping = _update_mapping t.ident (_get_row t.ident oldMapping) newMapping in  

    -- -- Mark the extended fields as present
    -- let newMapping = foldl 
    --   (lam m. lam l. _update_row_mapping t.ident l (TyPre ()) m)
    --   newMapping
    --   boundLabels in 

    -- -- Type check the binding expressions with newMapping
    -- let typeCheckBinding = lam label. lam expr. 
    --   match mapLookup label labelToType with Some (_, tyAbs) in 
    --   let expr = typeCheckExpr env expr in 
    --   let actualTy = tyTm expr in 

    --   let restrictedMapping = 
    --     _restrict_mapping (_labeldep_lookup env.extRecordType t.ident label) newMapping in 
    --   let expectedTy = resolveTyAbsApp (TyAbsApp {lhs = tyAbs, rhs = restrictedMapping}) in 
    --   let expectedTy = resolveType t.info env false expectedTy in 

    --   unify env [infoTm expr] expectedTy actualTy ;

    --   expr
    -- in 
    -- let bindings = mapMapWithKey typeCheckBinding t.bindings in 

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


    -- let resultTy = TyExtRec {ident = t.ident,
    --                          info = NoInfo (),
    --                          ty = newMapping} in 

    -- -- printLn "===";
    -- -- print "\t";
    -- -- printLn (type2str resultTy);
    -- -- printLn "===";

    -- TmExtExtend {t with e = e, 
    --                     bindings = bindings,
    --                     ty = resultTy}
end