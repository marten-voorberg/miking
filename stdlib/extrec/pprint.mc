include "mexpr/pprint.mc"
include "mexpr/ast.mc"

include "ast.mc"
include "ast-builder.mc"

lang ExtRecTermPrettyPrint = TypePrettyPrint + PrettyPrint + ExtRecordAst 
  sem isAtomic =
  | TmRecField _ | TmRecType _ -> false
  | TmExtRecord _ | TmExtProject _ -> true
  | TmExtExtend _ | TmExtExtend _ -> false


  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmRecType t ->
    match pprintTypeName env t.ident with (env, name) in
    match pprintCode indent env t.inexpr with (env, inexpr) in
    match mapAccumL pprintEnvGetStr env t.params with (env, paramsStr) in
    (env, join [
      "rectype ",
      name,
      " ",
      strJoin " " paramsStr,
      " in", pprintNewline indent,
      inexpr])
  | TmRecField t -> 
    let ty =  typeToString env t.tyIdent in 
    match pprintCode indent env t.inexpr with (env, inexpr) in
    match pprintTypeName env t.extIdent with (env, ext) in
    (env, join [
      "recfield ",
      t.label, 
      " of ",
      ext,
      " : ",
      ty,
      " in ",
      pprintNewline indent, 
      inexpr
    ])
  | TmExtRecord {bindings = bindings, ident = ident} ->
    let innerIndent = pprintIncr (pprintIncr indent) in
      match
        mapMapAccum
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) in
             (env,
              join [k, " = ", str]))
           env bindings
      with (env, bindMap) in
      let binds = mapValues bindMap in
      let merged =
        strJoin ", " binds
      in
      (env,join ["{", nameGetStr ident, " of ", merged, "}"])
  | TmExtUpdate {bindings = bindings, ident = ident, e = e} ->
    match pprintCode indent env e with (env, eStr) in 
    let innerIndent = pprintIncr (pprintIncr indent) in
      match
        mapMapAccum
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) in
             (env,
              join [k, " = ", str]))
           env bindings
      with (env, bindMap) in
      let binds = mapValues bindMap in
      let merged =
        strJoin ", " binds
      in
      (env, join [
        "{recupdate ",
        eStr,
        " of ",
        nameGetStr ident,
        " with ",
        merged,
        "}"
      ])
  | TmExtExtend {bindings = bindings, ident = ident, e = e} ->
    match pprintCode indent env e with (env, eStr) in 
    let innerIndent = pprintIncr (pprintIncr indent) in
      match
        mapMapAccum
          (lam env. lam k. lam v.
             match pprintCode innerIndent env v with (env, str) in
             (env,
              join [k, " = ", str]))
           env bindings
      with (env, bindMap) in
      let binds = mapValues bindMap in
      let merged =
        strJoin ", " binds
      in
      (env, join [
        "{recextend ",
        eStr,
        " of ",
        nameGetStr ident,
        " with ",
        merged,
        "}"
      ])
  | TmExtProject {e = e, ident = ident, label = label} -> 
    match pprintCode indent env e with (env, exprStr) in 
    (env, join [
      "(",
      exprStr, 
      " of ",
      nameGetStr ident,
      ")->",
      label
    ])
end

lang ExtRecordTypePrettyPrint = PrettyPrint + ExtRecordTypeAst
  sem getTypeStringCode indent env = 
  | TyPre _ -> (env, "pre")
  | TyAbsent _ -> (env, "abs")
  | TyExtRec t -> 
    match pprintTypeName env t.ident with (env, name) in
    let ty = typeToString env t.ty in 
    (env, join [
      "extrec {",
      name,
      " of ",
      ty, 
      "}"
    ])
  | TyExtensionRow t -> 
    let pprintPair = lam p.
      match p with (ext, pre) in 
      join [nameGetStr ext, "^", typeToString env pre]
    in 

    let rowStr = strJoin ", " (map pprintPair (mapToSeq t.row)) in 

    -- (env, join [nameGetStr t.ident, " of <", rowStr, ">"])
    (env, join ["<", rowStr, ">"])
end

lang TypeAbsPrettyPrint = PrettyPrint + TypeAbsAst
  sem getTypeStringCode indent env =
  | TyAbs t -> 
    match pprintVarName env t.ident with (env, ident) in
    match getTypeStringCode indent env t.body with (env, body) in 
    (env, join ["Lam ", ident, ". ", body])
end

lang TypeAbsAppAst = PrettyPrint + TypeAbsAppAst
  sem getTypeStringCode indent env = 
  | TyAbsApp t -> 
    match getTypeStringCode indent env t.lhs with (env, lhs) in 
    match getTypeStringCode indent env t.rhs with (env, rhs) in 
    (env, join [lhs, " @ ", rhs])
end

lang PresenceKindPrettyPrint = PrettyPrint + PresenceKindAst 
  sem getKindStringCode (indent : Int) (env : PprintEnv) =
  | Presence () -> (env, "Presence")
end

lang ExtRecPrettyPrint = ExtRecTermPrettyPrint + ExtRecordTypePrettyPrint +
                         TypeAbsPrettyPrint + TypeAbsAppAst + 
                         PresenceKindPrettyPrint
end