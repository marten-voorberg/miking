include "mexpr/pprint.mc"
include "mexpr/ast.mc"

lang ExtRecPrettyPrint = TypePrettyPrint + PrettyPrint + ExtRecordAst 
  sem isAtomic =
  | TmRecField _ | TmRecType _ -> false
  | TmExtRecord _ | TmExtProject _ -> true

  sem pprintCode (indent : Int) (env: PprintEnv) =
  | TmRecType t ->
    match pprintTypeName env t.ident with (env, name) in
    match pprintCode indent env t.inexpr with (env, inexpr) in
    (env, join [
      "rectype ",
      name,
      " in", pprintNewline indent,
      inexpr])
  | TmRecField t -> 
    let ty =  typeToString env t.tyIdent in 
    match pprintCode indent env t.inexpr with (env, inexpr) in
    (env, join [
      "recfield ",
      t.label, 
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