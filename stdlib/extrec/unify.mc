include "mexpr/unify.mc"

include "ast.mc"

lang PresenceKindAstUnify = Unify + PresenceKindAst
  sem unifyKinds u env = 
  | (Presence _, Presence _) -> u.empty

  sem addKinds u env = 
  | (Presence _, Presence _) -> (u.empty, Presence ())
end