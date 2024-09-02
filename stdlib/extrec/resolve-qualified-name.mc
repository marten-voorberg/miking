include "mlang/ast.mc"

include "map.mc"
include "name.mc"
include "digraph.mc"
include "set.mc"

type ResolveStaticEnv = {
  tydeps : Map Name (Set Name)
}
type ResolveLangEnv = {
  prodFields : Map Name (Set Name),
  sumFields : Map Name (Set Name)
}
type ResolveQualifiedNameEnv = {
  langEnvs : Map Name ResolveLangEnv
}

lang ResolveQualifiedName = MLangAst
  sem resolveQualifiedNames : ResolveStaticEnv -> 
                              ResolveLangEnv -> 
                              Decl -> 
                              (ResolveLangEnv, Decl)
  sem resolveQualifiedNames staticEnv accEnv =
  | DeclLang d -> never
  | other -> (accEnv, other)

  
end