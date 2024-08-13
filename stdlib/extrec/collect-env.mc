include "mexpr/ast.mc"
include "mexpr/type-check.mc"

include "digraph.mc"
include "error.mc"
include "map.mc"
include "name.mc"
include "set.mc"

type DependencyGraph = Digraph Name ()
type TyDeps = Map Name (Set Name)

lang ExtRecCollectEnv = MExprAst + ExtRecordAst + ExtRecordType
  sem collectEnv : ExtRecEnvType -> Expr -> ExtRecEnvType
  sem collectEnv env = 
  | TmRecType t -> 
    match mapLookup t.ident env with Some _ then
      errorMulti 
        [(t.info, nameGetStr t.ident)]
        "An extensible record type with this Name already exists!"
    else 
      let env = mapInsert t.ident (mapEmpty cmpString) env in 
      collectEnv env t.inexpr
  | TmRecField t -> 
    match t.tyIdent with TyArrow {from = lhs, to = rhs} then
      match lhs with TyCon {ident = ident} then 
        match mapLookup ident env with Some labelTypeMap then
          let labelTypeMap = mapInsert t.label rhs labelTypeMap in 
          let env = mapInsert ident labelTypeMap env in 
          collectEnv env t.inexpr
        else 
          errorMulti 
            [(t.info, "")]
            "The yyCon on rhs must be an extensible record type!"
      else
        errorMulti 
          [(t.info, "")]
          "The type of a record field must have TyCon on rhs!"
    else  
      errorMulti 
        [(t.info, "")]
        "The type of a record field must be an arrow type!"
  | expr -> 
    sfold_Expr_Expr collectEnv env expr

  sem includedRowTypes : Set Name -> Type -> Set Name 
  sem includedRowTypes acc = 
  | TyExtRec {ident = ident} -> setInsert ident acc
  | ty -> sfold_Type_Type includedRowTypes acc ty

  sem updateDependencyGraph : DependencyGraph -> Name -> [Type] -> DependencyGraph
  sem updateDependencyGraph graph name =| types -> 
    let includedTypes = foldl includedRowTypes (setEmpty nameCmp) types in 
    let graph = digraphMaybeAddVertex name graph in 
    let addEdge = lam g. lam n. 
      let g = digraphMaybeAddVertex n g in 
      digraphMaybeAddEdge name n () g
    in
    setFold addEdge graph includedTypes

  sem createDependencyGraph : ExtRecEnvType -> DependencyGraph 
  sem createDependencyGraph =
  | env ->
    let graph = digraphEmpty nameCmp (lam. lam. true) in 

    let work = lam graph. lam name. lam labelTyMap. 
      updateDependencyGraph graph name (mapValues labelTyMap) in 
    
    mapFoldWithKey work graph env

  sem updateTyDeps : DependencyGraph -> TyDeps -> Name -> TyDeps
  sem updateTyDeps graph acc = 
  | name -> 
    let deps = setOfKeys (digraphBFS name graph) in 
    mapInsert name deps acc

  sem computeTyDeps : DependencyGraph -> TyDeps 
  sem computeTyDeps = 
  | graph -> 
    let vertices = digraphVertices graph in 
    foldl (updateTyDeps graph) (mapEmpty nameCmp) vertices

  sem dumpTyDeps : TyDeps -> String
  sem dumpTyDeps =
  | tyDeps ->
    let pairs = mapToSeq tyDeps in
    let pprintPair = lam pair.
      match pair with (name, nameSet) in 
      let nameSetStr = strJoin ", " (map nameGetStr (setToSeq nameSet)) in 
      join ["tydeps(", nameGetStr name, ") = ", nameSetStr]
    in
    strJoin "\n" ["=== TyDeps ===", strJoin "\n" (map pprintPair pairs), "=== END TyDeps ==="]


  sem dumpDependencyGraph : DependencyGraph -> String
  sem dumpDependencyGraph = 
  | graph ->
    let edges = digraphEdges graph in 
    let edgesStr = map (lam e. join [nameGetStr e.0, " -> ", nameGetStr e.1]) edges in 
    strJoin "\n" (snoc (cons "=== DEPENDECY GRAPH ===" edgesStr) "=== END GRAPH ===")
end

-- TODO add some utests for ty dep calculation!