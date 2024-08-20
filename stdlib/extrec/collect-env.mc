include "mexpr/ast.mc"
include "mexpr/type-check.mc"

include "digraph.mc"
include "error.mc"
include "map.mc"
include "name.mc"
include "set.mc"
include "tuple.mc"
include "ast.mc"

type DependencyGraph = Digraph Name ()
type TyDeps = Map Name (Set Name)
type LabelTyDeps = Map Name (Map String (Set Name))

type AccEnv = {defs : ExtRecDefs,
               tyToExts : Map Name (Set Name),
               tyLabelToExt : Map (Name, String) Name,
               tyExtToLabel : Map (Name, Name) (Set String)}

let _emptyAccEnv : AccEnv = {
  defs = mapEmpty nameCmp,
  tyToExts = mapEmpty nameCmp,
  tyLabelToExt = mapEmpty (tupleCmp2 nameCmp cmpString),
  tyExtToLabel = mapEmpty (tupleCmp2 nameCmp nameCmp)
}

lang ExtRecCollectEnv = MExprAst + ExtRecordAst + ExtRecordTypeAst + 
                        TypeAbsAst
  sem collectEnv : AccEnv -> Expr -> AccEnv
  sem collectEnv env = 
  | TmRecType t -> 
    match mapLookup t.ident env.defs with Some _ then
      errorMulti 
        [(t.info, nameGetStr t.ident)]
        "An extensible record type with this Name already exists!"
    else 
      let defs = mapInsert t.ident (mapEmpty cmpString) env.defs in 
      collectEnv {env with defs = defs} t.inexpr
  | TmRecField t -> 
    match t.tyIdent with TyAll tyAll then 
      -- TODO: check tyAll.kind
      match tyAll.ty with TyArrow {from = lhs, to = rhs} then
        match lhs with TyCon {ident = ident} then 
          match mapLookup ident env.defs with Some labelTypeMap then
            -- Update defs
            let ty = TyAbs {ident = tyAll.ident,
                            kind = Mono (),
                            body = rhs} in 
            let labelTypeMap = mapInsert t.label (t.extIdent, ty) labelTypeMap in 

            let work = lam optSet.
              let s = match optSet with Some s then s else setEmpty nameCmp in 
              Some (setInsert t.extIdent s)
            in 
            let tyToExts = mapUpdate ident work env.tyToExts in 
            
            let tyLabelToExt = mapInsert (ident, t.label) t.extIdent env.tyLabelToExt in 
            
            let work = lam optSet.
              let s = match optSet with Some s then s else setEmpty cmpString in 
              Some (setInsert t.label s) 
            in
            let tyExtToLabel = mapUpdate (ident, t.extIdent) work env.tyExtToLabel in 


            let env = {env with defs = mapInsert ident labelTypeMap env.defs,
                                tyToExts = tyToExts,
                                tyLabelToExt = tyLabelToExt,
                                tyExtToLabel = tyExtToLabel} in 
            collectEnv env t.inexpr
          else 
            errorMulti 
              [(t.info, "")]
              "The tyCon on lhs must be an extensible record type!"
        else
          errorMulti 
            [(t.info, "")]
            "The type of a record field must have TyCon on lhs!"
      else  
        errorMulti 
          [(t.info, "")]
          "The type of a record field must be an arrow type!"
    else 
      errorSingle [t.info] "The type of a record field must be quantified over a mapping!"
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

  sem createDependencyGraph : ExtRecDefs -> DependencyGraph 
  sem createDependencyGraph =
  | env ->
    let graph = digraphEmpty nameCmp (lam. lam. true) in 

    let work = lam graph. lam name. lam labelTyMap. 
      updateDependencyGraph graph name (map snd (mapValues labelTyMap)) in 
    
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

  sem computeLabelTyDeps : TyDeps -> ExtRecDefs -> LabelTyDeps
  sem computeLabelTyDeps tydeps = 
  | defs -> 
    let work = lam n. lam innerMap. mapMapWithKey (lam label. lam pair.
      match pair with (ext, ty) in 
      let includedNames = includedRowTypes (setEmpty nameCmp) ty in 
      setFold (lam acc. lam n. setUnion acc (match mapLookup n tydeps with Some s in s)) (setEmpty nameCmp) includedNames
    ) innerMap in 
    mapMapWithKey work defs

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