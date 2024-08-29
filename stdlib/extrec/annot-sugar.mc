include "map.mc"
include "name.mc"
include "digraph.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

include "mlang/ast.mc"

include "ast.mc"

type AnnotationSugarEnv = {}

type ExtensionMap = Map Name (Set Name)

let _handle_set = lam m : ExtensionMap. lam s : Set Name. 
  let work = lam acc. lam n.
    match mapLookup n m with Some s then setUnion s acc else setInsert n acc 
  in 
  setFold work (setEmpty nameCmp) s

lang AnnotationSugar = Ast + DataKindAst + AllTypeAst
  sem sugarAnnot : Digraph Name () -> ExtensionMap -> Type -> Type

  sem desugarType : ExtensionMap -> Type -> Type
  sem desugarType m = 
  | TyAll t ->
    TyAll {t with kind = desugarKind m t.kind,
                  ty = desugarType m t.ty}
  | ty -> 
    smap_Type_Type (desugarType m) ty

  sem desugarKind : ExtensionMap -> Kind -> Kind
  sem desugarKind m = 
  | Data k ->
    let work = lam types. {
      lower = _handle_set m types.lower,
      upper = optionMap (_handle_set m) types.upper
    } in 
    Data {k with types = mapMap work k.types}
  | k -> k

end

mexpr
use AnnotationSugar in 
use MExprAst in 

let extMap = mapFromSeq nameCmp [
  (nameNoSym "Base_Expr", setOfSeq nameCmp [nameNoSym "TmOne", nameNoSym "TmTwo"]),
  (nameNoSym "Other_Expr", setOfSeq nameCmp [nameNoSym "TmThree"]),
  (nameNoSym "Some_Expr", setOfSeq nameCmp [nameNoSym "TmFour"])
] in 

let myEq = lam t1. lam t2. and
  (setEq t1.lower t2.lower)
  ((optionEq setEq) t1.upper t2.upper) in 

-- Test empty data kind
let emptyData = Data {types = mapFromSeq nameCmp [(nameNoSym "Expr", {lower = setEmpty nameCmp, upper = None ()})]} in 
let desugarEmptyData = desugarKind extMap emptyData in 

match (emptyData, desugarEmptyData) with (Data d1, Data d2) in 
utest d1.types with d2.types using mapEq myEq in

-- Test non-empty data kind
let nonEmptyData = Data {types = mapFromSeq nameCmp 
  [(nameNoSym "Expr", {lower = setSingleton nameCmp (nameNoSym "Base_Expr"), 
                       upper = Some (setOfSeq nameCmp [nameNoSym "Other_Expr", nameNoSym "Some_Expr"])})]} in 
let desugarNonEmptyData = desugarKind extMap nonEmptyData in 
let expected = Data {types = mapFromSeq nameCmp 
  [(nameNoSym "Expr", {lower = setOfSeq nameCmp [nameNoSym "TmOne", nameNoSym "TmTwo"], 
                       upper = Some (setOfSeq nameCmp [nameNoSym "TmThree", nameNoSym "TmFour"])})]} in 
match (desugarNonEmptyData, expected) with (Data d1, Data d2) in 

utest d1.types with d2.types using mapEq myEq in

-- Test kind in TyAll gets desugared
use ExtRecordTypeAst in 
let ty = nstyall_ (nameNoSym "r") nonEmptyData (TyExtRec {info = NoInfo (), 
                                                          ident = nameNoSym "Foo",
                                                          ty = tyvar_ "r"}) in 
let desugaredTy = desugarType extMap ty in 
match desugaredTy with TyAll {kind = Data d1} in 
match expected with Data d2 in 

utest d1.types with d2.types using mapEq myEq in

()