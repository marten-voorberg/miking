include "pprint.mc"
include "ast.mc"

include "mexpr/ast.mc"
include "mexpr/boot-parser.mc"

include "mlang/boot-parser.mc"
include "mlang/pprint.mc"

include "name.mc"
include "ast.mc"
include "ast-builder.mc"

lang ExtRecBootParser = BootParserMLang + ExtRecordAst + ExtRecordTypeAst
  sem matchTerm t = 
  | 117 -> 
    let n = glistlen t 0 in 
    let params = map (lam i. gname t (addi i 1)) (range 0 n 1) in 

    TmRecType {ident = gname t 0,
               params = params,
               ty = tyunknown_,
               inexpr = gterm t 0,
               info = ginfo t 0}
  | 118 -> 
    TmRecField {label = gstr t 0,
                extIdent = gname t 1,
                tyIdent = gtype t 0,
                inexpr = gterm t 0,
                ty = tyunknown_,
                info = ginfo t 0}
  | 119 ->
    let n = glistlen t 0 in 
    let ident = gname t 0 in 
    let bindingPairs = map (lam i. (gstr t (addi 1 i), gterm t i)) (range 0 n 1) in 
    TmExtRecord {bindings = mapFromSeq cmpString bindingPairs, 
                 ident = ident,
                 ty = tyunknown_, 
                 info = ginfo t 0}
  | 120 -> 
    TmExtProject {e = gterm t 0, 
                  ident = gname t 0,
                  label = gstr t 1, 
                  ty = tyunknown_,
                  info = ginfo t 0}
  | 121 ->
    let n = glistlen t 0 in 
    let ident = gname t 0 in 
    let e = gterm t 0 in 
    let bindingPairs = map (lam i. (gstr t (addi 1 i), gterm t (addi 1 i))) (range 0 n 1) in 
    TmExtUpdate {bindings = mapFromSeq cmpString bindingPairs, 
                 ident = ident,
                 e = e,
                 ty = tyunknown_, 
                 info = ginfo t 0}
  | 122 ->
    let n = glistlen t 0 in 
    let ident = gname t 0 in 
    let e = gterm t 0 in 
    let bindingPairs = map (lam i. (gstr t i, gterm t (addi 1 i))) (range 0 n 1) in 
    TmExtExtend {bindings = mapFromSeq cmpString bindingPairs, 
                 e = e,
                 ty = tyunknown_, 
                 info = ginfo t 0}

  sem matchType t = 
  | 215 -> 
    TyExtRec {info = ginfo t 0,
              ident = gname t 0,
              ty = gtype t 0}
end

lang RecDeclBootParser = BootParserMLang + ExtRecordTypeAst + RecTypeDeclAst + 
                         RecFieldDeclAst
  sem matchTop d = 
  | 711 ->
    let n = glistlen d 0 in 
    let params = map (lam i. gname d (addi i 1)) (range 0 n 1) in 
    RecTypeDecl {info = ginfo d 0,
                 ident = gname d 0,
                 params = params}
  | 712 ->
    RecFieldDecl {info = ginfo d 0,
                  label = gstr d 0,
                  extIdent = gname d 1, 
                  tyLabel = gtype d 0}
end

lang MyPrettyPrint = MLangPrettyPrint + ExtRecPrettyPrint 
end

mexpr
use ExtRecBootParser in 
use MyPrettyPrint in 
let parseProgram = lam str.
  match result.consume (parseMLangString str) with (_, Right p) in p
in

-- Test syn product extension
let str = strJoin "\n" [
  "mexpr",
  "rectype Foo in",
  "recfield x of MyExt: Foo -> Int in",
  "let r = {Foo of x = 1} in ",
  "(r of Foo)->x"
] in
let p = parseProgram str in 
printLn (mlang2str p) ;

()