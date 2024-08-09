include "pprint.mc"

include "mexpr/ast.mc"
include "mexpr/boot-parser.mc"

include "mlang/boot-parser.mc"
include "mlang/pprint.mc"

include "name.mc"

lang ExtRecBootParser = BootParserMLang + ExtRecordAst
  sem matchTerm t = 
  | 117 -> 
    TmRecType {ident = gname t 0,
               ty = tyunknown_,
               inexpr = gterm t 0,
               info = ginfo t 0}
  | 118 -> 
    TmRecField {label = gstr t 0,
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
  "recfield x : Foo -> Int in",
  "let r = {Foo of x = 1} in ",
  "(r of Foo)->x"
] in
let p = parseProgram str in 
printLn (mlang2str p) ;

()