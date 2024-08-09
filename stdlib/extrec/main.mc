-- The main file of the MLang pipline.
-- The semantic function `compileMLangToOcaml`, takes a filepath as input. 
-- It then puts the program at this file through the MLang pipeline and then
-- compiles it to OCaml.

include "map.mc"

include "boot-parser.mc"
include "symbolize.mc"
include "collect-env.mc"
include "pprint.mc"

include "mlang/include-handler.mc"
include "mlang/pprint.mc"
include "mlang/type-check.mc"
include "mlang/symbolize.mc"
include "mlang/const-transformer.mc"

include "mexpr/type-check.mc"

lang BigPrettyPrint = MLangPrettyPrint + ExtRecPrettyPrint 
end

lang BigSym = MLangSym + ExtRecordSym 
end

lang BigIncludeHandler = MLangIncludeHandler + BootParserMLang + ExtRecBootParser
end

lang BigPipeline = BigIncludeHandler + 
                     BigSym + 
                     BigPrettyPrint + 
                     ExtRecCollectEnv + 
                     MLangTypeCheck +
                     ExtRecordTypeCheck+ 
                     MLangConstTransformer

                     

  sem doIt =| filepath ->
    let p = parseAndHandleIncludes filepath in 

    let p = constTransformProgram builtin p in

    match symbolizeMLang symEnvDefault p with (_, p) in 

    let env = collectEnv (mapEmpty nameCmp) p.expr in 
    let tcEnv = {_tcEnvEmpty with extRecordType = env} in 

    let p = {p with expr = typeCheckExpr tcEnv p.expr} in 

    p

  sem pprintEnv =
  | env ->
    let pprintLabelMap = lam m.
      let seq = mapToSeq m in 
      let seqStr = map (lam p. join [
        p.0, 
        ": ",
        (type2str p.1)
      ]) seq in 
      strJoin ", " seqStr 
    in 

    let pprintUpper = lam p.  
      join [
        nameGetStr p.0,
        " :: {", 
        pprintLabelMap p.1,
        "}"
      ]
    in 

    strJoin "\n" (map pprintUpper (mapToSeq env))
end

mexpr 
use BigPipeline in
let p = doIt "example.mc" in 
printLn (mlang2str p) ; 

printLn "\n\n";

let env = collectEnv (mapEmpty nameCmp) p.expr in 
printLn (pprintEnv env) ;
()