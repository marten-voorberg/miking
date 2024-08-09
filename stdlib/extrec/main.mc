-- The main file of the MLang pipline.
-- The semantic function `compileMLangToOcaml`, takes a filepath as input. 
-- It then puts the program at this file through the MLang pipeline and then
-- compiles it to OCaml.

include "boot-parser.mc"
include "symbolize.mc"
include "pprint.mc"

include "mlang/include-handler.mc"
include "mlang/pprint.mc"
include "mlang/symbolize.mc"

lang BigPrettyPrint = MLangPrettyPrint + ExtRecPrettyPrint 
end

lang BigSym = MLangSym + ExtRecordSym 
end

lang BigIncludeHandler = MLangIncludeHandler + BootParserMLang + ExtRecBootParser
end

lang BigPipeline = BigIncludeHandler + 
                     BigSym + 
                     BigPrettyPrint
                     

  sem doIt =| filepath ->
    let p = parseAndHandleIncludes filepath in 
    match symbolizeMLang symEnvDefault p with (_, p) in 
    p
end

mexpr 
use BigPipeline in
printLn (mlang2str (doIt "example.mc")) ; 
()