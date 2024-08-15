-- The main file of the MLang pipline.
-- The semantic function `compileMLangToOcaml`, takes a filepath as input. 
-- It then puts the program at this file through the MLang pipeline and then
-- compiles it to OCaml.

include "map.mc"

include "boot-parser.mc"
include "symbolize.mc"
include "collect-env.mc"
include "pprint.mc"
include "monomorphise.mc"

include "mlang/include-handler.mc"
include "mlang/pprint.mc"
include "mlang/type-check.mc"
include "mlang/symbolize.mc"
include "mlang/const-transformer.mc"

include "mexpr/type-check.mc"
include "mexpr/eval.mc"

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
                   MLangConstTransformer + 
                   ExtRecMonomorphise + 
                   MExprEval

  -- For some reason, this is missing some function definitions, but
  -- I can not figure out why. 
  sem dumpTypes : [String] -> Expr -> [String]
  sem dumpTypes acc = 
  | TmLet t -> 
    let acc = snoc acc (join [nameGetStr t.ident, " : ", type2str t.tyBody]) in 
    let acc = sfold_Expr_Expr dumpTypes acc t.body in 
    sfold_Expr_Expr dumpTypes acc t.inexpr
  | expr ->
    sfold_Expr_Expr dumpTypes acc expr

  sem doIt =| filepath ->
    let p = parseAndHandleIncludes filepath in 

    let p = constTransformProgram builtin p in

    match symbolizeMLang symEnvDefault p with (_, p) in 

    let defs = collectEnv (mapEmpty nameCmp) p.expr in 

    let depGraph = createDependencyGraph defs in 
    printLn (dumpDependencyGraph depGraph) ;

    let tyDeps = computeTyDeps depGraph in 
    printLn (dumpTyDeps tyDeps) ;

    let labelTyDeps = computeLabelTyDeps tyDeps defs in 

    let tcEnv = {_tcEnvEmpty with extRecordType = {defs = defs, 
                                                   tyDeps = tyDeps,
                                                   labelTyDeps = labelTyDeps}} in 

    let p = {p with expr = typeCheckExpr tcEnv p.expr} in 

    printLn (strJoin "\n" (dumpTypes [] p.expr));
    printLn (expr2str p.expr);

    -- let p = {p with expr = monomorphiseExpr env p.expr} in 

    p

  sem runIt =| filepath ->
    let p = doIt filepath in 
    let result = eval (evalCtxEmpty ()) p.expr in 
    printLn (expr2str result);
    result

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
-- let p = doIt "basic.mc" in 
let p = doIt "example.mc" in 
-- printLn (mlang2str p) ; 

-- printLn "\n\n";

-- runIt "example.mc";

()