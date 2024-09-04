-- The main file of the MLang pipline.
-- The semantic function `compileMLangToOcaml`, takes a filepath as input. 
-- It then puts the program at this file through the MLang pipeline and then
-- compiles it to OCaml.

include "map.mc"
include "seq.mc"

include "boot-parser.mc"
include "symbolize.mc"
include "collect-env.mc"
include "pprint.mc"
include "compile.mc"
include "type-check.mc"
include "unify.mc"
include "monomorphise.mc"
include "resolve-qualified-name.mc"
include "mlang-ty-deps.mc"

include "mlang/include-handler.mc"
include "mlang/pprint.mc"
include "mlang/type-check.mc"
include "mlang/symbolize.mc"
include "mlang/const-transformer.mc"
include "mlang/language-composer.mc"
include "mlang/composition-check.mc"
include "mlang/compile.mc"

include "mexpr/type-check.mc"
include "mexpr/eval.mc"

lang BigPrettyPrint = MLangPrettyPrint + ExtRecPrettyPrint 
end

lang BigSym = MLangSym + ExtRecordSym + RecFieldDeclSym + RecTypeDeclSym
end

lang BigTypeCheck = MExprTypeCheckMost + GetPresenceKind + MExprTypeCheckLamLetVar +
                    ExtRecordTypeCheck + ExtRowUnify + PresenceKindAstUnify
end

lang BigIncludeHandler = MLangIncludeHandler + BootParserMLang + ExtRecBootParser + RecDeclBootParser
end

lang BigPipeline = BigIncludeHandler + 
                   BigSym + 
                   BigPrettyPrint + 
                   ExtRecCollectEnv + 
                   BigTypeCheck +
                   ExtRecordTypeCheck+ 
                   MLangConstTransformer + 
                   ExtRecMonomorphise + 
                   MExprEval + 
                   LanguageComposer +
                   MLangCompositionCheck +
                   MLangCompiler + 
                   RecFieldDeclCompiler + 
                   RecTypeDeclCompiler + 
                   ResolveQualifiedName + 
                   ComputeMLangTyDeps

  -- For some reason, this is missing some function definitions, but
  -- I can not figure out why. 
  sem dumpTypes : [String] -> Expr -> [String]
  sem dumpTypes acc = 
  | TmLet t -> 
    let acc = snoc acc (join [nameGetStr t.ident, " : ", type2str t.tyBody]) in 
    let acc = sfold_Expr_Expr dumpTypes acc t.body in 
    sfold_Expr_Expr dumpTypes acc t.inexpr
  | TmRecLets t -> 
    let acc = foldl 
      (lam acc. lam b. snoc acc (join [nameGetStr b.ident, " : ", type2str b.tyBody]))
      acc 
      t.bindings in 
    sfold_Expr_Expr dumpTypes acc t.inexpr
  | expr ->
    sfold_Expr_Expr dumpTypes acc expr

  sem doIt =| filepath ->
    let p = parseAndHandleIncludes filepath in 


    let p = constTransformProgram builtin p in

    
    let p = composeProgram p in 

    -- printLn (mlang2str p);

    match symbolizeMLang symEnvDefault p with (_, p) in 



    match result.consume (checkCompositionWithOptions defaultCompositionCheckOptions p) 
    with (_, Right compositionCheckEnv) in 

    let mlangTyDeps = getProgTyDeps compositionCheckEnv.baseMap2 p in  
    -- printLn (dumpTyDeps mlangTyDeps) ;

    -- let p = resolveQualifiedNameProgram tyDeps p in 
    let langEnvs = gatherLangEnvs mlangTyDeps p in 

    -- printLn (mlang2str p);

    let compilationCtx = _emptyCompilationContext compositionCheckEnv in 
    let res = result.consume (compile compilationCtx p) in 

    match res with (_, Right expr) in 

    -- printLn (expr2str expr);

    let accEnv = collectEnv _emptyAccEnv expr in 
    let defs = accEnv.defs in 

    let depGraph = createDependencyGraph defs in 
    -- printLn (dumpDependencyGraph depGraph) ;

    let tyDeps = computeTyDeps depGraph in 
    -- printLn (dumpTyDeps tyDeps) ;

    let labelTyDeps = computeLabelTyDeps tyDeps defs in 

    let tcEnv = {typcheckEnvDefault with
      disableConstructorTypes = false, 
      extRecordType = {defs = defs, 
                       tyDeps = tyDeps,
                       mlangTyDeps = mlangTyDeps,
                       labelTyDeps = labelTyDeps,
                       langEnvs = langEnvs}} in 

    let expr = typeCheckExpr tcEnv expr in 

    printLn (strJoin "\n" (dumpTypes [] expr));
    -- printLn (expr2str expr);

    expr

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
-- let p = doIt "temp/basic.mc" in 
-- let p = doIt "temp/constructor-types.mc" in 
-- let p = doIt "temp/point.mc" in 
let p = doIt (last argv) in 

-- let p = doIt "example.mc" in 
-- let p = doIt "symbolize-example/simple-sym.mc" in 
-- let p = doIt "temp/family.mc" in 
-- let p = doIt "temp/prodext.mc" in 
-- let p = doIt "temp/extend.mc" in 



-- let p = doIt "stdlib/name.mc" in


-- printLn (mlang2str p) ; 

-- printLn "\n\n";

-- runIt "example.mc";

()