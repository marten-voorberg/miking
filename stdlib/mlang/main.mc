include "result.mc"
include "fileutils.mc"
include "set.mc"
include "sys.mc"

include "compile.mc"
include "boot-parser.mc"
include "ast-builder.mc"
include "symbolize.mc"
include "composition-check.mc"
include "include-handler.mc"
include "const-transformer.mc"

include "mexpr/eval.mc"
include "mexpr/builtin.mc"

lang MainLang = MLangCompiler + BootParserMLang + 
                MLangSym + MLangCompositionCheck +
                MExprPrettyPrint + MExprEval + MExprEq + 
                MLangConstTransformer + MLangIncludeHandler 

  sem myEval : Expr -> Expr
  sem myEval =| e ->
    eval (evalCtxEmpty ()) e 

  sem evalMLangFile : String -> Expr
  sem evalMLangFile =| filepath ->
    let dir = filepathConcat (sysGetCwd ()) (eraseFile filepath) in 
    let libs = addCWDtoLibs (parseMCoreLibsEnv ()) in

    let p = handleIncludesFile (setEmpty cmpString) dir libs filepath in 
    let p = constTransformProgram builtin p in
    match symbolizeMLang symEnvDefault p with (_, p) in 
    match _consume (checkComposition p) with (_, res) in 
    match res with Right env in
    let ctx = _emptyCompilationContext env in 
    let res = _consume (compile ctx p) in 
    match res with (_, rhs) in 
    match rhs with Right expr in
    myEval expr
end

mexpr
use MainLang in 
evalMLangFile "stdlib/map.mc"; 
()