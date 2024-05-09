include "ast.mc"
include "boot-parser.mc"
include "pprint.mc"

include "set.mc"
include "stdlib.mc"
include "fileutils.mc"
include "sys.mc"

type IncludeEnv = {currentDir : String,
                   libs : Map String String}

-- OPT(voorberg, 06/05/2024): This naively copy includes into the 
-- MLang program, even if they have already been included. There 
-- is obviously a lot of potential for improvement here.
lang MLangIncludeHandler = MLangAst + BootParserMLang
  sem parseFileWithIncludes : Map String String -> String -> MLangProgram
  sem parseFileWithIncludes libs =| path ->
    let env = {currentDir = eraseFile path, libs = libs} in 
    match _consume (parseMLangFile path) with (_, errOrProg) in
    switch errOrProg
      case Left err then error (join [
        "File '",
        path,
        "' could not be parsed!"
      ])
      case Right prog then 
        let decls = prog.decls in 
        let envs = make (length decls) env in 
        let declEnvPairs = zip envs decls in 

        match mapAccumL flattenIncludes (setEmpty cmpString) declEnvPairs
        with (_, listOfDecls) in 

        {prog with decls = join listOfDecls}
    end


  -- sem handleIncludesFile : Set String -> IncludeEnv -> (Set String, MLangProgram)
  -- sem handleIncludesFile includes =| args ->
  --   match _consume (parseMLangFile args.path) with (_, errOrProg) in
  --   switch errOrProg
  --     case Left err then error (join [
  --       "File '",
  --       path,
  --       "' could not be parsed!"
  --     ])
  --     case Right prog then 
  --       handleIncludesProgram dir libs prog
  --   end

  sem flattenIncludes : Set String -> (IncludeEnv, Decl) -> (Set String, [Decl])
  sem flattenIncludes included =
  | (env, DeclInclude {path = path}) ->
    let path = findPath env path in 

    if setMem path included then 
      (included, [])
    else 
      let path = findPath env path in 
      match _consume (parseMLangFile path) with (_, errOrProg) in
      switch errOrProg
        case Left err then error (join [
          "File '",
          path,
          "' could not be parsed!"
        ])
        case Right prog then 
          let env = {env with currentDir = eraseFile path} in 

          let decls = prog.decls in 
          let envs = make (length decls) env in 
          let declEnvPairs = zip envs decls in 

          match mapAccumL flattenIncludes included declEnvPairs 
          with (included, listOfDecls) in 

          (included, join listOfDecls)
        end
  | (_, other) -> (included, [other])

  -- sem findPath : IncludeEnv -> String -> String
  sem findPath env =| path ->
    let libs = mapInsert "current" env.currentDir env.libs in 
    let prefixes = mapValues libs in 
    let paths = map (lam prefix. filepathConcat prefix path) prefixes in 

    let existingFiles = filter sysFileExists paths in 
    let existingFilesAsSet = setOfSeq cmpString existingFiles in 

    switch (setSize existingFilesAsSet)
      case 0 then 
        printLn path;
        error "File not found!"
      case _ then head (setToSeq existingFilesAsSet)
      case _ then 
        printLn path;
        iter printLn existingFiles;
        error "Multiple files were found!"
    end
end

mexpr
use MLangPrettyPrint in 
use MLangIncludeHandler in 

let dir = sysGetCwd () in 
let libs = addCWDtoLibs (parseMCoreLibsEnv ()) in

printLn (mlang2str (parseFileWithIncludes libs "stdlib/seq.mc"))