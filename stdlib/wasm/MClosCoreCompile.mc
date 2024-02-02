include "MClosCore.mc"
include "wasm-ast.mc"
include "wasm-pprint.mc"
include "string.mc"
include "common.mc"

type Context = {
    nameToFP: [(String, Int)]
}

recursive
let findName = lam l: [(String, Int)]. lam name: String. 
    match l with []
        then error "Name not found"
        else match head l with (id, fp)
            then 
                if eqString id name 
                    then fp 
                    else (findName (tail l) name)
            else error "Error unexpected mismatch!"
end


lang MClosCoreCompile = MClosCore + WasmAST
    sem compileExpr: Context -> Expr -> Instr
    sem compileExpr ctx = 
    | TmApp(TmFunc fname, TmEnvAdd r) -> 
        let fp = findName ctx.nameToFP fname in 
        let idToTMEnvVar = lam env. lam id. TmEnvVar(env, id) in
        let allValues = lam env.
            match env with BasicEnv r
                then
                    let tmEnvVars = map (idToTMEnvVar env) r.envVars in
                    map (compileExpr ctx) tmEnvVars
                else error "???" in
        let newEnv = match r.target with BasicEnv targetEnv
            then match r.src with BasicEnv sourceEnv
                then StructNew {
                    typeAlias = targetEnv.wasmTypeAlias,
                    values = cons (compileExpr ctx r.value) (allValues r.src)
                } 
            else error "???"
        else error "???" in 
        StructNew {
            typeAlias = "clos",
            values = [I32Const fp, newEnv]
        }
    | TmApp(e1, e2) -> 
        let res1 = compileExpr ctx e1 in
        let res2 = compileExpr ctx e2 in 
        Call ("apply", [res1, res2])
    | TmInt(i) -> 
        Call ("box", [I32Const i])
    | TmAdd(e1, e2) -> 
        let unbox = lam e. Call ("unbox", [e]) in
        let r1 = unbox (compileExpr ctx e1) in
        let r2 = unbox (compileExpr ctx e2) in 
        let addInstr = I32Add(r1, r2) in
        Call ("box", [addInstr])
    | TmFunc(id) -> 
        let fp = findName ctx.nameToFP id in
        let envName = concat id "-env" in
        StructNew {
            typeAlias = "clos",
            values = [I32Const fp, StructNew {typeAlias = envName, values = []}]
        }
    | TmVar(id) -> LocalGet id
    | TmEnvVar(env, id) -> match env with BasicEnv r
        then 
            StructGet {
                typeAlias = r.wasmTypeAlias,
                field = id,
                value = (RefCast {
                    typeAlias = r.wasmTypeAlias,
                    value = LocalGet "env"
                })
            }
        else error "Only BasicEnv is supported!"
    | TmEnvAdd r -> 
        error "Unsupported TmEnvAdd"
        -- let idToTMEnvVar = lam env. lam id. TmEnvVar(env, id) in
        -- let allValues = lam env.
        --     match env with BasicEnv r
        --         then
        --             let tmEnvVars = map (idToTMEnvVar env) r.envVars in
        --             map (compileExpr ctx) tmEnvVars
        --         else error "???" in
        -- match r.target with BasicEnv targetEnv
        --     then match r.src with BasicEnv sourceEnv
        --         then StructNew {
        --             typeAlias = targetEnv.wasmTypeAlias,
        --             values = cons (compileExpr ctx r.value) (allValues r.src)
        --         } 
        --     else error "???"
        -- else error "???"

    sem compileDef: Context -> Def -> Func
    sem compileDef ctx = 
    | FuncDef(fname, env, id, body) -> match env with BasicEnv r
        then
            let envType = r.wasmTypeAlias in
            let locals = [
                {name = "env", typeAlias=join["(ref $", envType, ")"]},
                {name=id, typeAlias="(ref $i32box)"}
            ] in
            let body = compileExpr ctx body in 
            let setLocal = LocalSet (
                "env",
                RefCast {typeAlias = envType, value = LocalGet "arg0"}) in
            let setLocal2 = LocalSet (
                id,
                RefCast {typeAlias = "i32box", value = LocalGet "arg1"}) in
            Function {
                name = fname,
                args = [
                    {name="arg0", typeString="anyref"}, 
                    {name="arg1", typeString="anyref"}
                ],
                locals = locals,
                resultTypeString = "anyref",
                instructions = [setLocal, setLocal2, body]
            }
        else 
            error "error"

    sem compileEnvToWasmType: Env -> WasmType
    sem compileEnvToWasmType = 
    | BasicEnv r -> 
        let var2wasmfield = lam var. {name = var, typeString = "(ref $i32box)"} in
        StructType {
            name = r.wasmTypeAlias,
            fields = map var2wasmfield r.envVars
        }

    sem wrapExprInMExpr: Instr -> Func
    sem wrapExprInMExpr = 
    | instr -> 
        let setResultInstr = LocalSet("result", instr) in
        let unboxResultInstr = Call(
            "unbox", 
            [RefCast {
                typeAlias = "i32box", 
                value = LocalGet "result"}]) in
        Function {
            name = "mexpr",
            args = [],
            resultTypeString = "i32",
            locals = [{name = "result", typeAlias="anyref"}],
            instructions = [setResultInstr, unboxResultInstr]
        }

    sem createCtx: [Def] -> Context
    sem createCtx = 
    | defs -> 
        let def2tuple = lam index. lam def. 
            match def with FuncDef(name, _, _, _)
                then (name, index)
                else error "Unsupported Def"
        in {nameToFP = mapi def2tuple defs}

    -- sem compile: [Def] -> Expr -> Context
    sem compile defs = 
    | expr -> 
        let def2env = lam def. match def with FuncDef(_, env, _, _)
            then env 
            else error "Unknown Def"
        in 
        let def2name = lam def. match def with FuncDef(name, _, _, _)
            then name 
            else error "Unknown Def"
        in 
        let closType = StructType {
            name = "clos",
            fields = [
                {name = "func_pointer", typeString = "i32"},
                {name = "env", typeString = "anyref"}
            ]
        } in 
        let i32boxType = StructType {
            name = "i32box",
            fields = [{name = "value", typeString = "i32"}]    
        } in
        let genericType = FunctionType {
            name = "generic-type",
            paramTypeStrings = ["anyref", "anyref"],
            resultTypeString = "anyref"
        } in 
        let box = Function {
            name = "box",
            args = [{name="x", typeString="i32"}],
            locals = [],
            resultTypeString = "(ref $i32box)",
            instructions = [StructNew {
                typeAlias = "i32box",
                values = [LocalGet "x"]
            }]
        } in
        let unbox = Function {
            name = "unbox",
            args = [{name="box", typeString="(ref $i32box)"}],
            locals = [],
            resultTypeString = "i32",
            instructions = [StructGet {
                typeAlias = "i32box",
                field="value",
                value = LocalGet "box"
            }]
        } in 
    let apply = Function {
            name = "apply",
            args = [
                {name = "cl_uncast", typeString="anyref"},
                {name = "arg", typeString="anyref"}
            ],
            locals = [{name = "cl", typeAlias = "(ref $clos)"}],
            resultTypeString = "anyref",
            instructions = [
                LocalSet ("cl", RefCast {
                    typeAlias = "clos",
                    value = LocalGet "cl_uncast"
                }),
                CallIndirect {
                    typeString = "generic-type",
                    args = [
                        StructGet {
                            typeAlias = "clos",
                            value = LocalGet "cl",
                            field = "env"
                        },
                        LocalGet "arg"
                    ],
                    fp = StructGet {
                        typeAlias = "clos",
                        value = LocalGet "cl",
                        field = "func_pointer"
                    }
                }
            ]
        } in 
        let ctx = createCtx defs in 
        let envs = map def2env defs in 
        let fnames = map def2name defs in 
        let table = Table {size = length fnames, typeString = "funcref"} in
        let elem = Elem {offset = I32Const 0, funcNames = fnames} in 
        let types = concat [closType, i32boxType, genericType] (map compileEnvToWasmType envs) in 
        let functions = map (compileDef ctx) defs in
        let main = wrapExprInMExpr (compileExpr ctx expr) in 
        Module {
            functions = join [[box, unbox], functions, [apply, main]],
            table = table,
            elem = elem,
            types = types,
            exports = ["mexpr"]
        }
    -- Module {functions = [], exports = []}
end

mexpr
-- let h lam env. lam z. x + y + z
use MClosCoreCompile in 
let h_env = BasicEnv {wasmTypeAlias = "h-env", envVars=["y", "x"]} in
let h = FuncDef("h", h_env, "z", TmAdd(
    TmAdd(
        TmEnvVar(h_env, "x"), 
        TmEnvVar(h_env, "y")
    ), TmVar("z"))) in

let g_env = BasicEnv {wasmTypeAlias = "g-env", envVars=["x"]} in
let g = FuncDef("g", g_env, "y", TmApp(TmFunc("h"), TmEnvAdd {
    src = g_env,
    target = h_env, 
    newId = "y",
    value = TmVar("y")
})) in

let f_env = BasicEnv {wasmTypeAlias = "f-env", envVars=[]} in
let f = FuncDef("f", f_env, "x", TmApp(TmFunc("g"), TmEnvAdd {
    src = f_env,
    target = g_env, 
    newId = "x",
    value = TmVar("x")
})) in

let gEnvType = compileEnvToWasmType g_env in 
let gEnvTypeStr = (use WasmPPrint in pprintType 0 gEnvType) in 
let main = TmApp(TmApp(TmApp(TmFunc("f"), TmInt(1)), TmInt(-5)), TmInt(1)) in 

let mod = compile [f, g, h] main in
let s = (use WasmPPrint in pprintMod mod) in 
(printLn s)