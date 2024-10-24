include "wasm-ast.mc"
include "wasm-pprint.mc"
include "wasm-rope.mc"
include "wasm-float.mc"

-- Integer Operations
let createIntBinop = lam ident. lam instrProducer.
    use WasmAST in 
    FunctionDef {
        ident = (nameNoSym ident),
        args = [
            {ident=(nameNoSym "lhs"), ty=Anyref ()},
            {ident=(nameNoSym "rhs"), ty=Anyref()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            I31Cast (
                instrProducer 
                    (I31GetS (RefCast {ty = I31Ref (), value = LocalGet (nameNoSym "lhs")}))
                    (I31GetS (RefCast {ty = I31Ref(), value = LocalGet (nameNoSym "rhs")}))
            )
        ]
    }

let addiWasm = 
    use WasmAST in 
    createIntBinop "addi" (lam l. lam r. I32Add (l, r))

let subiWasm = 
    use WasmAST in 
    createIntBinop "subi" (lam l. lam r. I32Sub (l, r))

let muliWasm = 
    use WasmAST in 
    createIntBinop "muli" (lam l. lam r. I32Mul (l, r))

let diviWasm = 
    use WasmAST in 
    createIntBinop "divi" (lam l. lam r. I32DivS (l, r))

let modiWasm = 
    use WasmAST in 
    createIntBinop "modi" (lam l. lam r. I32RemS (l, r))

let negiWasm = 
    use WasmAST in 
    FunctionDef {
        ident = (nameNoSym "negi"),
        args = [
            {ident=(nameNoSym "arg"), ty=Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            I31Cast (
                I32Sub (
                    I32Const 0,
                    (I31GetS (RefCast {ty = I31Ref(), value = LocalGet (nameNoSym "arg")}))
                )
            )
        ]
    }

-- slli = shift left logical integer
let slliWasm =
    use WasmAST in 
    createIntBinop "slli" (lam l. lam r. I32Shl (l, r))

-- TODO: Test difference between srli and srai. 
-- srli = shift right logical integer
let srliWasm =
    use WasmAST in 
    createIntBinop "srli" (lam l. lam r. I32ShrU (l, r))

-- srai = shift right arithmatic integer
let sraiWasm =
    use WasmAST in 
    createIntBinop "srai" (lam l. lam r. I32ShrS (l, r))

let eqiWasm = 
    use WasmAST in
    createIntBinop "eqi" (lam l. lam r. I32Eq (l, r))

let neqiWasm = 
    use WasmAST in
    createIntBinop "neqi" (lam l. lam r. I32Ne (l, r))

let ltiWasm = 
    use WasmAST in
    createIntBinop "lti" (lam l. lam r. I32LtS (l, r))

let gtiWasm = 
    use WasmAST in
    createIntBinop "gti" (lam l. lam r. I32GtS (l, r))

let leqiWasm = 
    use WasmAST in
    createIntBinop "leqi" (lam l. lam r. I32LeS (l, r))

let geqiWasm = 
    use WasmAST in
    createIntBinop "geqi" (lam l. lam r. I32GeS (l, r))

let idWasm = 
    use WasmAST in 
    let arg = nameSym "arg" in 
    FunctionDef {
        ident = nameNoSym "id",
        args = [
            {ident = arg, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [LocalGet arg]
    }

let constTrueWasm = 
    use WasmAST in 
    let arg = nameSym "arg" in 
    FunctionDef {
        ident = nameNoSym "const-true",
        args = [
            {ident = arg, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [I31Cast (I32Const 1)]
    }

let anyrefBoxDef = 
    use WasmAST in 
    StructTypeDef {
        ident = nameNoSym "anyref-box",
        fields = [
            {ident = nameNoSym "value", ty = Mut (Anyref ())}
        ]
    }

let refWasm = 
    let arg = nameSym "arg" in 
    use WasmAST in 
    FunctionDef {
        ident = nameNoSym "ref",
        args = [
            {ident = arg, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            StructNew {
                structIdent = nameNoSym "anyref-box",
                values = [LocalGet arg]
            }
        ]
    }

let derefWasm = 
    let arg = nameSym "arg" in 
    use WasmAST in 
    FunctionDef {
        ident = nameNoSym "deref",
        args = [
            {ident = arg, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            StructGet {
                structIdent = nameNoSym "anyref-box",
                field = nameNoSym "value",
                value = RefCast {
                    ty = Ref (nameNoSym "anyref-box"),
                    value = LocalGet arg
                }
            }
        ]
    }

let modrefWasm = 
    let box = nameSym "box" in 
    let val = nameSym "val" in 
    use WasmAST in 
    FunctionDef {
        ident = nameNoSym "modref",
        args = [
            {ident = box, ty = Anyref ()},
            {ident = val, ty = Anyref ()}
        ],
        locals = [],
        resultTy = Anyref (),
        instructions = [
            StructSet {
                structIdent = nameNoSym "anyref-box",
                field = nameNoSym "value",
                structValue = RefCast {
                    ty = Ref (nameNoSym "anyref-box"),
                    value = LocalGet box
                },
                fieldValue = LocalGet val
            },
            LocalGet box
        ]
    }

let printWasm = 
    let str = nameSym "str" in 
    let i = nameSym "i" in
    let n = nameSym "n" in 
    let loopIdent = nameSym "loop-ident" in 
    use WasmAST in 
        FunctionDef {
        ident = nameNoSym "print",
        args = [
            {ident = str, ty = Anyref ()}
        ],
        locals = [
            {ident = i, ty = Tyi32 ()},
            {ident = n, ty = Tyi32 ()}
        ],
        resultTy = Anyref (),
        instructions = [
            LocalSet (n, I31GetU (
                RefCast {
                    ty = I31Ref (),
                    value = (Call (nameNoSym "length", [LocalGet str]))
                }
            )),
            Loop {
                ident = loopIdent,
                body = [
                    I32Store {
                        index = LocalGet i,
                        value = I31GetU (
                            RefCast {
                                ty = I31Ref (),
                                value = (Call (nameNoSym "get", [LocalGet str, I31Cast (LocalGet i)]))
                            }
                        )
                    },
                    LocalSet (i, I32Add(LocalGet i, I32Const 1)),
                    BrIf {
                        ident = loopIdent,
                        cond = I32LtS (LocalGet i, LocalGet n)
                    }
                ]
            },
            Call (nameNoSym "callPrintJS", [LocalGet n]),
            I31Cast (LocalGet i)
        ]
    }

let float2stringWasm = 
    use WasmAST in 
    let f = nameSym "f" in 
    let n = nameSym "n" in 
    let i = nameSym "i" in
    let loopIdent = nameSym "loopIdent" in 

    let arr = nameSym "arr" in 
    FunctionDef {
        ident = nameNoSym "float2string",
        args = [
            {ident = f, ty = Anyref ()}
        ],
        locals = [
            {ident = arr, ty = Ref anyrefArrName},
            {ident = i, ty = Tyi32 ()},
            {ident = n, ty = Tyi32 ()}
        ],
        resultTy = Anyref (),
        instructions = [
            LocalSet (
                n,
                Call (
                    nameNoSym "jsFloat2String",
                    [anyref2float (LocalGet f)]    
                )
            ),
            LocalSet (
                arr,
                ArrayNew {
                    tyIdent = anyrefArrName,
                    initValue = RefNull "i31",
                    size = LocalGet n
                }    
            ),
            Loop {
                ident = loopIdent,
                body = [
                    ArraySet {
                        tyIdent = anyrefArrName,
                        value = LocalGet arr,
                        index = LocalGet i,
                        value2 = I31Cast (I32Load (LocalGet i))
                    },
                    LocalSet (i, I32Add (LocalGet i, I32Const 1)),
                    BrIf {
                        ident = loopIdent,
                        cond = I32LtS (LocalGet i, LocalGet n)
                    }
                ]
            },
            StructNew {
                structIdent = leafName,
                values = [
                    LocalGet n,
                    LocalGet arr
                ]
            }
        ]
    }


let integerIntrinsics = [
    addiWasm,
    subiWasm,
    muliWasm,
    modiWasm,
    diviWasm,
    negiWasm,
    slliWasm,
    srliWasm,
    sraiWasm,
    eqiWasm,
    neqiWasm,
    ltiWasm,
    gtiWasm,
    leqiWasm,
    geqiWasm,
    refWasm,
    derefWasm,
    modrefWasm,
    -- ,
    headWasm,
    tailWasm,
    -- lengthHelperWasm,
    lengthWasm,
    concatWasm,
    getWasm,
    consWasm,
    snocWasm,
    idWasm,
    constTrueWasm,
    arrayCopyWasm,
    flattenWasm,
    reverseWasm,
    iteriArrayWasm,
    iterArrayWasm,
    iterWasm,
    iteriWasm,
    foldlArrayWasm,
    foldrArrayWasm,
    foldlWasm,
    foldrWasm,
    printWasm,
    mapiArrayWasm,
    mapArrayWasm,
    mapWasm,
    mapiWasm,
    createWasm,
    nullWasm,
    setWasm,
    subsequenceWasm,
    splitatWasm,
    eqfWasm,
    addfWasm,
    subfWasm,
    mulfWasm, 
    divfWasm,
    neqfWasm,
    gtfWasm,
    ltfWasm,
    geqfWasm,
    leqfWasm,
    negfWasm,
    floorfiWasm,
    ceilfiWasm,
    roundfiWasm,
    int2floatWasm,
    float2stringWasm
]
