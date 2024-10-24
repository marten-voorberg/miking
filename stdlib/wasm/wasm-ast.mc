include "name.mc"

lang WasmAST
    syn FloatBinOp = 
    | FloatAdd {}
    | FloatSub {}
    | FloatMul {}
    | FloatDiv {}
    | FloatEq {}
    | FloatNe {}
    | FloatGt {}
    | FloatLt {} 
    | FloatGe {}
    | FloatLe {}

    syn FloatUnOp = 
    | FloatNeg {} 
    | FloatFloor {}
    | FloatCeil {}
    | FloatConvertI32 {}
    | FloatNearest

    syn Instr =
    | I32Const Int
    | I32Store {
        index: Instr,
        value: Instr
    }
    | I32Load Instr
    | F64UnOp (FloatUnOp, Instr)
    | F64BinOp (FloatBinOp, Instr, Instr)
    | F64Const Float
    | I32Add (Instr, Instr)
    | I32Sub (Instr, Instr)
    | I32Mul (Instr, Instr)
    | I32And (Instr, Instr)
    | I32Eq (Instr, Instr)
    | I32GtS (Instr, Instr)
    | I32LtS (Instr, Instr)
    | I32GeS (Instr, Instr)
    | I32LeS (Instr, Instr)
    | I32TruncF64S Instr
    | I32Ne (Instr, Instr)
    | I32DivS (Instr, Instr)
    | I32RemS (Instr, Instr)
    | I32Shl (Instr, Instr)
    | I32ShrS (Instr, Instr)
    | I32ShrU (Instr, Instr)
    | LocalGet Name
    | LocalSet (Name, Instr)
    | GlobalGet Name
    | GlobalSet (Name, Instr)
    | RefNull String
    | Drop Instr
    | Call (Name, [Instr])
    | Unreachable ()
    | Loop {
        ident: Name,
        body: [Instr]
    }
    | BrIf {
        ident: Name,
        cond: Instr
    }
    | StructGet {
        structIdent: Name,
        field: Name,
        value: Instr
    }
    | StructSet {
        structIdent: Name,
        field: Name,
        structValue: Instr,
        fieldValue : Instr
    }
    | StructNew {
        structIdent: Name,
        values: [Instr]
    }
    | ArrayNew {
        tyIdent: Name,
        initValue: Instr,
        size: Instr
    }
    | ArrayGet {
        tyIdent: Name,
        value: Instr,
        index: Instr
    }
    | ArraySet {
        tyIdent: Name,
        value: Instr,
        index: Instr,
        value2: Instr
    }
    | RefCast {
        ty: WasmType,
        value: Instr
    }
    | RefTest {
        ty: WasmType,
        value: Instr
    }
    | CallIndirect {
        ty: Name,
        args: [Instr],
        fp: Instr
    }
    | IfThenElse {
        cond: Instr,
        thn: [Instr],
        els: [Instr]
    }
    | Select {
        cond: Instr,
        thn: Instr,
        els: Instr
    }
    | Return Instr
    | I31Cast Instr
    | I31GetS Instr
    | I31GetU Instr

    syn Def = 
    | FunctionDef {
        ident: Name,
        args: [{ident: Name, ty: WasmType}],
        locals: [{ident: Name, ty: WasmType}],
        resultTy: WasmType,
        instructions: [Instr]
    }
    | StructTypeDef {
        ident: Name,
        fields: [{
            ident: Name,
            ty: WasmType
        }]
    }
    | FunctionTypeDef {
        ident: Name,
        paramTys: [WasmType],
        resultTy: WasmType
    }
    | ArrayTypeDef {
        ident: Name,
        paramTys: [WasmType]
    }
    | GlobalDef {
        ident: Name,
        ty: WasmType, 
        initValue: Instr
    }

    syn WasmType = 
    | Tyi32 ()
    | Tyi64 ()
    | Tyf32 ()
    | Tyf64 ()
    | Array WasmType
    | Anyref ()
    | Ref Name
    | I31Ref ()
    | Mut WasmType

    syn WasmMemory = 
    | Table {size: Int, typeString: String}
    | Elem {offset: Instr, funcNames: [Name]}
    | Memory {n: Int}

    syn WasmExport = 
    | FunctionExport {ident: Name}
    | MemoryExport {ident: Name, n: Int}

    syn Mod = 
    | Module {
        definitions: [Def],
        memory: WasmMemory,
        table: WasmMemory, 
        elem: WasmMemory, 
        types: [WasmType],
        imports: [{
            jsObjIdent: String,
            jsFieldIdent: String,
            wasmIdent: Name,
            paramTys: [WasmType],
            resultTy: Option WasmType
        }],
        exports: [WasmExport]
    }
end


mexpr 
use WasmAST in 
utest I32Const 10 with I32Const 10 in
utest I32Add (I32Const 10, I32Const 1) with I32Add (I32Const 10, I32Const 1) in
()