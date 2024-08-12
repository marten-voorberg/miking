include "mexpr/symbolize.mc"

lang ExtRecordSym = Sym + ExtRecordAst + ExtRecordType
  sem symbolizeType env = 
  | TyExtRec t -> 
    let ident = getSymbol {kind = "type constructor", 
                           info = [t.info],
                           allowFree = env.allowFree} env.currentEnv.tyConEnv t.ident in 
    let ty = symbolizeType env t.ty in 
    TyExtRec {t with ident = ident, ty = ty}

  sem symbolizeExpr env =
  | TmRecType t ->
    match setSymbol env.currentEnv.tyConEnv t.ident with (tyConEnv, ident) in
    let env = symbolizeUpdateTyConEnv env tyConEnv in 

    let params = map (setSymbol env.currentEnv.tyVarEnv) t.params in
    let params = map snd params in 

    TmRecType {t with ident = ident,
                      params = params,
                      inexpr = symbolizeExpr env t.inexpr}
  | TmRecField t -> 
    TmRecField {t with inexpr = symbolizeExpr env t.inexpr,
                       tyIdent = symbolizeType env t.tyIdent}
  | TmExtRecord t ->
    let ident = getSymbol {kind = "type constructor", 
                           info = [t.info],
                           allowFree = env.allowFree} env.currentEnv.tyConEnv t.ident in 
    let bindings = mapMap (symbolizeExpr env) t.bindings in 
    TmExtRecord {t with ident = ident, bindings = bindings}
  | TmExtUpdate t ->
    let ident = getSymbol {kind = "type constructor", 
                           info = [t.info],
                           allowFree = env.allowFree} env.currentEnv.tyConEnv t.ident in 
    let e = symbolizeExpr env t.e in 
    let bindings = mapMap (symbolizeExpr env) t.bindings in 
    TmExtUpdate {t with ident = ident, bindings = bindings, e = e}
  | TmExtExtend t ->
    let ident = getSymbol {kind = "type constructor", 
                           info = [t.info],
                           allowFree = env.allowFree} env.currentEnv.tyConEnv t.ident in 
    let e = symbolizeExpr env t.e in 
    let bindings = mapMap (symbolizeExpr env) t.bindings in 
    TmExtExtend {t with ident = ident, bindings = bindings, e = e}
  | TmExtProject t -> 
    let ident= getSymbol {kind = "type constructor", 
                          info = [t.info],
                          allowFree = env.allowFree} env.currentEnv.tyConEnv t.ident in 
    TmExtProject {t with ident = ident, e = symbolizeExpr env t.e}
end
