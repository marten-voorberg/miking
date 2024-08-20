include "mlang/ast.mc"

include "mexpr/ast.mc"

include "name.mc"

lang RecTypeDeclAst = DeclAst 
  syn Decl = 
  | RecTypeDecl {info : Info, 
                 ident : Name,
                 params : [Name]}
end

lang RecFieldDeclAst = DeclAst + Ast
  syn Decl = 
  | RecFieldDecl {info : Info,
                  label : String,
                  extIdent : Name,
                  tyLabel : Type}
end

lang ExtRecordAst = Ast
  syn Expr = 
  | TmRecType {ident : Name,
               params : [Name],
               ty : Type,
               inexpr : Expr, 
               info : Info}
  | TmRecField {label : String, 
                tyIdent : Type, 
                extIdent : Name,
                inexpr : Expr,
                ty : Type,
                info : Info}
  | TmExtRecord  {bindings : Map String Expr, 
                  ident : Name,
                  ty : Type,
                  info : Info}
  | TmExtProject {e : Expr,
                  ident : Name,
                  label : String,
                  ty : Type,
                  info : Info}
  | TmExtUpdate {e : Expr, 
                 ident : Name, 
                 bindings : Map String Expr,
                 ty : Type,
                 info : Info}
  | TmExtExtend {e : Expr, 
                 ident : Name, 
                 bindings : Map String Expr,
                 ty : Type,
                 info : Info}
  
  sem infoTm =
  | TmRecField t -> t.info
  | TmRecType t -> t.info
  | TmExtRecord t -> t.info
  | TmExtProject t -> t.info
  | TmExtUpdate t -> t.info
  | TmExtExtend t -> t.info

  sem tyTm =
  | TmRecField t -> t.ty
  | TmRecType t -> t.ty
  | TmExtRecord t -> t.ty
  | TmExtProject t -> t.ty
  | TmExtUpdate t -> t.ty 
  | TmExtExtend t -> t.ty 

  sem withInfo info =
  | TmRecField t -> TmRecField {t with info = info}
  | TmRecType t -> TmRecType {t with info = info}
  | TmExtRecord t -> TmExtRecord {t with info = info}
  | TmExtProject t -> TmExtProject {t with info = info}
  | TmExtExtend t -> TmExtExtend {t with info = info}
  | TmExtUpdate t -> TmExtUpdate {t with info = info}

  sem withType  ty =
  | TmRecField t -> TmRecField {t with ty = ty}
  | TmRecType t -> TmRecType {t with ty = ty}
  | TmExtRecord t -> TmExtRecord {t with ty = ty}
  | TmExtProject t -> TmExtProject {t with ty = ty}
  | TmExtExtend t -> TmExtExtend {t with ty = ty}
  | TmExtUpdate t -> TmExtUpdate {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmRecType t ->
    match f acc t.inexpr with (acc, inexpr) in 
    (acc, TmRecType {t with inexpr = inexpr})
  | TmRecField t ->
    match f acc t.inexpr with (acc, inexpr) in 
    (acc, TmRecField {t with inexpr = inexpr})
  | TmExtRecord t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.bindings with (acc, bindings) in
    (acc, TmExtRecord {t with bindings = bindings})
  | TmExtProject t -> 
    match smapAccumL_Expr_Expr f acc t.e with (acc, e) in 
    (acc, TmExtProject {t with e = e})
  | TmExtExtend t -> 
    match f acc t.e with (acc, e) in 
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.bindings 
    with (acc, bindings) in
    (acc, TmExtExtend {t with e = e, bindings = bindings})
  | TmExtUpdate t -> 
    match f acc t.e with (acc, e) in 
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.bindings 
    with (acc, bindings) in
    (acc, TmExtUpdate {t with e = e, bindings = bindings})

  sem smapAccumL_Expr_Type f acc = 
  | TmRecType t ->
    match f acc t.ty with (acc, ty) in
    (acc, TmRecType {t with ty = ty})
  | TmRecField t -> 
    match f acc t.tyIdent with (acc, tyIdent) in 
    match f acc t.ty with (acc, ty) in 
    (acc, TmRecField {t with tyIdent = tyIdent,
                             ty = ty})
  | TmExtRecord t ->
    match f acc t.ty with (acc, ty) in 
    (acc, TmExtRecord {t with ty = ty}) 
  | TmExtProject t ->
    match f acc t.ty with (acc, ty) in 
    (acc, TmExtProject {t with ty = ty}) 
  | TmExtUpdate t ->
    match f acc t.ty with (acc, ty) in 
    (acc, TmExtUpdate {t with ty = ty}) 
  | TmExtExtend t ->
    match f acc t.ty with (acc, ty) in 
    (acc, TmExtExtend {t with ty = ty}) 
end

lang ExtRecordTypeAst = Ast 
  syn Type = 
  | TyAbsent ()
  | TyPre ()
  | TyExtRec {info : Info, 
              ident : Name,
              ty : Type}
  | TyExtensionRow {row : Map Name Type}

  sem tyWithInfo info = 
  | t & (TyAbsent _ | TyPre _ | TyExtensionRow _) -> t
  | TyExtRec t -> TyExtRec {t with info = info}

  sem smapAccumL_Type_Type f acc =
  | TyExtensionRow t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.row with (acc, row) in
    (acc, TyExtensionRow {t with row = row})
  | TyExtRec t -> 
    match f acc t.ty with (acc, ty) in 
    (acc, TyExtRec {t with ty = ty})
end

lang PresenceKindAst = Ast
  syn Kind = 
  | Presence ()
end

lang ExtensionRowKindAst = Ast 
  syn Kind = 
  | ExtensionRow ()
end

lang TypeAbsAst = Ast 
  syn Type = 
  | TyAbs {ident : Name,
           kind : Kind,
           body : Type}

  sem tyWithInfo info = 
  | TyAbs _ & t -> t

  sem smapAccumL_Type_Type f acc = 
  | TyAbs t ->
    match f acc t.body with (acc, body) in 
    (acc, TyAbs {t with body = body})
end

lang TypeAbsAppAst = Ast
  syn Type =
  | TyAbsApp {lhs : Type,
              rhs : Type}

  sem tyWithInfo info = 
  | TyAbsApp _ & t -> t

  sem smapAccumL_Type_Type f acc = 
  | TyAbsApp t ->
    match f acc t.lhs with (acc, lhs) in 
    match f acc t.rhs with (acc, rhs) in 
    (acc, TyAbsApp {t with lhs = lhs, rhs = rhs})
end