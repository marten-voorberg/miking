include "ast.mc"
include "result.mc"

include "mlang/compile.mc"
include "mexpr/ast.mc"

lang RecTypeDeclCompiler = RecTypeDeclAst + DeclCompiler + ExtRecordAst
  sem compileDecl ctx = 
  | RecTypeDecl d ->
    result.ok (withExpr ctx (TmRecType {ident = d.ident,
                                  params = d.params,
                                  ty = tyunknown_,
                                  inexpr = uunit_, 
                                  info = d.info}))
end

lang RecFieldDeclCompiler = RecFieldDeclAst + DeclCompiler + ExtRecordAst
  sem compileDecl ctx = 
  | RecFieldDecl d ->
    result.ok (withExpr ctx (TmRecField {label = d.label,
                                         tyIdent = d.tyLabel,
                                         extIdent = d.extIdent,
                                         ty = tyunknown_,
                                         inexpr = uunit_, 
                                         info = d.info}))
end