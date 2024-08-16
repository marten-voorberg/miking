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
                  tyLabel : Type}
end