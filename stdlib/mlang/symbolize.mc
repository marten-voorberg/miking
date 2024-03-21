include "ast.mc"
include "bool.mc"
include "map.mc"
include "name.mc"
include "../mexpr/symbolize.mc"
include "mlang/pprint.mc"


lang MLangSym = MLangAst + MExprSym 
    sem symbolizeMLang : SymEnv -> MLangProgram -> (SymEnv, MLangProgram)
    sem symbolizeMLang env =| prog -> 
        match mapAccumL symbolizeDecl env prog.decls with (env, decls) in
        let expr = symbolizeExpr env prog.expr in 
        (env, {
            decls = decls,
            expr = expr
        })

    sem symbolizeExpr env = 
    | TmUse t -> 
        match mapLookup (nameGetStr t.ident) env.langEnv with Some langEnv 
            then 
                let env = {env with currentEnv = mergeNameEnv env.currentEnv langEnv.allNames} in 
                let inexpr = symbolizeExpr env t.inexpr in 
                TmUse {t with ident = langEnv.ident,
                              inexpr = inexpr}
            else 
                symLookupError 
                    {kind = "language", info = [t.info], allowFree = false}
                    t.ident

    sem symbolizeDecl : SymEnv -> Decl -> (SymEnv, Decl)
    sem symbolizeDecl env = 
    | DeclInclude r ->
        error "Symbolization expects all DeclInclude to have been removed!"
    | DeclLet t ->  
        match symbolizeTyAnnot env t.tyAnnot with (tyVarEnv, tyAnnot) in
        match setSymbol env.currentEnv.varEnv t.ident with (varEnv, ident) in
        let env = updateVarEnv env varEnv in 
        let decl = DeclLet {t with ident = ident,
                            tyAnnot = tyAnnot,
                            body = symbolizeExpr env t.body} in 
        (env, decl)
    | DeclType t -> 
        match setSymbol env.currentEnv.tyConEnv t.ident with (tyConEnv, ident) in
        match mapAccumL setSymbol env.currentEnv.tyVarEnv t.params with (tyVarEnv, params) in
        let decl = DeclType {t with ident = ident,
                             params = params,
                             tyIdent = symbolizeType (updateTyVarEnv env tyVarEnv) t.tyIdent} in 
        let env = updateTyConEnv env tyConEnv in 
        (env, decl)
    | DeclRecLets t -> 
        -- Generate fresh symbols for all identifiers and add to the environment
        let setSymbolIdent = lam env. lam b.
            match setSymbol env b.ident with (env, ident) in
            (env, {b with ident = ident})
        in

        match mapAccumL setSymbolIdent env.currentEnv.varEnv t.bindings with (varEnv, bindings) in
        let newEnv = updateVarEnv env varEnv in

        -- Symbolize all bodies with the new environment
        let bindings =
        map (lam b. match symbolizeTyAnnot env b.tyAnnot with (tyVarEnv, tyAnnot) in
                    {b with body = symbolizeExpr (updateTyVarEnv newEnv tyVarEnv) b.body,
                            tyAnnot = tyAnnot})  bindings in

        (newEnv, DeclRecLets {t with bindings = bindings})
    | DeclConDef t -> 
        match setSymbol env.currentEnv.conEnv t.ident with (conEnv, ident) in

        let decl = DeclConDef {t with ident = ident,
                                      tyIdent = symbolizeType env t.tyIdent} in 
        let env = updateConEnv env conEnv in 
        (env, decl)
    | DeclUtest t -> 
        -- This can be rewritten to use a shallow map on declarations. E.g.
        -- smap (symbolizeExpr env) (DeclUtest t) 
        let decl = DeclUtest {t with test = symbolizeExpr env t.test,
                                     expected = symbolizeExpr env t.expected,
                                     tusing = optionMap (symbolizeExpr env) t.tusing} in 
        (env, decl)
    | DeclExt t -> 
        -- When ignoreExternals is set, the DeclExt should have been filtered
        -- out of the program before attempting to symbolize the declarations.
        if env.ignoreExternals then
            error "DeclExt should have been removed when 'ignoreExternals' is true!"
        else 
            match setSymbol env.currentEnv.varEnv t.ident with (varEnv, ident) in
            let decl = DeclExt {t with ident = ident,
                                       tyIdent = symbolizeType env t.tyIdent} in 
            let env = updateVarEnv env varEnv in 
            (env, decl)
    | DeclLang t -> 
        -- Todo: Fix use of nameGetStr
        let ident = nameSym (nameGetStr t.ident) in 
        let t = {t with ident = ident} in 
        let langEnv = _langEnvEmpty ident in 

        let isSynDecl = lam d. match d with DeclSyn _ then true else false in 
        let synDecls = filter isSynDecl t.decls in 

        let isSemDecl = lam d. match d with DeclSem _ then true else false in 
        let semDecls = filter isSemDecl t.decls in 

        let isTypeDecl = lam d. match d with DeclType _ then true else false in 
        let typeDecls = filter isTypeDecl t.decls in 

        let symbIncludes = lam langEnvs : [LangEnv]. lam n : Name. 
            match mapLookup (nameGetStr n) env.langEnv with Some langEnv then 
                ((cons langEnv langEnvs), langEnv.ident)
            else 
                symLookupError 
                    {kind = "language", info = [t.info], allowFree = false}
                    t.ident
        in
        match mapAccumL symbIncludes [] t.includes with (includedLangEnvs, includes) in 

        let findSemIncludes : Name -> [Name] = lam n. 
            let varEnvs = map (lam langEnv. langEnv.extensibleNames.varEnv) includedLangEnvs in 
            mapOption (mapLookup (nameGetStr n)) varEnvs
        in
        -- let includedLangEnvs : [LangEnv] = 

        -- 1. Symbolize ident and params of SynDecls
        let symSynIdentParams = lam langEnv : LangEnv. lam synDecl.
            let env = {env with currentEnv = mergeNameEnv env.currentEnv langEnv.allNames} in 
            match synDecl with DeclSyn s in

            -- Since syn definitions are extensible, we add information to both
            -- allNames and extensibleNames
            match setSymbol langEnv.allNames.tyConEnv s.ident with (allTyConEnv, ident) in
            -- We update the ident on 's' so 'setSymbol' does not assign a new symbol.
            let s = {s with ident = ident} in
            match setSymbol langEnv.extensibleNames.tyConEnv s.ident with (extensibleTyConEnv, ident) in
            let allNames = {langEnv.allNames with tyConEnv = allTyConEnv} in
            let extensible = {langEnv.extensibleNames with tyConEnv = extensibleTyConEnv} in
            let langEnv = {langEnv with allNames = allNames,
                                        extensibleNames = extensible} in

            match mapAccumL setSymbol env.currentEnv.tyVarEnv s.params with (_, params) in
            let s = {s with params = params} in

            (langEnv, DeclSyn s)
        in
        match mapAccumL symSynIdentParams langEnv synDecls with (langEnv, synDecls) in 

        -- 2. Symbolize DeclType and params
        let symbDeclType = lam langEnv : LangEnv. lam typeDecl. 
            let env = {env with currentEnv = mergeNameEnv env.currentEnv langEnv.allNames} in 
            match typeDecl with DeclType t in 
            
            match setSymbol langEnv.allNames.tyConEnv t.ident with (allTyConEnv, ident) in
            match mapAccumL setSymbol env.currentEnv.tyVarEnv t.params with (_, params) in

            let allNames = {langEnv.allNames with tyConEnv = allTyConEnv} in
            let langEnv = {langEnv with allNames = allNames} in 

            let t = {t with ident = ident,
                            params = params} in 
            
            (langEnv, DeclType t)
        in 
        match mapAccumL symbDeclType langEnv typeDecls with (langEnv, typeDecls) in 

        -- 3. Symbolize syntax constructors (add defs to conEnv)
        let symbDef = lam langEnv : LangEnv. lam def : {ident : Name, tyIdent : Type}. 
            match setSymbol langEnv.allNames.conEnv def.ident with (allConEnv, ident) in 
            match setSymbol langEnv.extensibleNames.conEnv def.ident with (extensibleConEnv, ident) in 

            let allNames : NameEnv = {langEnv.allNames with conEnv = allConEnv} in
            let extensible : NameEnv = {langEnv.extensibleNames with conEnv = extensibleConEnv} in
            let langEnv : LangEnv = {langEnv with allNames = allNames,
                                                  extensibleNames = extensible} in

            let env = {env with currentEnv = mergeNameEnv env.currentEnv langEnv.allNames} in
            let tyIdent = symbolizeType env def.tyIdent in

            (langEnv, {ident = ident, tyIdent = tyIdent})
        in
        let symbSynConstructors = lam langEnv. lam synDecl. 
            match synDecl with DeclSyn s in 
            match mapAccumL symbDef langEnv s.defs with (langEnv, defs) in 
            let s = {s with defs = defs} in 
            (langEnv, DeclSyn s)
        in 
        match mapAccumL symbSynConstructors langEnv synDecls with (langEnv, synDecls) in 

        -- 4. Assign names to semantic functions
        let symbSem = lam langEnv : LangEnv. lam declSem. 
            match declSem with DeclSem s in 
            match setSymbol langEnv.allNames.varEnv s.ident with (allVarEnv, ident) in 
            match setSymbol langEnv.extensibleNames.varEnv ident with (extensibleVarEnv, ident) in 
            
            let allNames : NameEnv = {langEnv.allNames with varEnv = allVarEnv} in
            let extensible : NameEnv = {langEnv.extensibleNames with varEnv = extensibleVarEnv} in
            let langEnv : LangEnv = {langEnv with allNames = allNames,
                                                  extensibleNames = extensible} in

            let env = {env with currentEnv = mergeNameEnv env.currentEnv langEnv.allNames} in

            let tyAnnot = symbolizeType env s.tyAnnot in 
            let tyBody = symbolizeType env s.tyBody in 

            let includes : [Name] = findSemIncludes ident in

            let s = {s with ident = ident,
                            tyAnnot = tyAnnot,
                            tyBody = tyBody} in 
            
            -- let s = {s with ident = ident,
            --                 tyAnnot = tyAnnot,
            --                 tyBody = tyBody,
            --                 includes = includes} in 

            (langEnv, DeclSem s)
        in 
        match mapAccumL symbSem langEnv semDecls with (langEnv, semDecls) in 

        -- 5. Assign names to semantic bodies.
        let symbSem2 = lam langEnv : LangEnv. lam declSem. 
            match declSem with DeclSem s in 

            let env = {env with currentEnv = mergeNameEnv env.currentEnv langEnv.allNames} in
            
            let symbArg = lam env : SymEnv. lam arg : {ident : Name, tyAnnot : Type}. 
                match setSymbol env.currentEnv.varEnv arg.ident with (varEnv, ident) in 
                let env = updateVarEnv env varEnv in 
                let tyAnnot = symbolizeType env arg.tyAnnot in 
                (env, {ident = ident, tyAnnot = tyAnnot})
            in
            
            match mapAccumL symbArg env s.args with (env, args) in 

            let symbCases = lam cas : {pat : Pat, thn : Expr}. 
                match symbolizePat env (mapEmpty cmpString) cas.pat with (thnVarEnv, pat) in
                let thn = symbolizeExpr (updateVarEnv env thnVarEnv) cas.thn in
                {pat = pat, thn = thn}
            in

            let cases = map symbCases s.cases in

            DeclSem {s with args = args,
                            cases = cases}
        in
        let semDecls = map (symbSem2 langEnv) semDecls in 

        let env = {env with langEnv = mapInsert (nameGetStr t.ident) langEnv env.langEnv} in 
        let t = {t with decls = join [typeDecls, synDecls, semDecls]} in
        (env, DeclLang t)
end

-- let _and = lam cond. lam f. lam. if cond () then f () else false
-- let _andFold = lam f. lam acc. lam e. _and acc (f e)

lang TestLang = MLangSym + SymCheck + MLangPrettyPrint
    sem isFullySymbolizedExpr = 
    | TmUse t -> 
        _and (lam. nameHasSym t.ident) (isFullySymbolizedExpr t.inexpr)

    sem isFullySymbolizedDecl : Decl -> () -> Bool
    sem isFullySymbolizedDecl =
    | DeclLang l -> 
        _and (lam. nameHasSym l.ident) (_and 
            (lam. forAll nameHasSym l.includes)
            (foldl (_andFold isFullySymbolizedDecl) (lam. true) l.decls)
        )
    | DeclSyn l -> 
        _and (lam. nameHasSym l.ident) (_and 
            (lam. (forAll nameHasSym l.params))
            (lam. (forAll nameHasSym (map (lam d. d.ident) l.defs)))
        )
    | DeclSem l -> 
        let argIdents = map (lam a. a.ident) l.args in 
        let argTys = map (lam a. a.tyAnnot) l.args in 
        let casePats = map (lam c. c.pat) l.cases in 
        let caseThns = map (lam c. c.thn) l.cases in 

        foldl _and (lam. true) [
            lam. nameHasSym l.ident,
            isFullySymbolizedType l.tyAnnot,
            isFullySymbolizedType l.tyBody,
            lam. forAll nameHasSym argIdents,
            foldl (_andFold isFullySymbolizedType) (lam. true) argTys,
            foldl (_andFold isFullySymbolizedPat) (lam. true) casePats, 
            foldl (_andFold isFullySymbolizedExpr) (lam. true) caseThns
        ]
    | DeclType l -> 
        _and (lam. nameHasSym l.ident) (_and 
             (lam. (forAll nameHasSym l.params))
             (isFullySymbolizedType l.tyIdent))
        
end

let synDeclIdentHasSymbolized = lam decl. 
    use MLangAst in 
    match decl with DeclSyn t then
        (if nameHasSym t.ident then
            ()
        else error (join [
            "SynDecl '",
            nameGetStr t.ident,
            "' has not been symbolized!"
        ])) ;
        let defHasName = lam def : {ident : Name, tyIdent : Type}. 
            if nameHasSym def.ident then
                ()
            else error (join [
                "Syntax constructor '",
                nameGetStr def.ident,
                "' has not been symbolized!"
            ])
        in 
        iter defHasName t.defs
    else 
        ()
    

let typeDeclIdentHasSymbolized = lam decl. 
    use MLangAst in 
    -- Check syn ident has been symbolized
    match decl with DeclType t then
        if nameHasSym t.ident then
            ()
        else error (join [
            "TypeDecl '",
            nameGetStr t.ident,
            "' has not been symbolized!"
        ])
    else 
        ()

let semDeclIdentHasSymbolized = lam decl. 
    use MLangAst in 
    -- Check syn ident has been symbolized
    match decl with DeclSem t then
        if nameHasSym t.ident then
            ()
        else error (join [
            "SemDecl '",
            nameGetStr t.ident,
            "' has not been symbolized!"
        ])
    else 
        ()


mexpr
use TestLang in 
let p : MLangProgram = {
    decls = [
        decl_lang_ "L1" [
            decl_syn_ "Foo" [("Baz", tyint_), ("BazBaz", tychar_)],
            decl_type_ "Bar" [] tyint_,
            decl_sem_ "f" [] []
        ]
    ],
    expr = bind_ (use_ "L1") (var_ "f")
} in 
match symbolizeMLang symEnvDefault p with (_, p) in 
let l1 = head p.decls in 
match l1 with DeclLang l in 
utest isFullySymbolizedDecl l1 () with true in 
utest isFullySymbolized p.expr with true in 
utest nameHasSym l.ident with true in
iter typeDeclIdentHasSymbolized l.decls ;
iter synDeclIdentHasSymbolized l.decls ;
iter semDeclIdentHasSymbolized l.decls ;
()