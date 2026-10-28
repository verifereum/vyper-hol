Theory sourceOrdinaryDecl
Ancestors
  sourceOrdinaryStmt sourceModuleElaborate sourceModuleDecl sourceModuleEnv
  sourceModuleDefs sourceSyntax sourceOrdinaryClaims jsonToVyperExpr vyperAST list pair

(* Signature phase resolves ORIGINAL annotations/bounds and validates source
   linkage/policies, but never infers executable function bodies. *)
Definition source_ordinary_declaration_def:
  source_ordinary_declaration fuel roots path ctx legacy slots policy original =
    source_module_bind (source_module_policy_signature fuel ctx slots policy original) (\tls.
      case (original,tls) of
        (SD_Function name decorators args defaults returns body,
         [FunctionDecl vis mut nr raw id params placeholders ret ignored]) =>
          if source_module_declaration_only policy \/ MEM (SX_Name "abstract") decorators then SM_Ok [] else
          let fctx = source_module_function_context ctx name args params;
              lctx = expr_with_local_types legacy params;
              inputs = ZIP (GENLIST I (LENGTH defaults),
                ZIP (MAP SND (DROP (LENGTH params - LENGTH defaults) params),defaults)) in
          source_module_bind (source_module_collect (MAP (\(i,(ty,e)).
            source_ordinary_expression fuel roots (path ++ [2;1;i]) ctx lctx ty e) inputs)) (\ds.
          source_module_bind (source_ordinary_statements fuel roots (path ++ [4]) 0 fctx lctx ret body)
            (\(ss,last,llast). SM_Ok [FunctionDecl vis mut nr raw id params ds ret ss]))
      | _ => SM_Ok tls)
End

Definition source_ordinary_declarations_def:
  source_ordinary_declarations fuel roots path ctx legacy slots policy syntax =
    let decls = source_module_declarations syntax in
    source_module_bind (source_module_collect (MAP (\(i,d).
      source_ordinary_declaration fuel roots (path ++ [0;i]) ctx legacy slots policy d)
        (ZIP (GENLIST I (LENGTH decls),decls)))) (\tls. SM_Ok (FLAT tls))
End
