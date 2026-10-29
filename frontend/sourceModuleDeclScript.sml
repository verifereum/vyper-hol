Theory sourceModuleDecl
Ancestors
  sourceModuleSignature sourceModuleEnv sourceModuleStmt sourceModuleDefs sourceExprElaborate
  sourceTypeDefs sourceSyntax sourceConstAnnotation sourceConstAST
  vyperTypeContract vyperTypeSystem vyperAST list alist finite_map
Libs
  intLib

(* Full-Source body production extends the shared signature pass. *)
Definition source_module_body_def:
  source_module_body fuel ctx slots declaration =
    source_module_bind (source_module_signature fuel ctx slots declaration) (\tls.
      case (declaration,tls) of
        (SD_Function name decorators args defaults returns body,
          [FunctionDecl vis mut nr raw id params placeholders ret ignored]) =>
          if MEM (SX_Name "abstract") decorators then SM_Ok [] else
          let fctx = source_module_function_context ctx name args params in
          source_module_bind (source_module_collect
            (MAP (\(ty,e). source_module_expression fuel ctx ty e)
              (ZIP (MAP SND (DROP (LENGTH params - LENGTH defaults) params),defaults)))) (\ds.
          source_module_bind (source_module_statements fuel fctx ret body)
            (\(ss,last). SM_Ok [FunctionDecl vis mut nr raw id params ds ret ss]))
      | _ => SM_Ok tls)
End

Definition source_module_policy_body_def:
  source_module_policy_body fuel ctx slots policy declaration =
    source_module_bind (source_module_policy_signature fuel ctx slots policy declaration) (\tls.
      case declaration of SD_Function name decorators args defaults returns body =>
        if source_module_declaration_only policy then SM_Ok [] else
        source_module_bind (source_module_body fuel ctx slots declaration) (\bodies.
          SM_Ok (MAP (\tl. case (tls,tl) of
            ([FunctionDecl vis mut nr raw id ps ds ret ss],
             FunctionDecl bv bm bn br bi bp bd bt bs) =>
               FunctionDecl bv bm nr br bi bp bd bt bs
            | _ => tl) bodies))
      | _ => SM_Ok tls)
End

Definition source_module_policy_bodies_def:
  source_module_policy_bodies fuel ctx slots policy syntax =
    source_module_bind (source_module_collect
      (MAP (source_module_policy_body fuel ctx slots policy)
        (source_module_declarations syntax))) (\tls. SM_Ok (FLAT tls))
End

Definition source_module_bodies_def:
  source_module_bodies fuel ctx slots syntax =
    source_module_bind (source_module_collect
      (MAP (source_module_body fuel ctx slots) (source_module_declarations syntax)))
      (\tls. SM_Ok (FLAT tls))
End
