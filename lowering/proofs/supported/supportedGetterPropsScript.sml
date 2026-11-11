(* Supported bodies and parameter types for the selected external entry,
   including synthesized getters of admitted public declarations. *)
Theory supportedGetterProps
Ancestors
  supportedProgram supportedDecls supportedExprForms supportedExprs
  supportedNames supportedTypes supportedStmts supportedStmtTraverse
  e2eDefs vyperTypeContractGetter vyperTypeContractContext
  compileEnv exprLowering vyperGetter vyperInterpreter list pair finite_map

(* Visibility changes getter generation; ordinary source lookup uses the
   visibility-independent find_var_decl_by_name. A getter is a Return of a
   top-level read or a subscript chain, with distinct generated argument names. *)
Theorem supported_selected_external_body:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  supported_function_body tops External args fbody /\
  EVERY (supported_place_type tops) (MAP SND args) /\
  (ret = NoneT \/ supported_place_type tops ret)
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (drule_all supported_program_function >>
      gvs[supported_program_def, supported_declaration_headers_def, EVERY_MEM] >>
      first_x_assum drule >>
      simp[supported_declaration_header_def, supported_function_argument_def,
           supported_function_return_def, EVERY_MAP]) >>
  gvs[supported_program_def, supported_declaration_headers_def, EVERY_MEM] >>
  first_x_assum drule >>
  Cases_on `decl` >>
  gvs[supported_declaration_header_def, is_public_getter_decl_def,
      external_getter_tuple_def] >>
  metis_tac[]
QED
