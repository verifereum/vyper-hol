Theory entryParameterAdmissibility
Ancestors
  list finite_map e2eDefs vyperLoweringCorrect supportedProgram supportedDecls
  vyperTypeContract vyperTypeContractContext vyperInterpreter vyperContext
  vyperAST entryStateRel

Theorem selected_external_params_ok:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, nr, args, [], ret, fbody) ==>
  params_ok (type_env tops) args
Proof
  rpt strip_tac >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all source_typing_ok_params_ok >> simp[]
QED

Theorem selected_external_parameter_assignable:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut, nr, args, [], ret, fbody) /\
  MEM (name, ty) args ==>
  assignable_type (type_env tops) ty
Proof
  strip_tac >> drule_all selected_external_params_ok >>
  simp[params_ok_def, EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `(name,ty)` mp_tac) >> simp[]
QED
