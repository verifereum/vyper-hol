Theory entrySelectedAbiWidths
Ancestors
  entrySupportedAbiWidths entryParameterAdmissibility supportedProgram
  supportedDecls supportedTypes vyperContext vyperInterpreter vyperTypeSystem
  list finite_map pair combin

Theorem supported_fields_main_namespace[local]:
  !tops module_id name fields.
    supported_struct_fields tops (module_id,name) = SOME fields ==>
    module_id = NONE
Proof
  Cases >> simp[supported_struct_fields_def] >>
  rpt gen_tac >> Cases_on `module_id` >> simp[]
QED

Theorem type_env_struct_supported_fields:
  !tops id fields.
    FLOOKUP (type_env tops) id = SOME (StructArgs fields) ==>
    supported_struct_fields tops id = SOME fields
Proof
  simp[type_env_def] >> Induct >> rpt gen_tac
  >- simp[type_env_for_module_def] >>
  PairCases_on `id` >> Cases_on `h` >>
  simp[type_env_for_module_def, supported_struct_fields_def,
       FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[supported_fields_main_namespace]
QED

Theorem selected_external_parameter_support[local]:
  !tops tops0 name mut nr args dflts ret fbody.
    EVERY (supported_declaration_header tops0) tops /\
    lookup_function NONE name External tops =
      SOME (mut, nr, args, dflts, ret, fbody) ==>
    EVERY (supported_place_type tops0 o SND) args
Proof
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h` >>
  gvs[supported_declaration_header_def, lookup_function_def,
      supported_function_argument_def] >>
  BasicProvers.every_case_tac >>
  gvs[lookup_function_def, AllCaseEqs(), supported_function_argument_def] >>
  gvs[EVERY_MEM, o_DEF, supported_function_argument_def] >> metis_tac[]
QED

Theorem selected_external_parameter_abi_widths:
  supported_program tops /\ source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  EVERY (abi_decode_bytes_widths (type_env tops)) (MAP SND args)
Proof
  rpt strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    fs[supported_program_def, supported_declaration_headers_def] >>
  drule_all selected_external_parameter_support >>
  simp[EVERY_MEM, MEM_MAP, o_DEF] >> strip_tac >>
  rpt strip_tac >> gvs[] >> PairCases_on `y` >>
  irule supported_assignable_abi_widths >>
  conj_tac >- (drule_all selected_external_parameter_assignable >> simp[]) >>
  qexistsl [`LENGTH tops`, `tops`] >>
  simp[type_env_struct_supported_fields] >>
  gvs[supported_place_type_def] >>
  first_x_assum (qspec_then `(y0,y1)` mp_tac) >> simp[]
QED
