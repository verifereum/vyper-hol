Theory externalReturnSupport
Ancestors
  supportedProgram vyperInterpreter

(* Supported headers exclude public getters, so lookup selects a declaration. *)
Theorem return_lookup_external_decl[local]:
  !tops tops0 name mut nr args dflts ret fbody.
    EVERY (supported_declaration_header tops0) tops /\
    lookup_function NONE name External tops =
      SOME (mut, nr, args, dflts, ret, fbody) ==>
    ?raw. MEM (FunctionDecl External mut nr raw name args dflts ret fbody) tops
Proof
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `h` >> gvs[supportedDeclsTheory.supported_declaration_header_def,
                        lookup_function_def] >>
  BasicProvers.every_case_tac >> gvs[lookup_function_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem return_selected_external_support:
  supported_program tops /\
  lookup_function NONE name External tops =
    SOME (mut, nr, args, dflts, ret, fbody) ==>
  ret = NoneT \/ supported_place_type tops ret
Proof
  simp[supported_program_def,
       supportedDeclsTheory.supported_declaration_headers_def] >>
  strip_tac >>
  drule_all return_lookup_external_decl >> strip_tac >>
  gvs[listTheory.EVERY_MEM] >>
  qpat_x_assum `!e. MEM e tops ==> supported_declaration_header tops e` drule >>
  simp[supportedDeclsTheory.supported_declaration_header_def,
       supportedDeclsTheory.supported_function_return_def]
QED
