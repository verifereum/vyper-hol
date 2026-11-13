Theory externalReturnSupport
Ancestors
  supportedProgram supportedGetterProps vyperTypeContractGetter vyperInterpreter

Theorem return_selected_external_support:
  supported_program tops /\
  lookup_function NONE name External tops =
    SOME (mut, nr, args, dflts, ret, fbody) ==>
  ret = NoneT \/ supported_place_type tops ret
Proof
  strip_tac >> drule lookup_function_External_cases >> strip_tac
  >- (gvs[supported_program_def,
          supportedDeclsTheory.supported_declaration_headers_def,
          listTheory.EVERY_MEM] >>
      qpat_x_assum `!e. MEM e tops ==> supported_declaration_header tops e` drule >>
      simp[supportedDeclsTheory.supported_declaration_header_def,
           supportedDeclsTheory.supported_function_return_def]) >>
  `supported_declaration_header tops decl` by
    (gvs[supported_program_def,
         supportedDeclsTheory.supported_declaration_headers_def,
         listTheory.EVERY_MEM] >> metis_tac[]) >>
  metis_tac[supported_public_getter_return]
QED
