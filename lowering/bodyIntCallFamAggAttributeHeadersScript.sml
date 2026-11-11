(* Named-struct support from declaration headers. *)
Theory bodyIntCallFamAggAttributeHeaders
Ancestors
  bodyIntCallFamAggAttributeSaturation supportedDecls typedCopyMetadata
  supportedTypes list option

Theorem supported_struct_fields_header:
  supported_declaration_headers tops /\
  supported_struct_fields tops id = SOME fields ==>
  EVERY (supported_place_type tops o SND) fields
Proof
  PairCases_on `id` >> strip_tac >>
  `id0 = NONE` by metis_tac[supported_struct_fields_other_module, NOT_SOME_NONE] >>
  gvs[] >> drule supported_struct_fields_origin >> strip_tac >>
  gvs[supported_declaration_headers_def, EVERY_MEM] >>
  first_x_assum drule >> simp[supported_declaration_header_def, EVERY_MEM]
QED

Theorem supported_struct_fields_header_nonempty:
  supported_declaration_headers tops /\
  supported_struct_fields tops id = SOME fields ==>
  ~NULL fields
Proof
  PairCases_on `id` >> strip_tac >>
  `id0 = NONE` by metis_tac[supported_struct_fields_other_module, NOT_SOME_NONE] >>
  gvs[] >> drule supported_struct_fields_origin >> strip_tac >>
  gvs[supported_declaration_headers_def, EVERY_MEM] >>
  first_x_assum drule >> simp[supported_declaration_header_def]
QED

Theorem supported_place_struct_header:
  supported_declaration_headers tops /\
  supported_struct_fields tops id = SOME fields ==>
  supported_place_type tops (StructT id)
Proof
  strip_tac >> drule_all supported_struct_fields_header >> strip_tac >>
  drule_all supported_struct_fields_header_nonempty >> strip_tac >>
  simp[supported_place_type_def] >>
  irule supported_nested_type_saturated >>
  qexists `SUC (LENGTH tops)` >>
  once_rewrite_tac[supported_nested_type_def] >>
  gvs[EVERY_MEM, supported_place_type_def]
QED
