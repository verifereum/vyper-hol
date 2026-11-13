Theory exprSimAbiDecodeWidthBoundary
Ancestors
  exprSimAbiDecodeTupleAssembly exprSimAbiDecodeTupleOutcome
  abiDecoderCoherence abiDecodeRanges
  valueEncodingProps vyperTypeSystem contractABI arithmetic list

Theorem abi_decode_embedded_head_le_memory:
  abi_decoder_coherent ce env sf ty tv /\ assignable_type env ty ==>
  abi_embedded_static_size ce.ce_struct_fields ty <= type_memory_bytes ce ty
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `0 < type_slot_size tv` by
    (irule assignable_type_slot_size_pos >> metis_tac[]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  gvs[abi_member_head_size_def, type_memory_size_slots]
QED

Theorem abi_tuple_rows_head_le_memory:
  !rows. abi_tuple_rows_schema ce env rows ==>
    SUM (MAP abi_tuple_row_abi_width rows) <=
    SUM (MAP abi_tuple_row_mem_width rows)
Proof
  Induct >- simp[] >> gen_tac >> PairCases_on `h` >>
  simp_tac (srw_ss()) [abi_tuple_rows_schema_def,
    abi_tuple_row_abi_width_def, abi_tuple_row_mem_width_def] >>
  strip_tac >>
  `SUM (MAP abi_tuple_row_abi_width rows) <=
   SUM (MAP abi_tuple_row_mem_width rows)` by
    (first_x_assum irule >> simp[abi_tuple_rows_schema_def]) >>
  drule_all abi_decode_embedded_head_le_memory >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  asm_rewrite_tac [] >> decide_tac
QED
