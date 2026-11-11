(* Dynamic tuple assembly does not require aggregate canonical typing. *)
Theory abiTupleEncodeOpenAssembly
Ancestors
  abiTupleEncodeAssembly abiTupleEncodeOpenMemory abiTupleEncodeLayout abiTupleProps
  abiEncoderOpenInput abiEncoderInput abiEncoderMemory abiStaticAggregateProps
  compileEnv exprLowering valueEncoding contractABI words list rich_list arithmetic pair combin

Theorem abi_tuple_encode_open_complex_input:
  abi_tuple_encode_open_memory sf ce xs ats avs d mem /\ abi_tuple_encode_layout ce xs ats ==>
  abi_encoder_open_input (AbiComplex (abi_tuple_encode_infos sf ce xs)) (Tuple ats) (ListV avs)
    d (abi_tuple_bytes ce xs) mem
Proof
  strip_tac >> drule abi_tuple_encode_open_memory_lengths >> strip_tac >>
  irule abiEncoderOpenInputTheory.complex >> simp[abi_encoder_tuple_type_def, abi_tuple_encode_infos_shape] >>
  qx_genl_tac [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] >> strip_tac >>
  `i < LENGTH xs` by fs[abi_tuple_encode_infos_shape] >>
  drule_all abi_tuple_encode_infos_el >> strip_tac >>
  drule_all abi_tuple_encode_layout_el >> strip_tac >>
  drule_all abi_tuple_encode_open_memory_el >> strip_tac >>
  gvs[abi_tuple_encode_infos_shape]
QED

Theorem abi_tuple_encode_open_dynamic_input:
  abi_tuple_encode_open_memory sf ce xs ats avs d mem /\ abi_tuple_encode_layout ce xs ats /\
  any_dynamic ats ==>
  abi_encoder_open_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs))) (Tuple ats) (ListV avs)
    d (abi_tuple_bytes ce xs) mem
Proof
  strip_tac >> drule abi_tuple_encode_layout_dynamic >> strip_tac >>
  drule_all abi_tuple_encode_open_complex_input >>
  asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def, abi_tuple_encode_infos_def,
    MAP_MAP_o, o_DEF, LAMBDA_PROD]
QED
