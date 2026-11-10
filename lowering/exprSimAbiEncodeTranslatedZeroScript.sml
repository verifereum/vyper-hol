Theory exprSimAbiEncodeTranslatedZero
Ancestors
  valueEncodingDefs
  exprSimAbiEncodeEmptySource exprSimAbiEncodeSourceSupplier
  exprSimAbiEncodePlanMetadata exprSimAbiEncodeSourceMetadata
  exprLowering compileEnv vyperTypeSystem vyperValue vyperABI
  abiEncoderOpenInput abiEncoderInput abiEncoderSourceAggregate contractABI

Theorem abi_encode_translated_zero_descriptor:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  value_has_type tv v /\ vyper_to_abi E ty v = SOME av /\
  val_footprint tv v = 0 ==>
  type_to_abi_enc_info sf ce ty = AbiCopy 0 \/
  type_to_abi_enc_info sf ce ty = AbiComplex []
Proof
  strip_tac >>
  `type_memory_size tv = 0` by metis_tac[abi_encode_zero_footprint_size] >>
  `~is_dynamic (vyper_to_abi_type E ty)` by metis_tac[abi_encode_zero_size_static] >>
  drule_all abi_encode_element_metadata >> strip_tac >>
  Cases_on `ty` >>
  gvs[type_to_abi_enc_info_def] >>
  Cases_on `b` >> gvs[type_to_abi_enc_info_def, is_abi_dynamic_def] >>
  Cases_on `b'` >> gvs[type_to_abi_enc_info_def, is_abi_dynamic_def]
QED

Theorem abi_encode_translated_zero_open_bytes:
  (ei = AbiCopy 0 \/ ei = AbiComplex []) /\
  abi_encoder_open_input ei ct rv sb 0 mem ==>
  enc ct rv = []
Proof
  strip_tac >> gvs[Once abi_encoder_open_input_cases,
    abi_encoder_tuple_type_def, abi_encoder_member_span_def,
    enc_def, valueEncodingTheory.mem_bytes_at_def, listTheory.REV_DEF]
QED
