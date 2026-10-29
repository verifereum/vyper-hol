(* Extract actual body phases and their containing-function code. *)
Theory abiEncoderArrayBodyCode
Ancestors
  abiEncoderArrayCode abiEncoderArrayAddress abiEncoderAdmissible abiEncoderLeafCode
  abiEncoderChildContext abiEncoderAppend abiEncoderCounters abiEncoder
  abiDecoderContract fragExec compileEnv emitHelperProps valueEncoding venomState list arithmetic

Theorem abi_encode_array_static_body_trace:
  abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) ==>
  ?coords prepared ignored.
    abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) /\
    compile_abi_encode_static_info (SND (SND coords)) (SND (FST coords)) ei prepared = (ignored,end_st) /\
    out = FST (FST coords)
Proof
  simp_tac bool_ss [abi_encode_array_static_body_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_encode_array_addresses _ _ _ _ _ st = (coords,prepared)` >>
  rename1 `compile_abi_encode_static_info _ _ ei prepared = (ignored,end_st)` >>
  qexistsl_tac [`coords`, `prepared`, `ignored`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_static_body_context:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?coords prepared ignored.
    abi_encode_array_addresses ip src dst asz msz st = (coords,prepared) /\
    compile_abi_encode_static_info (SND (SND coords)) (SND (FST coords)) ei prepared = (ignored,end_st) /\
    out = FST (FST coords) /\ fn_has_code st prepared func /\ fn_has_code prepared end_st func /\
    prepared.cs_next_id = st.cs_next_id+7 /\ prepared.cs_next_var = st.cs_next_var+7 /\
    prepared.cs_next_id <= end_st.cs_next_id /\ prepared.cs_next_var <= end_st.cs_next_var /\
    prepared.cs_blocks = st.cs_blocks /\ end_st.cs_blocks = prepared.cs_blocks
Proof
  strip_tac >> drule abi_encode_array_static_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  qpat_assum `abi_encoder_static_leaf ei` (fn th =>
    qpat_assum `compile_abi_encode_static_info _ _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [MATCH_MP abi_encode_static_info_agrees th])) >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends st prepared` by (irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl_tac [`coords`, `prepared`, `ignored`] >> asm_simp_tac bool_ss []
QED
