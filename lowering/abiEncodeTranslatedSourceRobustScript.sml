Theory abiEncodeTranslatedSourceRobust
Ancestors
  abiEncodeTranslatedUniformSource exprSimAbiEncodeSourceSupplier
  abiEncoderSourceRobust abiEncoderWindowSource abiEncoderLiveSource
  abiEncoderSourceAggregate abiEncoderOpenInput abiEncoderWindow bodyPtrDefs
  vyperABI vyperABIValid valueEncoding vyperValue vyperTyping
  contractABI compileEnv finite_map list arithmetic
  exprLowering abiEncoderSourceWindow loweringPosts

Theorem abi_encode_translated_source_window_robust:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  value_has_type tv v /\ vyper_to_abi E ty v = SOME av /\
  (!mem. mem_agree_outside tainted initial_mem mem ==>
    val_in_memory tv v sb mem) ==>
  ?ct rv. source_rep E ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type E ty) av /\
    LENGTH (enc ct rv) <= vyper_abi_size_bound E ty /\
    !mem. mem_agree_outside tainted initial_mem mem ==>
      abi_encoder_open_input (type_to_abi_enc_info sf ce ty) ct rv sb (type_memory_size tv) mem
Proof
  strip_tac >>
  `val_in_memory tv v sb initial_mem` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all abi_encode_translated_uniform_source >>
  disch_then (qx_choose_then `ct` strip_assume_tac) >>
  `source_rep E ty (type_to_abi_enc_info sf ce ty) ct` by
    (simp[source_rep_def] >> metis_tac[]) >>
  qpat_x_assum `!u v av sb mem0. _` drule_all >>
  disch_then (qx_choose_then `rv` strip_assume_tac) >>
  drule_all (cj 1 vyperABIValidTheory.vyper_to_abi_enc_le_size_bound) >>
  strip_tac >> qexistsl_tac [`ct`, `rv`] >> simp[]
QED

Theorem abi_encode_translated_source_footprint_robust:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  value_has_type tv v /\ vyper_to_abi E ty v = SOME av /\
  (!mem. mem_agree_outside tainted initial_mem mem ==>
    val_in_memory tv v sb mem) ==>
  ?ct rv. source_rep E ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type E ty) av /\
    LENGTH (enc ct rv) <= vyper_abi_size_bound E ty /\
    !mem. mem_agree_outside tainted initial_mem mem ==>
      abi_encoder_window_input (type_to_abi_enc_info sf ce ty) ct rv sb (val_footprint tv v) mem
Proof
  strip_tac >>
  drule_all (cj 1 vyperABIValidTheory.vyper_to_abi_enc_le_size_bound) >> strip_tac >>
  Cases_on `val_footprint tv v = type_memory_size tv`
  >- (drule_all abi_encode_translated_source_window_robust >> strip_tac >>
      qexistsl_tac [`ct`, `rv`] >> simp[] >> rpt strip_tac >>
      irule abi_encoder_open_input_window >> metis_tac[]) >>
  drule_all abi_source_non_nominal_forms >> strip_tac >> gvs[]
  >~ [`BaseT (BytesT (Dynamic n))`]
  >- (qexistsl_tac [`Bytes NONE`, `contractABI$BytesV bs`] >>
      simp[type_to_abi_enc_info_def] >> conj_tac
      >- (simp[source_rep_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
          rpt strip_tac >> qexists `av` >> simp[] >>
          irule abi_encoder_open_bytes_source >>
          qexistsl_tac [`E`, `v`] >> simp[vyper_to_abi_def]) >>
      gvs[vyper_to_abi_def, enc_def] >>
      rpt strip_tac >> simp[val_footprint_def] >>
      irule (SIMP_RULE (srw_ss()) [ADD_COMM] abi_encoder_window_bytes_source) >>
      qexistsl_tac [`E`, `BaseTV (BytesT (Dynamic n))`, `vyperValue$BytesV bs`] >>
      simp[vyper_to_abi_def] >> metis_tac[]) >>
  qexistsl_tac [`String`, `contractABI$BytesV (MAP n2w_o_ORD str)`] >>
  simp[type_to_abi_enc_info_def] >> conj_tac
  >- (simp[source_rep_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def] >>
      rpt strip_tac >> qexists `av` >> simp[] >>
      irule abi_encoder_open_string_source >>
      qexistsl_tac [`E`, `v`] >> simp[vyper_to_abi_def]) >>
  gvs[vyper_to_abi_def, enc_def] >>
  rpt strip_tac >> simp[val_footprint_def] >>
  `val_in_memory (BaseTV (StringT n)) (StringV str) sb mem` by metis_tac[] >>
  `vyper_to_abi E (BaseT (StringT n)) (StringV str) =
    SOME (contractABI$BytesV (MAP n2w_o_ORD str))` by simp[vyper_to_abi_def] >>
  drule_all abi_encoder_window_string_source >> simp[ADD_COMM]
QED
