Theory bodyFullAbiEncodeNonwordWindow
Ancestors
  bodyFullAbiEncodeUniformTranslation abiEncoderLiveSource
  abiEncoderWindowSource abiEncoderWindow exprLowering loweringPosts
  vyperABI contractABI finite_map list

Theorem abi_encode_uniform_translated_footprint_window:
  evaluate_type E ty = SOME tv /\ E SUBMAP E0 /\
  sfields_tenv_consistent sf E /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  value_has_type tv v /\ vyper_to_abi E ty v = SOME av /\
  (!mem. mem_agree_outside tainted initial_mem mem ==> val_in_memory tv v sb mem)
  ==>
  ?ct rv. enc ct rv = enc (vyper_to_abi_type E ty) av /\
    !mem. mem_agree_outside tainted initial_mem mem ==>
      abi_encoder_window_input (type_to_abi_enc_info sf ce ty)
        ct rv sb (val_footprint tv v) mem
Proof
  strip_tac >> Cases_on `val_footprint tv v = type_memory_size tv`
  >- (drule_all abi_encode_uniform_translated_source >> strip_tac >>
      first_x_assum drule >> disch_then drule >> disch_then drule >>
      strip_tac >> qexistsl_tac [`ct`, `rv`] >> simp[] >>
      rpt strip_tac >> irule abi_encoder_open_input_window >>
      metis_tac[]) >>
  drule_all abi_source_non_nominal_forms >> strip_tac >> gvs[]
  >- (qexistsl_tac [`Bytes NONE`, `contractABI$BytesV bs`] >>
      gvs[vyper_to_abi_def] >>
      simp[type_to_abi_enc_info_def, val_footprint_def] >>
      rpt strip_tac >> irule (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM]
        abi_encoder_window_bytes_source) >>
      qexistsl_tac [`E`, `BaseTV (BytesT (Dynamic n))`, `vyperValue$BytesV bs`] >>
      simp[vyper_to_abi_def]) >>
  qexistsl_tac [`String`, `contractABI$BytesV (MAP n2w_o_ORD str)`] >>
  gvs[vyper_to_abi_def] >>
  simp[type_to_abi_enc_info_def, val_footprint_def] >>
  rpt strip_tac >>
  `val_in_memory (BaseTV (StringT n)) (StringV str) sb mem` by metis_tac[] >>
  `vyper_to_abi E (BaseT (StringT n)) (StringV str) =
     SOME (contractABI$BytesV (MAP n2w_o_ORD str))` by simp[vyper_to_abi_def] >>
  drule_all abi_encoder_window_string_source >> simp[]
QED
