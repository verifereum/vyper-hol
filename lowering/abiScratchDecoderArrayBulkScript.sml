(* Static-element bulk copying uses a validity-derived readable prefix and no scratch allocation. *)
Theory abiScratchDecoderArrayBulk
Ancestors
  vyperABIValid abiScratchDecoderContract abiScratchDecoderRanges abiScratchEncoderContract
  abiScratchLeafEffect abiDecoderValidContract abiDecoderCorrectPrimitiveArray
  abiDecoderBulkReentry abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry abiDecoderLoop abiDecoderFrame abiDecodeRanges
  abiValidStatic abiEncoder fragExec exprLowering compileEnv valueEncoding vyperABI vyperValue
  contractABI venomState venomExecSemantics words list arithmetic

Theorem abi_scratch_decoder_static_array_pre:
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs v st src dst opc hi sb d first last b cap s /\
  abi_decoder_budget first last b cap s /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)))
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) v st st.cs_next_id src dst opc hi sb d
    s.vs_alloca_next 0 (abi_decoder_prune_vars st.cs_next_var s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  `abi_decoder_reservation st.cs_next_id st.cs_next_id s.vs_alloca_next 0 s` by
    (mp_tac abi_scratch_decoder_point_reservation >> asm_simp_tac bool_ss []) >>
  `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs` by
    fs[abi_scratch_decoder_input_def, Once vyper_to_abi_type_def,
      Excl "vyper_decode_valid_enc_def", Excl "dec_def", Excl "enc_def"] >>
  `valid_enc (Array NONE (vyper_to_abi_type env ty)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc (Array NONE _) bs` mp_tac >>
     simp_tac bool_ss [Once vyper_decode_valid_enc_def, Once valid_enc_def, LET_THM] >>
     strip_tac >> gvs[] >>
     irule (cj 2 vyper_decode_valid_enc_static_mutual) >> simp[]) >>
  drule_all abi_valid_static_array_prefix >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [Once vyper_to_abi_type_def] (Q.INST
    [`ty` |-> `ArrayT ty (Dynamic maxn)`, `tv` |-> `ArrayTV tv (Dynamic maxn)`,
     `last` |-> `st.cs_next_id`, `b` |-> `s.vs_alloca_next`, `cap` |-> `0:num`]
    abi_decoder_valid_pre_prefix)) >> asm_simp_tac bool_ss [vyper_to_abi_type_def]
QED

Theorem abi_scratch_decoder_array_bulk:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) F maxn) st = ((),end_st) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\ ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  fn_has_code st end_st func /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by
    fs[abi_scratch_decoder_input_def, abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
  drule_all abi_scratch_decoder_static_array_pre >> strip_tac >>
  qhdtm_x_assum `abi_scratch_decoder_input`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [Once vyper_to_abi_type_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  (qpat_assum `~is_abi_dynamic ce.ce_struct_fields ty` (fn static =>
    qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def, static])) >>
  drule_all (Q.INST [`st'` |-> `end_st`, `b` |-> `initial.vs_alloca_next`, `cap` |-> `0:num`,
    `last` |-> `st.cs_next_id`] abi_decoder_bulk_reentry_from_state) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual` by
    (irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED
