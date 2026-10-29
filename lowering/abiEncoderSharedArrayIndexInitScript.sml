(* Open-array index initialization through the shared prefix raw owner. *)
Theory abiEncoderSharedArrayIndexInit
Ancestors
  abiEncoderSharedArrayPrepare abiEncoderSharedArrayInit abiEncoderArrayInitCode
  abiEncoderSharedArrayInput abiEncoderSharedInputEffect abiEncoderSharedContract abiEncoderSharedArrayInitFrame
  abiEncoderMemberPhaseRaw abiEncoderComplexPrefix abiEncoderArrayCursor abiEncoderMembersDefs
  abiEncoderSequence abiScratchEncoderPrefix abiScratchOwnedPrefix abiScratchPrefixReach
  abiScratchPrefix abiScratchFootprint abiScratchEffect abiScratchEncoderContract abiScratchSubset
  abiEncoderRegisteredEffect abiEncoderExtendSim abiDecoderAllocation abiDecoderContract
  abiDecoderReentry abiDecoderFrame abiDecoderFootprint abiEncoderArrayPrefix abiEncoderOpenInput
  compileEnv venomState instIdxIndep words list arithmetic pred_set valueEncoding contractABI

Theorem abi_encoder_shared_array_index_prepare:
  abi_decode_index_init st = (ip,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (st,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ prepared.cs_next_id <= last /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
      (prepared,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual /\
    abi_encoder_array_prefix ty avs j d actual.vs_memory /\
    abi_encoder_cursor T ip st.cs_next_id slot first st.cs_next_id prepared 0 actual /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id prepared.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  strip_tac >>
  `abi_encode_complex_prefix ([]:(abi_enc_info # num # num # bool) list) st = (ip,prepared)` by
    asm_simp_tac bool_ss [GSYM abi_decode_index_init_complex_prefix] >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule_all abi_encoder_complex_prefix_raw_reach >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `st.cs_next_id IN abi_decoder_ids first last /\
   st.cs_next_id IN abi_decoder_ids st.cs_next_id prepared.cs_next_id` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual` by
    (irule abi_scratch_prefix_effect >> simp[] >>
     qexistsl_tac [`ip`,`[]:(abi_enc_info # num # num # bool) list`] >> simp[]) >>
  drule abi_encoder_shared_input_effect >> disch_then drule >> simp[] >> disch_tac >>
  drule_all abi_scratch_prefix_cursor >> disch_then (qx_choose_then `slot` assume_tac) >>
  `abi_encoder_shared_input (AbiDynArray ei asz msz active,Array NONE ty,ListV avs)
    (prepared,src,dst) (sb,source_cap) (d,sz) (first,last,b,cap) actual` by
    (irule abi_encoder_shared_input_mono >> qexists_tac `st` >> simp[]) >>
  `abi_encoder_array_prefix ty avs j d actual.vs_memory` by
    (irule abi_encoder_shared_array_prefix_scratch >> goal_assum (drule_at (Pat `abi_decode_footprint_frame _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `abi_encoder_shared_input _ _ _ _ _ _`)) >> simp[]) >>
  drule_all abi_encoder_complex_prefix_raw_registered >> strip_tac >>
  drule_all abi_encoder_complex_prefix_raw_extend >> disch_then (qspec_then `ctx` assume_tac) >>
  `actual.vs_current_bb = prepared.cs_current_bb /\
   actual.vs_inst_idx = LENGTH prepared.cs_current_insts` by
    (qpat_assum `abi_encoder_member_phase_raw _ _ _ _`
       (qx_choose_then `raw` strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_member_phase_raw_def]) >>
     drule_all abi_encoder_run_sequence_reach >>
     disch_then (qspec_then `ctx` strip_assume_tac) >> gvs[]) >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (qx_choose_then `init_slot` strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  qexistsl_tac [`actual`,`slot`] >> gvs[]
QED
