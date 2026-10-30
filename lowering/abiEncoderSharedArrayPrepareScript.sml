(* Parent and cursor preparation through the existing prefix execution owner. *)
Theory abiEncoderSharedArrayPrepare
Ancestors
  abiEncoderSharedArrayInit abiEncoderSharedInputEffect abiEncoderSharedContract
  abiEncoderMemberPhaseRaw abiEncoderComplexPrefix abiEncoderArrayCursor
  abiEncoderMembersDefs abiEncoderSequence abiScratchEncoderPrefix abiScratchOwnedPrefix abiScratchPrefixReach
  abiScratchPrefix abiScratchFootprint abiScratchEffect abiScratchEncoderContract
  abiEncoderRegisteredEffect abiEncoderExtendSim abiDecoderAllocation abiDecoderContract
  abiDecoderReentry compileEnv venomState instIdxIndep words list arithmetic

Theorem abi_encoder_complex_prefix_raw_reach:
  abi_encode_complex_prefix (infos:(abi_enc_info # num # num # bool) list) st = (dp,prepared) /\
  abi_decoder_budget first last b cap initial /\
  first <= st.cs_next_id /\ prepared.cs_next_id <= last /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. abi_encoder_member_phase_raw st prepared initial actual /\
    abi_encoder_complex_prefix_post infos dp st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
    abi_decode_footprint_frame
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id prepared.cs_next_id) b cap initial)
      initial actual
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`] abi_scratch_encoder_prefix_sequence) >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  `abi_decode_footprint_frame
    (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id prepared.cs_next_id) b cap initial)
    initial raw` by
    (`st.cs_next_id < prepared.cs_next_id` by decide_tac >>
     drule_all abi_scratch_owned_prefix_frame >> simp[]) >>
  qexists_tac `raw with vs_inst_idx := LENGTH prepared.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def, abi_encoder_complex_prefix_post_inst_idx, abi_scratch_inst_idx] >>
  qexists_tac `raw` >> simp[]
QED

Theorem abi_encoder_shared_cursor_prepare:
  abi_encode_complex_prefix (infos:(abi_enc_info # num # num # bool) list) st = (dp,prepared) /\
  fn_has_code st prepared func /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,sz)
    (first,last,b,cap) initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ prepared.cs_next_id <= last /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_encoder_shared_input (ei,at,av) (prepared,src,dst) (sb,source_cap) (d,sz)
      (first,last,b,cap) actual /\
    abi_encoder_cursor T dp st.cs_next_id slot first st.cs_next_id prepared
      (SUM (MAP (\(_,asz,_,_). asz) infos)) actual /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d sz b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids st.cs_next_id prepared.cs_next_id) [(d,sz)] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = prepared.cs_current_bb /\ actual.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule_all abi_encoder_complex_prefix_raw_reach >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `st.cs_next_id IN abi_decoder_ids first last /\
   st.cs_next_id IN abi_decoder_ids st.cs_next_id prepared.cs_next_id` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
    limit_st d sz b cap initial actual` by
    (irule abi_scratch_prefix_effect >> simp[] >> qexistsl_tac [`dp`,`infos`] >> simp[]) >>
  drule abi_encoder_shared_input_effect >> disch_then drule >> simp[] >> disch_tac >>
  drule_all abi_scratch_prefix_cursor >> disch_then (qx_choose_then `slot` assume_tac) >>
  `abi_encoder_shared_input (ei,at,av) (prepared,src,dst) (sb,source_cap) (d,sz)
    (first,last,b,cap) actual` by
    (irule abi_encoder_shared_input_mono >> qexists_tac `st` >> simp[]) >>
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
