(* Counted physical execution of the encoder parent cursor initializer. *)
Theory bodyIntCallEncoderCountedPrefix
Ancestors
  bodyIntCallDecoderCountedPrimitive abiScratchEncoderPrefix abiEncoderComplexPrefix
  abiScratchFootprint abiDecoderFootprint abiDecoderFrame abiDecoderAllocation
  abiDecoderContract fragExec fragGasPath entrySinkExtraction compileEnv
  venomState venomExecSemantics instIdxIndep list rich_list pred_set exprLoweringProps emitHelperProps

Theorem intcall_scratch_encoder_prefix_counted:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_decoder_budget first last b cap initial /\
  st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FINITE ids /\ st.cs_next_id IN ids /\ fn_has_code st st' func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution ids b cap initial actual /\
    abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap initial) initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all abi_scratch_encoder_prefix_sequence >> strip_tac >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  goal_assum (drule_at Any) >>
  fs[abi_scratch_evolution_def, abi_decode_footprint_frame_def] >>
  first_assum ACCEPT_TAC
QED
