(* Re-enter the actual singleton prefix with an arbitrary decoded offset. *)
Theory abiValidSingletonReentry
Ancestors
  abiValidSingletonSetup abiValidSingletonCode abiDecoderSingletonSetup abiDecoderReentryPrefix
  abiDecoderReentrySequence abiDecoderReentry abiDecoderVarExtend abiDecoderDynamicLoopSetup
  abiDecoderReservation abiDecoderContract abiEncoderSequence fragExec instIdxIndep compileEnv
  emitHelper emitHelperProps exprLoweringProps venomExecSemantics venomState words list pair

Theorem abi_valid_singleton_setup_reentry:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_valid_singleton_setup_pre st src dst opc hi sb d offset
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand child_src actual = SOME (n2w (sb + offset)) /\
    eval_operand child_dst actual = SOME (n2w d) /\
    abi_decoder_operand_live st'.cs_next_var child_src /\
    abi_decoder_operand_live st'.cs_next_var child_dst /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\ inst_extends st st'
Proof
  strip_tac >> drule_all abi_valid_singleton_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  `abi_decode_source_opcode opc` by fs[abi_valid_singleton_setup_pre_def] >>
  drule_all abi_valid_singleton_setup_code >> strip_tac >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  drule abi_valid_singleton_setup_live >> simp_tac bool_ss [FST, SND] >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  `eval_operand child_src actual = SOME (n2w (sb + offset)) /\
   eval_operand child_dst actual = SOME (n2w d)` by
    metis_tac[abi_decoder_vars_extend_eval] >>
  qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [abi_decoder_address_frame_def, abi_decoder_prune_vars_def]
QED

Theorem abi_valid_singleton_setup_reach:
  abi_decode_singleton_setup dst src opc hi st = ((child_src,child_dst),st') /\
  abi_valid_singleton_setup_pre st src dst opc hi sb d offset
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ ~initial.vs_halted ==>
  ?actual. actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    eval_operand child_src actual = SOME (n2w (sb + offset)) /\
    eval_operand child_dst actual = SOME (n2w d) /\
    abi_decoder_operand_live st'.cs_next_var child_src /\
    abi_decoder_operand_live st'.cs_next_var child_dst /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_valid_singleton_setup_reentry >> strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_valid_singleton_setup_pre_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial reached` >>
  qexists_tac `reached` >>
  gvs[abi_decoder_address_frame_def, eval_op_inst_idx, fresh_vars_wrt_def]
QED
