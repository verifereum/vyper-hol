(* Counted straight-line encoder execution with physical scratch effects. *)
Theory bodyIntCallEncoderCountedLeaves
Ancestors
  bodyIntCallDecoderCountedPrimitive abiEncoderSequence abiScratchLeafEffect
  abiScratchEncoderContract abiDecoderContract abiDecoderAllocation abiDecoderLoop
  abiEncoderReentryLeaves abiEncoderBytes abiEncoderBytesCode abiEncoderLeafCode abiEncoderAdmissible
  compileEnv emitHelperProps exprLoweringProps fragExec fragGasPath entrySinkExtraction
  venomState venomExecSemantics venomInst instIdxIndep valueEncoding contractABI
  words list rich_list

Theorem intcall_encoder_sequence_counted:
  st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_has_code st st' func /\ abi_decoder_budget first last b cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (?raw. run_inst_seq (emitted_insts st st') initial = OK raw /\
    abi_encoder_sequence_post at av out st limit_st d initial raw) ==>
  ?actual n. abi_encoder_sequence_post at av out st limit_st d initial actual /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  irule abi_scratch_sequence_post_effect >> simp[] >>
  qexists_tac `out` >> simp[]
QED

Theorem intcall_encoder_word_counted:
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,st') /\
  abi_encoder_input AbiPrimWord at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ abi_decoder_budget first last b arena_cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_encoder_sequence_post at av out st limit_st d initial actual /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b arena_cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `abi_encoder_static_leaf AbiPrimWord` by simp[abi_encoder_static_leaf_def] >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule_all abi_encoder_word_input_reentry >> strip_tac >>
  irule intcall_encoder_sequence_counted >> simp[] >>
  simp[abi_encoder_sequence_post_def]
QED

Theorem intcall_encoder_copy_counted:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_input (AbiCopy sz) at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ abi_decoder_budget first last b arena_cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_encoder_sequence_post at av out st limit_st d initial actual /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b arena_cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `abi_encoder_static_leaf (AbiCopy sz)` by simp[abi_encoder_static_leaf_def] >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule_all abi_encoder_copy_input_reentry >> strip_tac >>
  irule intcall_encoder_sequence_counted >> simp[] >>
  simp[abi_encoder_sequence_post_def]
QED

Theorem intcall_encoder_bytes_counted:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') /\
  abi_encoder_input (AbiBytestring maxlen) at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d+LENGTH (enc at av) < dimword (:256) /\
  (sb+cap <= d \/ d+LENGTH (enc at av) <= sb) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ abi_decoder_budget first last b arena_cap initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_encoder_sequence_post at av out st limit_st d initial actual /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b arena_cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_bytes_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all abi_encoder_bytes_sequence >> strip_tac >>
  irule intcall_encoder_sequence_counted >> simp[] >>
  simp[abi_encoder_sequence_post_def]
QED
