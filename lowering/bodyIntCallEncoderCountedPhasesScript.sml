(* Counted address phases and concrete encoder array control. *)
Theory bodyIntCallEncoderCountedPhases
Ancestors
  bodyIntCallDecoderCountedPrimitive bodyIntCallDecoderCountedControl
  bodyIntCallEncoderCountedLeaves abiEncoderMemberPhaseRaw abiEncoderArrayParent
  abiEncoderArrayHeader abiEncoderArrayPhases abiEncoderComplexCode
  abiEncoderAddressReach abiDecoderArrayHeader abiDecoderContract abiDecoderLoop
  abiDecoderArrayLoopInit entrySinkExtraction abiEncoderArrayContext
  fragExec fragGasPath emitHelperProps compileEnv venomState venomInst
  venomExecSemantics instIdxIndep words list rich_list finite_map arithmetic

Theorem intcall_encoder_phase_raw_path:
  fn_has_code st final func /\ final.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts final.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final) /\
  abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?n. gas_path ctx func initial n (OK ready)
Proof
  strip_tac >> gvs[abi_encoder_member_phase_raw_def] >>
  irule intcall_same_block_seq_path >> simp[] >> qexists_tac `st` >> simp[]
QED

Theorem intcall_encoder_binary_counted:
  emit_op opc [lhs;rhs] st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready n. eval_operand out ready = SOME (if opc = ADD then a+b else a*b) /\
    fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
    ready.vs_current_bb = final.cs_current_bb /\
    ready.vs_inst_idx = LENGTH final.cs_current_insts /\ ~ready.vs_halted /\
    gas_path ctx func initial n (OK ready)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_binary_raw >> strip_tac >>
  drule_all abi_encoder_member_binary_transport >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[mk_inst_def, is_terminator_def]) >>
  drule_all intcall_encoder_phase_raw_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_encoder_load_counted:
  emit_op MLOAD [src] st = (out,final) /\ eval_operand src initial = SOME p /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready n. eval_operand out ready = SOME (mload (w2n p) initial) /\
    fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
    ready.vs_current_bb = final.cs_current_bb /\
    ready.vs_inst_idx = LENGTH final.cs_current_insts /\ ~ready.vs_halted /\
    gas_path ctx func initial n (OK ready)
Proof
  strip_tac >> drule_all abi_encoder_member_load_raw >> strip_tac >>
  drule_all abi_encoder_member_load_transport >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by
    (drule emitted_insts_emit_op >> strip_tac >> gvs[mk_inst_def, is_terminator_def]) >>
  drule_all intcall_encoder_phase_raw_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem intcall_encoder_array_count_counted:
  abi_decode_array_header dst src MLOAD st = (cnt,final) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. eval_operand cnt actual = SOME (mload sb initial) /\
    mem_word_at db actual.vs_memory = mload sb initial /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame db 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_array_count_copy_sequence >> strip_tac >>
  `isPREFIX st.cs_current_insts final.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  goal_assum (drule_at Any) >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> metis_tac[]
QED

Theorem intcall_encoder_array_finish_counted:
  abi_encode_array_finish parent_ptr size_op st = (out,final) /\
  eval_operand parent_ptr initial = SOME (n2w slot) /\ mload slot initial = old_word /\
  eval_operand size_op initial = SOME size_word /\
  abi_decoder_operand_live st.cs_next_var parent_ptr /\ abi_decoder_operand_live st.cs_next_var size_op /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st final func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. eval_operand out actual = SOME (old_word+size_word) /\
    mload slot actual = old_word+size_word /\ fresh_vars_wrt limit_st actual /\
    abi_decode_frame slot 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >> drule abi_encode_array_finish_shape >> strip_tac >>
  drule_all abi_encode_array_finish_sequence >> strip_tac >>
  `isPREFIX st.cs_current_insts final.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  goal_assum (drule_at Any) >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def] >> metis_tac[]
QED

Theorem intcall_encoder_array_header_path:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl|> /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\ count_op <> Var iv /\
  eval_operand ip s = SOME p /\ eval_operand count_op s = SOME (n2w n) /\
  mload (w2n p) s = n2w i /\ i <= n /\ n < dimword (:256) ==>
  gas_path ctx func s 0 (OK (jump_to (if i<n then body_lbl else exit_lbl)
    (abi_encode_array_header_state iv cmp done i n s)))
Proof
  strip_tac >> drule_all abi_encode_array_header_prefix >> strip_tac >>
  qmatch_goalsub_abbrev_tac `jump_to dest t` >>
  `gas_path ctx func s 0 (OK (t with vs_inst_idx := 3))` by
    (irule intcall_zero_prefix_path >> simp[] >>
     qexists_tac `TAKE 3 (abi_encode_array_header_insts id ip count_op iv cmp done body_lbl exit_lbl)` >>
     simp[abi_encode_array_header_insts_def, mk_inst_def, is_terminator_def, Abbr `t`]) >>
  `gas_path ctx func (t with vs_inst_idx := 3) 0 (OK (jump_to dest t))` by
    (`jump_to dest t = jump_to dest (t with vs_inst_idx := 3)` by simp[jump_to_def] >>
     pop_assum SUBST1_TAC >> irule intcall_jump_step_path >>
     simp[Abbr `t`, abi_encode_array_header_state_def, update_var_def] >>
     qexists_tac `mk_inst (id+3) JNZ [Var done;Label exit_lbl;Label body_lbl] []` >>
     simp[get_instruction_def, abi_encode_array_header_insts_def, mk_inst_def,
       is_terminator_def, step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, Abbr `dest`] >>
     Cases_on `i<n` >> simp[bool_to_word_def]) >>
  metis_tac[gas_path_then, ADD_CLAUSES]
QED
