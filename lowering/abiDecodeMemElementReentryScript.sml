(* Finite memory-checked decoder sequences tolerate stale temporaries. *)
Theory abiDecodeMemElementReentry
Ancestors
  abiDecodeMemElementFrame abiDecodeMemElementPointer abiDecodeMemReentry abiDecoderReentryPointer
  abiDecoderReentry abiDecoderContract abiEncoder abiDecoderBytesPrefix words
  abiDecoderVarSequence abiDecoderVarExtend opcodeClass venomExecSemantics
  venomState venomInst fragExecMem fragExec emitHelperProps exprLoweringProps
  compileEnv emitHelper rich_list list fragGasSeqMem fragGasSeqAbort
  entrySinkExtraction entryDecoderHistoryFrame loweringStateRelDefs bodyUnopFragMemory

Theorem abi_decode_revert_inputs[local]:
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = Abort Revert_abort u ==>
  abi_decoder_inputs_defined inst s
Proof
  strip_tac >>
  `inst.inst_opcode = ASSERT` by
    (drule opcodeClassTheory.step_inst_base_abort_opcodes >>
     fs[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[step_inst_base_def] >> strip_tac >>
  gvs[AllCaseEqs(), abi_decoder_inputs_defined_def, eval_operand_def] >>
  rpt strip_tac >> gvs[eval_operand_def]
QED

Theorem abi_decode_sequence_revert_extend[local]:
  !code extras s t u.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  abi_decoder_vars_extend extras s t /\
  run_inst_seq code s = Abort Revert_abort u ==>
  ?v. run_inst_seq code t = Abort Revert_abort v /\
    abi_decoder_vars_extend extras u v
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[]
  >- (drule_all abi_decoder_step_vars_extend >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      goal_assum (drule_at Any) >> simp[run_inst_seq_def]) >>
  drule_all abi_decode_revert_inputs >> strip_tac >>
  drule_all abi_decode_reentry_revert >> strip_tac >>
  goal_assum (drule_at Any) >> simp[run_inst_seq_def]
QED

Theorem abi_decode_sequence_mem_extend[local]:
  !code extras s t.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  abi_decoder_vars_extend extras s t /\
  ((?u. run_inst_seq code s = OK u) \/
   (?u. run_inst_seq code s = Abort Revert_abort u)) /\
  run_inst_seq_mem_ok code s ==>
  run_inst_seq_mem_ok code t
Proof
  Induct >- simp[run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> simp_tac bool_ss [EVERY_DEF, run_inst_seq_def,
    run_inst_seq_mem_ok_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[]
  >>~- ([`step_inst_base h s = OK v`],
    drule_all abi_decoder_step_inputs_defined >> strip_tac >>
    drule_all abi_decode_reentry_memory_checks >> strip_tac >>
    drule_all abi_decoder_step_vars_extend >> strip_tac >>
    simp[] >> rpt conj_tac >- metis_tac[] >- metis_tac[] >>
    first_x_assum irule >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all abi_decode_revert_inputs >> strip_tac >>
  drule_all abi_decode_reentry_memory_checks >> strip_tac >>
  drule_all abi_decode_reentry_revert >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem abi_decode_element_reentry_sequence[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') /\
  hi <> Lit 0w /\ eval_operand bop s = SOME b /\ eval_operand src s = SOME p /\
  eval_operand data s = SOME d /\ eval_operand hi s = SOME h /\
  abi_decoder_operand_live st.cs_next_var bop /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var data /\
  abi_decoder_operand_live st.cs_next_var hi /\
  w2n (b+p) + 32 <= s.vs_alloca_next /\ sz < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  (w2n d + w2n (abi_decode_load MLOAD (b+p) s) + sz <= w2n h ==>
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      eval_operand ptr_op t = SOME (d+abi_decode_load MLOAD (b+p) s) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (~(w2n d + w2n (abi_decode_load MLOAD (b+p) s) + sz <= w2n h) ==>
    ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t)
Proof
  strip_tac >>
  qabbrev_tac `clean = abi_decoder_prune_vars st.cs_next_var s` >>
  `fresh_vars_wrt st clean /\ abi_decoder_vars_extend s.vs_vars clean s` by
    simp[Abbr `clean`, abi_decoder_prune_fresh, abi_decoder_prune_extension] >>
  `eval_operand bop clean = SOME b /\ eval_operand src clean = SOME p /\
   eval_operand data clean = SOME d /\ eval_operand hi clean = SOME h /\
   w2n (b+p)+32 <= clean.vs_alloca_next /\
   abi_decode_load MLOAD (b+p) clean = abi_decode_load MLOAD (b+p) s` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_vars_def,
      abi_decode_load_def, mload_def] >>
  drule_all abi_decode_element_sequence >> simp_tac bool_ss [LET_THM] >>
  `((w2n d <= w2n (d+abi_decode_load MLOAD (b+p) s) /\
      w2n (d+abi_decode_load MLOAD (b+p) s) <=
        w2n (d+abi_decode_load MLOAD (b+p) s+n2w sz) /\
      w2n (d+abi_decode_load MLOAD (b+p) s+n2w sz) <= w2n h) <=>
     w2n d + w2n (abi_decode_load MLOAD (b+p) s) + sz <= w2n h)` by
    metis_tac[abi_decode_element_bounds] >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all abi_decode_element_mem_ok >> strip_tac >>
  drule abi_decode_element_shape >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')`
    by suspend "opcodes" >>
  `(?t. run_inst_seq (emitted_insts st st') clean = OK t) \/
   (?t. run_inst_seq (emitted_insts st st') clean = Abort Revert_abort t)` by metis_tac[] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule abi_decode_sequence_mem_extend >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[] >> conj_tac >- suspend "accept" >>
  strip_tac >> gvs[] >> drule_all abi_decode_sequence_revert_extend >> metis_tac[]
QED
Resume abi_decode_element_reentry_sequence[opcodes]:
  qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `hi <> Lit 0w` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  Cases_on `bop = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def] >> strip_tac >>
  gvs[emitted_insts_def, abi_decoder_reentry_opcode_def, mk_inst_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED
Resume abi_decode_element_reentry_sequence[accept]:
  strip_tac >> gvs[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_nonallocating_sequence_frame >> strip_tac >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  goal_assum (drule_at Any) >>
  conj_tac >- metis_tac[abi_decoder_vars_extend_eval] >>
  reverse conj_tac >- simp[Abbr `clean`, abi_decoder_prune_vars_def] >>
  metis_tac[abi_decode_element_total_frame]
QED
Finalise abi_decode_element_reentry_sequence

Theorem abi_decode_mload_element_reentry_path_mem:
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') /\
  hi <> Lit 0w /\ eval_operand bop s = SOME b /\ eval_operand src s = SOME p /\
  eval_operand data s = SOME d /\ eval_operand hi s = SOME h /\
  abi_decoder_operand_live st.cs_next_var bop /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var data /\
  abi_decoder_operand_live st.cs_next_var hi /\
  w2n (b+p) + 32 <= s.vs_alloca_next /\ sz < dimword (:256) /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n d + w2n (abi_decode_load MLOAD (b+p) s) + sz <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand ptr_op t = SOME (d+abi_decode_load MLOAD (b+p) s) /\
      w2n (d+abi_decode_load MLOAD (b+p) s) =
        w2n d + w2n (abi_decode_load MLOAD (b+p) s) /\
      w2n d <= w2n (d+abi_decode_load MLOAD (b+p) s) /\
      w2n (d+abi_decode_load MLOAD (b+p) s) + sz <= w2n h /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
      alloca_history func t) /\
  (~(w2n d + w2n (abi_decode_load MLOAD (b+p) s) + sz <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >> drule abi_decode_element_shape >> strip_tac >>
  drule_all abi_decode_element_reentry_sequence >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_mload_element_reentry_path_mem[accept]:
  strip_tac >> gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0`
    by (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_MEM] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by simp[IS_PREFIX_APPEND] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `w2n h < dimword (:256)` by irule w2n_lt >>
  `w2n d + w2n (abi_decode_load MLOAD (b+p) s) < dimword (:256)` by decide_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, w2n_add_2] >> gvs[]
QED
Resume abi_decode_mload_element_reentry_path_mem[reject]:
  disch_tac >> gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
Finalise abi_decode_mload_element_reentry_path_mem
