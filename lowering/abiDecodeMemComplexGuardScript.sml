(* The bounded complex head guard, including stale-variable replay and rejection. *)
Theory abiDecodeMemComplexGuard
Ancestors
  abiDecodeMemFiniteGuards abiDecodeMemSequenceReentry abiDecodeMemStaticFrame
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderReentryPointer
  abiDecoderReentry abiDecoderVarSequence abiDecoderVarExtend abiDecoderContract
  abiDecoderSiteEffect abiEncoder freshWrites
  fragGasSeqMem fragGasSeqAbort fragGasMode fragExecMem
  entryDecoderHistoryFrame entryDecoderSetupEndpoint entrySinkExtraction allocaHistoryFragment
  bodyUnopFragMemory loweringStateRelDefs emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst
  words arithmetic list rich_list

Theorem abi_decode_complex_guard_clean[local]:
  abi_decode_complex_head_guard src hi head_sz st = ((),en) /\ hi <> Lit 0w /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\ inst_extends st en /\
  (w2n p <= w2n (p+n2w head_sz) /\ w2n (p+n2w head_sz) <= w2n h ==>
    ?t. run_inst_seq (emitted_insts st en) s = OK t /\
      fresh_vars_wrt en t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (~(w2n p <= w2n (p+n2w head_sz) /\ w2n (p+n2w head_sz) <= w2n h) ==>
    ?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_complex_head_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `eval_operand (Lit (n2w head_sz)) s = SOME (n2w head_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_range_sequence_mem >> strip_tac >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Theorem abi_decode_complex_guard_outputs[local]:
  abi_decode_complex_head_guard src hi head_sz st = ((),en) /\ not_fresh_at st x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st en)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> fs[not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem abi_decode_complex_guard_reentry_mem[local]:
  abi_decode_complex_head_guard src hi head_sz st = ((),en) /\ hi <> Lit 0w /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\
  (w2n p <= w2n (p+n2w head_sz) /\ w2n (p+n2w head_sz) <= w2n h ==>
    ?t. run_inst_seq (emitted_insts st en) s = OK t /\
      fresh_vars_wrt limit_st t /\ decode_static_frame s t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (~(w2n p <= w2n (p+n2w head_sz) /\ w2n (p+n2w head_sz) <= w2n h) ==>
    ?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t)
Proof
  strip_tac >> qabbrev_tac `clean = abi_decoder_prune_vars st.cs_next_var s` >>
  `fresh_vars_wrt st clean /\ abi_decoder_vars_extend s.vs_vars clean s /\
   eval_operand src clean = SOME p /\ eval_operand hi clean = SOME h` by
    simp[Abbr `clean`, abi_decoder_prune_fresh, abi_decoder_prune_extension,
      abi_decoder_prune_eval] >>
  drule_all abi_decode_complex_guard_clean >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st en)`
    by fs[EVERY_MEM] >>
  `(?u. run_inst_seq (emitted_insts st en) clean = OK u) \/
   (?u. run_inst_seq (emitted_insts st en) clean = Abort Revert_abort u)` by
    (Cases_on `w2n p <= w2n (p+n2w head_sz) /\ w2n (p+n2w head_sz) <= w2n h` >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (irule abi_decode_sequence_mem_extend >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[] >> conj_tac >- suspend "accept" >>
  strip_tac >> gvs[] >>
  drule_all abi_decode_sequence_revert_extend >> metis_tac[]
QED
Resume abi_decode_complex_guard_reentry_mem[accept]:
  strip_tac >> gvs[] >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) s = OK actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `fresh_vars_wrt limit_st actual` by
    (irule abi_decoder_vars_extend_fresh >> goal_assum (drule_at Any) >>
     fs[fresh_vars_wrt_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by fs[EVERY_MEM] >>
  drule_all entry_sequence_nonterminator_labels >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op actual = eval_operand op s` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def] >> strip_tac >>
     rename1 `lookup_var name actual = lookup_var name s` >>
     `not_fresh_at st name` by fs[not_fresh_at_def] >>
     irule entry_sequence_nonoutput_lookup >>
     qexists_tac `emitted_insts st en` >> simp[] >>
     drule_all abi_decode_complex_guard_outputs >> fs[EVERY_MEM]) >>
  `decode_static_frame s actual` by
    (irule abi_decode_reentry_sequence_static_frame >>
     qexists_tac `emitted_insts st en` >> simp[]) >>
  qexists_tac `actual` >> simp[] >>
  fs[Abbr `clean`, abi_decoder_prune_vars_def]
QED
Finalise abi_decode_complex_guard_reentry_mem[local]

Theorem abi_decode_complex_guard_path_mem:
  abi_decode_complex_head_guard src hi head_sz st = ((),en) /\ hi <> Lit 0w /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n p <= w2n (p+n2w head_sz) /\ w2n (p+n2w head_sz) <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
      t.vs_inst_idx = LENGTH en.cs_current_insts /\
      fresh_vars_wrt limit_st t /\ decode_static_frame s t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t) /\
  (~(w2n p <= w2n (p+n2w head_sz) /\ w2n (p+n2w head_sz) <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >> drule_all abi_decode_complex_guard_reentry_mem >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st en)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     Cases_on `i.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def]) >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  conj_tac >- suspend "accept" >>
  strip_tac >>
  `?u. run_inst_seq (emitted_insts st en) s = Abort Revert_abort u` by metis_tac[] >>
  pop_assum strip_assume_tac >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
Resume abi_decode_complex_guard_path_mem[accept]:
  strip_tac >>
  qpat_x_assum `(_ /\ _ ==> ?t. run_inst_seq _ _ = OK t /\ _)` mp_tac >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) s = OK u` >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st en)) = 0` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st en) = LENGTH en.cs_current_insts` by
    gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexists_tac `u with vs_inst_idx := LENGTH en.cs_current_insts` >>
  gvs[instMemFrontierTheory.eval_operand_inst_idx, fresh_vars_wrt_def,
    decode_static_frame_def, venom_state_component_equality]
QED
Finalise abi_decode_complex_guard_path_mem
