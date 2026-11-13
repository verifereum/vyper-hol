Theory abiDecodeMemRange
Ancestors
  abiDecoderReentry abiDecoderRange abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomInst venomState words arithmetic list rich_list
  fragGasSeqMem fragGasSeqAbort fragGasMode
  allocaHistoryFragment freshWrites fragGasFresh
  instMemFrontier memSafeRun fragExecMem loweringStateRelDefs bodyUnopFragMemory

Theorem abi_decode_range_sequence:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h ==>
  ?t. (if w2n p <= w2n q /\ w2n q <= w2n h then
         run_inst_seq (emitted_insts st st') s = OK t
       else run_inst_seq (emitted_insts st st') s = Abort Revert_abort t)
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op LT [e;src] st = (wrapped,c1)` >>
  rename1 `emit_op ISZERO [wrapped] c1 = (no_wrap,c2)` >>
  rename1 `emit_op GT [e;hi] c2 = (oob,c3)` >>
  rename1 `emit_op ISZERO [oob] c3 = (in_bounds,c4)` >>
  rename1 `emit_op AND [no_wrap;in_bounds] c4 = (ok,c5)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand e s2 = SOME q /\ eval_operand hi s2 = SOME h` by metis_tac[] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand no_wrap s4 = SOME (bool_to_word (bool_to_word (w2n q < w2n p) = 0w))` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  suspend "finish"
QED

Resume abi_decode_range_sequence[finish]:
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  ntac 4 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  Cases_on `w2n p <= w2n q /\ w2n q <= w2n h`
  >- (`eval_operand ok s5 = SOME 1w` by
        (gvs[bool_to_word_def] >> simp[]) >>
      `(1w:bytes32) <> 0w` by simp[] >>
      drule_all emit_void_ASSERT_ok_full >> simp[] >> strip_tac >> gvs[] >>
      drule_all abi_decode_sequence_chain >> strip_tac >> metis_tac[]) >>
  `eval_operand ok s5 = SOME 0w` by
    (Cases_on `w2n q < w2n p` >> Cases_on `w2n q > w2n h` >>
     gvs[bool_to_word_def]) >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  `emitted_insts st st' = emitted_insts st c5 ++ emitted_insts c5 st'` by
    (irule emitted_insts_append >> gvs[inst_extends_def, IS_PREFIX_APPEND] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  simp[] >> drule run_inst_seq_append >>
  disch_then (pure_rewrite_tac o single) >> simp[]
QED
Finalise abi_decode_range_sequence

Theorem abi_decode_range_straight[local]:
  straight_fresh (compile_abi_decode_range_check src e hi)
Proof
  rewrite_tac[compile_abi_decode_range_check_def] >>
  rpt (irule straight_fresh_bind >>
       (reverse conj_tac >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
       gen_tac >> BETA_TAC) >>
  irule straight_fresh_emit_void >> simp[fresh_write_op_def]
QED

Theorem abi_decode_range_mem_ok:
  compile_abi_decode_range_check src e hi st = ((),st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  mp_tac abi_decode_range_straight >> simp[straight_fresh_def] >>
  disch_then drule >> strip_tac >> metis_tac[writes_fresh_mem_ok]
QED

Theorem abi_decode_range_path_mem:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n p <= w2n q /\ w2n q <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
      alloca_history func t) /\
  (~(w2n p <= w2n q /\ w2n q <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >>
  `straight_fresh (compile_abi_decode_range_check src e hi)` by
    metis_tac[abi_decode_range_straight] >>
  drule_all straight_fresh_code_prefix >> strip_tac >>
  `writes_fresh st (emitted_insts st st') /\
   st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
   st'.cs_current_bb = st.cs_current_bb` by gvs[straight_fresh_def] >>
  drule writes_fresh_path_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[abi_decode_range_mem_ok] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0` by
    metis_tac[writes_fresh_gas_count] >>
  conj_tac >- suspend "success" >> suspend "reject"
QED

Resume abi_decode_range_path_mem[success]:
  strip_tac >> drule_all compile_abi_decode_range_check_sequence >> strip_tac >>
  suspend "success_path"
QED

Resume abi_decode_range_path_mem[success_path]:
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (Cases >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def, lookup_var_def, not_fresh_at_def]) >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st st' ++ rest`
    by fs[IS_PREFIX_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')`
    by fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  qexists_tac `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st')` >>
  simp[eval_operand_def, lookup_var_def] >>
  `t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[] >> conj_tac >- metis_tac[LENGTH_APPEND] >>
  fs[fresh_vars_wrt_def]
QED

Resume abi_decode_range_path_mem[reject]:
  strip_tac >> drule_all abi_decode_range_sequence >> simp[] >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) (emitted_insts st st')`
    by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >>
  metis_tac[]
QED
Finalise abi_decode_range_path_mem
