Theory ctorDeployMemoryRunMemEntryPrefix
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunMemEntryRegistration ctorDeployMemoryRunMemEntryBoundary
  ctorDeployMemoryRunMemEntryCompositeSetup contextProps emitHelperProps
  context emitHelper fragExec fragExecMem instMemFrontier unitTransformDefs
  venomInst venomState venomExecSemantics allocaHistory exprLoweringProps
  compileEnv instIdxIndep memSafeRun moduleLoweringProps entrySinkExtraction
  abiDecoderReservation rich_list list contextCodegenRel codegenRel

(* The fixed immutables region only names address zero.  In particular this
   step does not allocate, touch memory, or consume a GAS reading. *)
Theorem ctor_checked_fixed_region:
  compile_fixed_region_with_id nbytes st = ((id,buf),st') /\
  fresh_vars_wrt st initial /\ fn_has_code st st' func /\
  alloca_history func initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    actual = (update_var (STRING #"%" (toString st.cs_next_var)) 0w initial
      with vs_inst_idx := LENGTH st'.cs_current_insts) /\
    eval_operand buf.buf_operand actual = SOME 0w /\
    fresh_vars_wrt st' actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\
    alloca_history func actual
Proof
  strip_tac >> drule compile_fixed_region_as_assign >> strip_tac >>
  drule ctor_checked_arg_emit_shape >> strip_tac >>
  `run_inst_seq (emitted_insts st st') initial =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) 0w initial)` by
    (drule emitted_insts_emit_op >>
     simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  drule compile_fixed_region_zero_correct >> disch_then drule >> strip_tac >>
  `inst_extends st st'` by metis_tac[inst_extends_emit_op] >>
  `ss' = update_var (STRING #"%" (toString st.cs_next_var)) 0w initial` by
    gvs[] >>
  `ss'.vs_allocas = initial.vs_allocas /\ ss'.vs_current_bb = initial.vs_current_bb` by
    simp[update_var_def] >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` mp_tac) >>
  strip_tac >>
  goal_assum (drule_at Any) >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, update_var_def]
QED

Theorem ctor_checked_payable_shape:
  emit_op CALLVALUE [] st0 = (cv,st1) /\
  emit_op ISZERO [cv] st1 = (nv,st2) /\
  emit_void ASSERT [nv] st2 = ((),st3) ==>
  inst_extends st0 st3 /\ st3.cs_current_bb = st0.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st0 st3) /\
  !s. run_inst_seq_mem_ok (emitted_insts st0 st3) s
Proof
  strip_tac >>
  `inst_extends st0 st3` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void, inst_extends_trans] >>
  asm_rewrite_tac[] >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  gen_tac >> irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_mem_below_frontier_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    inst_dload_in_section_def]
QED

Theorem ctor_checked_payable:
  emit_op CALLVALUE [] st0 = (cv,st1) /\
  emit_op ISZERO [cv] st1 = (nv,st2) /\
  emit_void ASSERT [nv] st2 = ((),st3) /\
  fresh_vars_wrt st0 initial /\ initial.vs_call_ctx.cc_callvalue = 0w /\
  fn_has_code st0 st3 func /\ alloca_history func initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st0.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st0.cs_current_insts ==>
  ?actual raw.
    run_inst_seq (emitted_insts st0 st3) initial = OK raw /\
    actual = raw with vs_inst_idx := LENGTH st3.cs_current_insts /\
    fresh_vars_wrt st3 actual /\ ~actual.vs_halted /\
    actual.vs_current_bb = st3.cs_current_bb /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\
    alloca_history func actual
Proof
  strip_tac >> drule_all compile_payable_check_ok_or_revert >>
  simp[] >> strip_tac >>
  drule_all ctor_checked_payable_shape >> strip_tac >>
  `ss'.vs_halted = initial.vs_halted /\
   ss'.vs_current_bb = initial.vs_current_bb /\ ss'.vs_prev_bb = initial.vs_prev_bb` by
    (irule run_inst_seq_preserves_entry_control >>
     qexists `emitted_insts st0 st3` >> fs[EVERY_CONJ]) >>
  `ss'.vs_allocas = initial.vs_allocas /\ ss'.vs_alloca_next = initial.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     qexists `emitted_insts st0 st3` >> fs[EVERY_CONJ]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st0 st3)` by
    fs[EVERY_CONJ] >>
  `run_inst_seq_mem_ok (emitted_insts st0 st3) initial` by simp[] >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists `ss'` >>
  gvs[fresh_vars_wrt_def]
QED

Theorem ctor_checked_lock_shape:
  compile_nonreentrant_lock key F F st = ((),st') ==>
  inst_extends st st' /\ st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st') /\
  !s. run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[compile_nonreentrant_lock_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st st'` by metis_tac[inst_extends_trans] >>
  asm_rewrite_tac[] >>
  gvs[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
      fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  gen_tac >> irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_mem_below_frontier_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    inst_dload_in_section_def]
QED

Theorem ctor_checked_lock:
  compile_nonreentrant_lock key F F st = ((),st') /\
  sload (n2w key) initial <> 2w /\ ~initial.vs_call_ctx.cc_static /\
  fresh_vars_wrt st initial /\ fn_has_code st st' func /\
  alloca_history func initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual raw.
    run_inst_seq (emitted_insts st st') initial = OK raw /\
    actual = raw with vs_inst_idx := LENGTH st'.cs_current_insts /\
    sload (n2w key) actual = 2w /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\
    alloca_history func actual
Proof
  strip_tac >> drule_all compile_nonreentrant_lock_correct >> strip_tac >>
  drule ctor_checked_lock_shape >> strip_tac >>
  `ss'.vs_halted = initial.vs_halted /\
   ss'.vs_current_bb = initial.vs_current_bb /\ ss'.vs_prev_bb = initial.vs_prev_bb` by
    (irule run_inst_seq_preserves_entry_control >>
     qexists `emitted_insts st st'` >> fs[EVERY_CONJ]) >>
  `ss'.vs_allocas = initial.vs_allocas /\ ss'.vs_alloca_next = initial.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     qexists `emitted_insts st st'` >> fs[EVERY_CONJ]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by simp[] >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexistsl [`ss' with vs_inst_idx := LENGTH st'.cs_current_insts`, `ss'`] >>
  gvs[sload_def, contract_storage_def]
QED
