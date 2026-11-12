(* Preparation with an explicit ambient frame at the paired endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixEntryPrepare
Ancestors
  loweringStateRelDefs
  slotCopyExecution compileEnv
  ctorDeployMemoryRunPtrPrefixPrepare
  ctorDeployMemoryRunPtrPrefixRegisterAddress ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixSequence context emitHelper emitHelperProps exprLoweringProps
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  finite_map words arithmetic pred_set list rich_list codegenRel contextCodegenRel memLocDefs
  fragExec abiDecoderContract abiDecoderLoop
  fragGasSeqMem allocaFootprint ctorDeployMemoryRunMemEntryWord
  unitTransformDefs memSafeRun fragGasPathMem
  fragGasOriginPtr fragGasOriginPtrLoop

Theorem prepare_sequence_checked[local]:
  last.cs_current_insts = st.cs_current_insts ++ code /\
  last.cs_current_bb = st.cs_current_bb /\ fn_has_code st last func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS /\ i.inst_opcode <> ALLOCA) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH last.cs_current_insts)) /\
  (alloca_history func s ==>
    alloca_history func (t with vs_inst_idx := LENGTH last.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX last.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) code) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  conj_tac
  >- (drule_all run_inst_seq_gas_path_mem >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  strip_tac >> irule ctor_sequence_history_advance >>
  qexistsl [`bb`,`code`,`s`] >> fs[EVERY_MEM]
QED

(* The paycheck's ASSERT on a nonzero word, as a zero-mark joint path. *)
Theorem prepare_assert_origin[local]:
  emit_void ASSERT [a] st = ((),last) /\
  eval_operand a initial = SOME w /\ w <> 0w /\ op_taint tn a = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fn_has_code st last func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) []
    (OK (initial with vs_inst_idx := LENGTH last.cs_current_insts), G, tn)
Proof
  strip_tac >>
  `last.cs_current_bb = st.cs_current_bb /\
   last.cs_current_insts = st.cs_current_insts ++ [mk_inst st.cs_next_id ASSERT [a] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, emit_def] >>
  `?bb. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX last.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `get_instruction bb initial.vs_inst_idx = SOME (mk_inst st.cs_next_id ASSERT [a] [])` by
    (gvs[IS_PREFIX_APPEND] >> simp[get_instruction_def, EL_APPEND_EQN]) >>
  `step_inst 0 ctx (mk_inst st.cs_next_id ASSERT [a] []) initial = OK initial` by
    simp[step_inst_non_invoke, step_inst_base_def, mk_inst_def] >>
  `ghost_step 0 ctx PG G tn (mk_inst st.cs_next_id ASSERT [a] []) initial = (G, tn)` by
    (irule prefix_assert_ghost_step >> simp[]) >>
  `LENGTH last.cs_current_insts = SUC initial.vs_inst_idx` by simp[ADD1] >>
  pop_assum SUBST1_TAC >>
  mp_tac (Q.INST [`s` |-> `initial`, `i` |-> `mk_inst st.cs_next_id ASSERT [a] []`,
    `u` |-> `initial`, `G'` |-> `G`, `tn'` |-> `tn`] step_origin_ptr_path) >>
  simp[prefix_assert_ptr_step] >>
  simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

val PrepareEmit = ``\checked.
  emit_op opc ops st = (out,last) /\
  ((opc = CALLVALUE /\ ops = [] /\ w = initial.vs_call_ctx.cc_callvalue) \/
   (opc = ASSIGN /\ ops = [Lit 0w] /\ w = 0w) \/
   (opc = ISZERO /\ ops = [a] /\ eval_operand a initial = SOME 0w /\
    op_taint tn a = {} /\ w = 1w)) /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ fn_has_code st last func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt. eval_operand out t = SOME w /\ op_taint qt out = {} /\
    op_prov H out = NONE /\ fresh_vars_wrt last t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    t.vs_code = initial.vs_code /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
    t.vs_block_ctx = initial.vs_block_ctx /\ t.vs_logs = initial.vs_logs /\
    t.vs_requests = initial.vs_requests /\
    t.vs_pending_deletions = initial.vs_pending_deletions /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
    (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK t, H, qt)) /\
    (checked ==> gas_path_mem ctx func initial 0 (OK t) /\
      (alloca_history func initial ==> alloca_history func t))``;

Theorem prefix_entry_prepare_emit_actual_checked:
  (^PrepareEmit) T
Proof
  BETA_TAC >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `opc <> INVOKE /\ ~is_terminator opc /\
   run_inst_seq (emitted_insts st last) initial = OK
      (update_var (STRING #"%" (toString st.cs_next_var)) w initial)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[is_terminator_def, run_inst_seq_def, prefix_prepare_callvalue_step,
       SIMP_RULE (srw_ss()) [venomStateTheory.eval_operand_def]
         (Q.INST [`a` |-> `Lit 0w`] slotCopyExecutionTheory.slot_copy_step_assign),
       SIMP_RULE (srw_ss()) [venomExecSemanticsTheory.bool_to_word_def]
         (Q.SPECL [`a`,`0w`] emitHelperPropsTheory.step_ISZERO)]) >>
  drule_all prefix_register_address_emit_finish >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st last) initial` by
    (irule emit_op_mem_ok >> goal_assum (drule_at Any) >>
     gvs[inst_mem_below_frontier_def, inst_dload_in_section_def, mk_inst_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `gas_path_mem ctx func initial 0 (OK
      ((update_var (STRING #"%" (toString st.cs_next_var)) w initial)
       with vs_inst_idx := LENGTH last.cs_current_insts)) /\
    (alloca_history func initial ==> alloca_history func
      ((update_var (STRING #"%" (toString st.cs_next_var)) w initial)
       with vs_inst_idx := LENGTH last.cs_current_insts))` by
    (irule prepare_sequence_checked >> simp[update_var_def] >>
     qexistsl [`emitted_insts st last`,`st`] >>
     drule emitted_insts_emit_op >> drule prefix_register_address_emit_shape >>
     gvs[mk_inst_def, is_terminator_def, update_var_def]) >>
  `!D' explicit.
     gas_origin_ptr_path (D', lo, explicit, ctx, func, PG) (initial, G, tn) []
       (OK ((update_var (STRING #"%" (toString st.cs_next_var)) w initial)
            with vs_inst_idx := LENGTH last.cs_current_insts),
        DRESTRICT G (COMPL {STRING #"%" (toString st.cs_next_var)}),
        tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{}))` by
    (rpt gen_tac >> drule emitted_insts_emit_op >> strip_tac >>
     drule prefix_register_address_emit_origin >> disch_then irule >>
     gvs[is_terminator_def, run_inst_seq_mem_ok_def, prefix_prepare_callvalue_ptr,
         prefix_prepare_zero_ptr, prefix_iszero_ptr_step,
         prefix_prepare_callvalue_ghost, prefix_prepare_zero_ghost,
         prefix_prepare_iszero_ghost]) >>
  drule prefix_register_address_emit_shape >> strip_tac >>
  qexistsl [`(update_var (STRING #"%" (toString st.cs_next_var)) w initial)
               with vs_inst_idx := LENGTH last.cs_current_insts`,
            `DRESTRICT G (COMPL {STRING #"%" (toString st.cs_next_var)})`,
            `tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})`] >>
  `!y. not_fresh_at st y ==> y <> STRING #"%" (toString st.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  asm_rewrite_tac[] >>
  simp[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
    update_var_def] >>
  gvs[] >>
  FIRST [drule_all prefix_prepare_callvalue_run, drule_all prefix_prepare_zero_run,
         drule_all prefix_prepare_iszero_run] >>
  simp[update_var_def]
QED


val PrepareRegion = ``\checked.
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
   else comp_return (Lit 0w)) st = (imm,last) /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ fn_has_code st last func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt.
    eval_operand imm t = SOME 0w /\ op_taint qt imm = {} /\ op_prov H imm = NONE /\
    fresh_vars_wrt last t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    t.vs_code = initial.vs_code /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
    t.vs_block_ctx = initial.vs_block_ctx /\ t.vs_logs = initial.vs_logs /\
    t.vs_requests = initial.vs_requests /\
    t.vs_pending_deletions = initial.vs_pending_deletions /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
    (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK t, H, qt)) /\
    (checked ==> gas_path_mem ctx func initial 0 (OK t) /\
      (alloca_history func initial ==> alloca_history func t))``;

Theorem prefix_entry_prepare_region_actual_checked:
  (^PrepareRegion) T
Proof
  BETA_TAC >> strip_tac >> Cases_on `cap > 0`
  >- (gvs[comp_bind_def, comp_return_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> rename1 `compile_fixed_region_with_id cap st = (r,last)` >>
      PairCases_on `r` >>
      drule prefix_prepare_fixed_region_emit >> strip_tac >>
      simp[] >> irule (SRULE [] prefix_entry_prepare_emit_actual_checked) >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[comp_return_def] >> qexistsl [`initial`,`G`,`tn`] >>
  simp[eval_operand_def, op_taint_def, op_prov_def, abi_decode_sim_refl,
    gas_path_mem_rules, gas_origin_ptr_path_rules]
QED


Theorem prefix_entry_prepare_paycheck_actual_checked:
  emit_op CALLVALUE [] st = (cv,sa) /\
  emit_op ISZERO [cv] sa = (nv,sb) /\ emit_void ASSERT [nv] sb = ((),last) /\
  fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb last func /\
  initial.vs_call_ctx.cc_callvalue = 0w /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt.
    fresh_vars_wrt last t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    t.vs_code = initial.vs_code /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
    t.vs_block_ctx = initial.vs_block_ctx /\ t.vs_logs = initial.vs_logs /\
    t.vs_requests = initial.vs_requests /\
    t.vs_pending_deletions = initial.vs_pending_deletions /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
    (!D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK t, H, qt)) /\
    gas_path_mem ctx func initial 0 (OK t) /\
    (alloca_history func initial ==> alloca_history func t)
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `CALLVALUE`, `ops` |-> `[]`, `w` |-> `0w`]
    prefix_entry_prepare_emit_actual_checked)) >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
    (qx_choose_then `s1` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `allocas_from lo s1` by (fs[allocas_from_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[cv]`, `a` |-> `cv`, `w` |-> `1w`]
    prefix_entry_prepare_emit_actual_checked)) >>
  disch_then (qspecl_then [`PG`,`G1`,`D`]
    (qx_choose_then `s2` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  `allocas_from lo s2` by (fs[allocas_from_def] >> metis_tac[]) >>
  `1w <> (0w:bytes32)` by simp[] >>
  drule_all prefix_prepare_assert_actual >>
  disch_then (qspecl_then [`PG`,`G2`,`D`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `gas_path_mem ctx func s2 0
      (OK (s2 with vs_inst_idx := LENGTH last.cs_current_insts)) /\
    (alloca_history func s2 ==> alloca_history func
      (s2 with vs_inst_idx := LENGTH last.cs_current_insts))` by
    (irule prepare_sequence_checked >> simp[] >>
     qexistsl [`emitted_insts sb last`,`sb`] >>
     `run_inst_seq_mem_ok (emitted_insts sb last) s2` by
       (irule emit_void_mem_ok >> goal_assum (drule_at Any) >>
        simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def, mk_inst_def]) >>
     drule_all emit_void_ASSERT_ok >>
     drule emitted_insts_emit_void >>
     gvs[emit_void_assert_inst, mk_inst_def, is_terminator_def]) >>
  `gas_path_mem ctx func initial 0
      (OK (s2 with vs_inst_idx := LENGTH last.cs_current_insts))` by
    metis_tac[gas_path_mem_then, ADD] >>
  `!y. not_fresh_at st y ==> not_fresh_at sa y` by
    (drule (Q.INST [`opc` |-> `CALLVALUE`, `ops` |-> `[]`] prefix_register_address_emit_shape) >>
     strip_tac >> simp[not_fresh_at_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `!D' explicit.
     gas_origin_ptr_path (D', lo, explicit, ctx, func, PG) (initial, G, tn) []
       (OK (s2 with vs_inst_idx := LENGTH last.cs_current_insts), G2, tn2)` by
    (drule_all prepare_assert_origin >> strip_tac >>
     metis_tac[gas_origin_ptr_path_trans]) >>
  qexistsl [`s2 with vs_inst_idx := LENGTH last.cs_current_insts`,`G2`,`tn2`] >>
  simp[lookup_var_def] >>
  rpt conj_tac
  >- metis_tac[lookup_var_def]
  >- metis_tac[abi_decode_sim_trans]
  >> metis_tac[]
QED


Theorem prefix_entry_prepare_payable_actual_checked:
  (if payable then comp_return ()
   else comp_bind (emit_op CALLVALUE [])
     (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),last) /\
  (payable \/ initial.vs_call_ctx.cc_callvalue = 0w) /\
  fn_has_code st last func /\ allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt.
    fresh_vars_wrt last t /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    t.vs_code = initial.vs_code /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
    t.vs_block_ctx = initial.vs_block_ctx /\ t.vs_logs = initial.vs_logs /\
    t.vs_requests = initial.vs_requests /\
    t.vs_pending_deletions = initial.vs_pending_deletions /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
    (!D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK t, H, qt)) /\
    gas_path_mem ctx func initial 0 (OK t) /\
    (alloca_history func initial ==> alloca_history func t)
Proof
  rpt gen_tac >> disch_tac >> Cases_on `payable`
  >- (gvs[comp_return_def] >> qexistsl [`initial`,`G`,`tn`] >> simp[abi_decode_sim_refl, gas_path_mem_rules,
        gas_origin_ptr_path_rules]) >>
  gvs[comp_bind_def] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLVALUE [] st = (cv,sa)` >>
  rename1 `emit_op ISZERO [cv] sa = (nv,sb)` >>
  `cs_extends st sa` by (drule (Q.INST [`opc` |-> `CALLVALUE`, `ops` |-> `[]`]
      prefix_register_address_emit_shape) >> simp[]) >>
  `cs_extends sa sb` by (drule (Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[cv]`]
      prefix_register_address_emit_shape) >> simp[]) >>
  `cs_extends sb last` by
    (irule cs_extends_same_block >>
     gvs[emit_void_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,fresh_id_def,emit_def]) >>
  `fn_has_code st sa func /\ fn_has_code sa sb func /\ fn_has_code sb last func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  irule prefix_entry_prepare_paycheck_actual_checked >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED


Theorem prefix_entry_prepare_actual_checked:
  (if payable then comp_return ()
   else comp_bind (emit_op CALLVALUE [])
     (\cv. comp_bind (emit_op ISZERO [cv]) (\nv. emit_void ASSERT [nv]))) st = ((),pay) /\
  (if cap > 0 then
     comp_bind (compile_fixed_region_with_id cap) (\r. comp_return (SND r).buf_operand)
   else comp_return (Lit 0w)) pay = (imm,last) /\
  (payable \/ initial.vs_call_ctx.cc_callvalue = 0w) /\
  fn_has_code st last func /\ allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
  fresh_vars_wrt st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t H qt.
    eval_operand imm t = SOME 0w /\ op_taint qt imm = {} /\ op_prov H imm = NONE /\
    fresh_vars_wrt last t /\
    (!x. imm = Var x ==> FLOOKUP H x = NONE) /\
    (tn = entry_taint ==> qt.t_mem = {} /\ qt.t_stor = {} /\ qt.t_trans = {} /\ qt.t_imm = {}) /\
    t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
    t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_data_section = initial.vs_data_section /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_labels = initial.vs_labels /\
    t.vs_outcomes = initial.vs_outcomes /\ t.vs_gas_readings = initial.vs_gas_readings /\
    t.vs_code = initial.vs_code /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
    t.vs_block_ctx = initial.vs_block_ctx /\ t.vs_logs = initial.vs_logs /\
    t.vs_requests = initial.vs_requests /\
    t.vs_pending_deletions = initial.vs_pending_deletions /\
    (!y v. not_fresh_at st y /\ lookup_var y initial = SOME v ==> lookup_var y t = SOME v) /\
    (!y. not_fresh_at st y ==> FLOOKUP H y = FLOOKUP G y /\
      op_taint qt (Var y) = op_taint tn (Var y)) /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial t /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt t) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial) /\
    (!D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (initial, G, tn) [] (OK t, H, qt)) /\
    gas_path_mem ctx func initial 0 (OK t) /\
    (alloca_history func initial ==> alloca_history func t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule prefix_prepare_payable_layout >> strip_tac >>
  drule prefix_prepare_region_layout >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all prefix_entry_prepare_payable_actual_checked >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
    (qx_choose_then `s1` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `allocas_from lo s1` by (fs[allocas_from_def] >> metis_tac[]) >>
  drule_all (SRULE [] prefix_entry_prepare_region_actual_checked) >>
  disch_then (qspecl_then [`tn1`,`PG`,`G1`,`D`]
    (qx_choose_then `s2` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  `!y. not_fresh_at st y ==> not_fresh_at pay y` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!D' explicit.
     gas_origin_ptr_path (D', lo, explicit, ctx, func, PG) (initial, G, tn) []
       (OK s2, G2, tn2)` by metis_tac[gas_origin_ptr_path_trans] >>
  qexistsl [`s2`,`G2`,`tn2`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> gvs[op_prov_def]) >>
  conj_tac >- (strip_tac >> gvs[entry_taint_def]) >>
  metis_tac[abi_decode_sim_trans, gas_path_mem_then, ADD]
QED
