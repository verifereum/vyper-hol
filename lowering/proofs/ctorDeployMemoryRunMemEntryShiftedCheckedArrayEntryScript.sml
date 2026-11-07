Theory ctorDeployMemoryRunMemEntryShiftedCheckedArrayEntry
Ancestors
  ctorDeployMemoryRunMemEntryShiftedIndex ctorDeployMemoryRunMemEntryArraySteps
  ctorDeployMemoryRunMemEntryShiftedObservation ctorDeployMemoryRunMemEntryShiftedFrame
  ctorDeployMemoryFrontier ctorAbiActualAlloc ctorAbiActualFrame ctorAbiActualSites
  valueEncodingProps abiDecoderContract abiDecoderArrayLoopInit
  abiDecoderIndexInit allocaFrontierBound allocaBudgetProps abiDecoderExecution
  abiDecoderLoop abiDecoderVarSequence abiDecoderReentry abiDecoderDynamicLoopSetup
  ctorDeployMemoryRunMemEntryWord emitHelperProps fragExec
  abiEncoderRegisteredEffect instIdxIndep fragGasPathMem allocaHistory
  fragExecMem instMemFrontier memSafeRun venomExecSemantics venomInst venomState venomMemDefs
  exprLoweringProps venomInstProofs1 rich_list list words arithmetic

val O = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s``;

Theorem ctor_checked_index_sequence_mem_ok_from:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule ctor_actual_index_insts >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by (first_x_assum irule >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id IN ids` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all ctor_actual_word_alloca_run_from >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `p < dimword (:256)` by (irule ctor_actual_index_slot_bound_from >> metis_tac[mk_inst_def]) >>
  `p+32 <= t.vs_alloca_next` by
    (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[Abbr `inst`, mk_inst_def]) >>
  simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
  gvs[Abbr `inst`] >>
  pure_once_rewrite_tac[GSYM mk_inst_def] >>
  rewrite_tac[run_inst_seq_mem_ok_last] >> conj_tac
  >- simp[below_frontier_MSTORE, w2n_n2w] >>
  simp[memSafeRunTheory.inst_dload_in_section_def, mk_inst_def]
QED

Theorem ctor_checked_array_index_entry_from:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ mload d s = n2w (LENGTH vs) /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func s ==>
  ?t p. eval_operand ip t = SOME (n2w p) /\
    (^O) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    gas_path_mem ctx func s 0 (OK t) /\
    t.vs_gas_readings = s.vs_gas_readings /\ alloca_history func t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_index_observation_from >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  `st.cs_next_id IN ids` by fs[ctor_actual_sites_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule ctor_checked_index_sequence_mem_ok_from >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule ctor_actual_index_insts >> strip_tac >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
    emitted_insts st st' = code` by
    (fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
    t.vs_gas_readings = s.vs_gas_readings /\
    alloca_history func (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (`lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all ctor_checked_index_endpoint >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[] >> gvs[]) >>
  `~t.vs_halted` by (drule_all ctor_actual_index_var_frame >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_current_bb` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by gvs[mk_inst_def, is_terminator_def] >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  qexistsl [`t with vs_inst_idx := LENGTH st'.cs_current_insts`, `p`] >>
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem ctor_checked_array_header_index_entry_from:
  abi_decode_array_header dst src DLOAD st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st header_st func /\ fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func initial ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    (^O) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `d+32 <= initial.vs_alloca_next` by decide_tac >>
  drule_all ctorDeployMemoryRunMemEntryArrayStepsTheory.ctor_checked_array_count_header_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial header` >>
  `alloca_inv header /\ alloca_frontier_inv_from k ctx func site header /\
    ctor_actual_scratch func ids D N header /\ D+N <= header.vs_alloca_next` by
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     qpat_x_assum `alloca_frontier_inv_from k ctx func site initial` mp_tac >>
     qpat_x_assum `ctor_actual_scratch func ids D N initial` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_from_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `mload d header = n2w (LENGTH vs)` by fs[mem_word_at_eq_mload] >>
  `header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all ctor_checked_array_index_entry_from >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func header actual` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial header` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[(d,32)]`] >> simp[] >> rpt strip_tac >> decide_tac) >>
  `header.vs_call_ctx = initial.vs_call_ctx /\
    header.vs_data_section = initial.vs_data_section` by fs[abi_decode_frame_def] >>
  `(^O) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id p initial 0 0 actual` by
    (irule ctor_actual_array_observation_rebase_from >>
     qexistsl [`header_st.cs_next_var`, `header`] >> simp[abi_decode_frame_def] >>
     rpt strip_tac >>
     qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
     simp[abi_decoder_operand_live_def, eval_operand_def, IN_DEF]) >>
  qexistsl [`actual`, `p`] >> simp[] >>
  conj_tac >- (irule abi_decode_sim_trans >> qexists `header` >> simp[]) >>
  drule_all gas_path_mem_then >> simp[]
QED
