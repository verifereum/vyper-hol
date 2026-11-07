Theory ctorDeployMemoryRunMemEntryArrayEntryWorld
Ancestors
  ctorDeployMemoryRunMemEntryShiftedCheckedArrayEntry
  ctorDeployMemoryRunMemEntrySequenceWorld
  ctorAbiActualArrayPrepare ctorAbiActualArrayInvariant
  ctorDeployMemoryRunMemEntryCompositeSetup
  ctorDeployMemoryRunMemEntryArraySteps
  ctorDeployMemoryRunMemEntryShiftedIndex
  ctorDeployMemoryRunMemEntryShiftedObservation
  ctorDeployMemoryRunMemEntryShiftedFrame ctorDeployMemoryFrontier
  ctorAbiActualAlloc ctorAbiActualFrame ctorAbiActualSites
  valueEncodingProps abiDecoderContract abiDecoderArrayLoopInit
  abiDecoderIndexInit allocaFrontierBound allocaBudgetProps abiDecoderExecution
  abiDecoderLoop abiDecoderVarSequence abiDecoderReentry abiDecoderDynamicLoopSetup
  ctorDeployMemoryRunMemEntryWord emitHelperProps fragExec
  abiEncoderRegisteredEffect instIdxIndep fragGasPathMem allocaHistory
  fragExecMem instMemFrontier memSafeRun venomExecSemantics venomInst venomState venomMemDefs
  exprLoweringProps compileEnv venomInstProofs1 rich_list list words arithmetic

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

val Ow = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    (^O) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot base prefix cursor s /\
    s.vs_tx_ctx = base.vs_tx_ctx /\ s.vs_block_ctx = base.vs_block_ctx /\
    s.vs_outcomes = base.vs_outcomes``;

Theorem ctor_array_observation_index_fields[local]:
  (mload d (s with vs_inst_idx := n) = mload d s) /\
  (alloca_frontier_inv_from k ctx func site (s with vs_inst_idx := n) =
    alloca_frontier_inv_from k ctx func site s) /\
  (ctor_actual_scratch func ids D N (s with vs_inst_idx := n) =
    ctor_actual_scratch func ids D N s) /\
  (fresh_vars_wrt st (s with vs_inst_idx := n) = fresh_vars_wrt st s) /\
  (lookup_var x (s with vs_inst_idx := n) = lookup_var x s)
Proof
  simp[NoAsms, mload_def, alloca_frontier_inv_from_def,
    remaining_alloca_budget_def, ctor_actual_scratch_def,
    fresh_vars_wrt_def, lookup_var_def]
QED

Theorem ctor_checked_array_index_world_entry_from:
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
    (^Ow) k ctx func site ids D N d outsz
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
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    simp[mk_inst_def, abi_decoder_reentry_opcode_def] >>
  drule_all ctor_decoder_sequence_context_world >> strip_tac >>
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
  fs[instIdxIndepTheory.eval_op_inst_idx, ctor_array_observation_index_fields] >>
  fs[abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem ctor_checked_array_count_header_world_reach:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  d+32 <= initial.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ alloca_history func initial ==>
  ?actual. eval_operand cnt actual = SOME (abi_decode_load DLOAD (n2w sb : bytes32) initial) /\
    mem_word_at d actual.vs_memory = abi_decode_load DLOAD (n2w sb : bytes32) initial /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(d,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual /\
    actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
    actual.vs_outcomes = initial.vs_outcomes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_count_header_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule_all ctor_actual_array_count_header_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ctor_decoder_sequence_context_world >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (irule ctor_checked_array_count_header_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _ /\ _ /\ ~is_alloca_op _` drule >>
     qpat_x_assum `!i. MEM i _ ==> abi_decoder_reentry_opcode _` drule >>
     simp[abi_decoder_reentry_opcode_def, is_alloca_op_def] >>
     rpt strip_tac >> gvs[]) >>
  `actual.vs_current_bb = initial.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_current_bb` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  `actual.vs_halted = initial.vs_halted` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_halted` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[instIdxIndepTheory.eval_op_inst_idx, abi_decode_frame_def,
    fresh_vars_wrt_def, lookup_var_def, abi_encoder_registered_effect_def] >>
  metis_tac[]
QED

Theorem ctor_checked_array_prefix_world_reach:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+n*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ alloca_history func initial ==>
  ?actual. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [] initial actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual /\
    actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
    actual.vs_outcomes = initial.vs_outcomes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_prefix_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all ctor_actual_array_prefix_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ctor_decoder_sequence_context_world >> strip_tac >>
  `actual.vs_allocas = initial.vs_allocas` by fs[abi_decoder_address_frame_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (irule ctor_checked_array_prefix_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> ~is_alloca_op _ /\ _` drule >>
     qpat_x_assum `!i. MEM i _ ==> abi_decoder_reentry_opcode _` drule >>
     simp[abi_decoder_reentry_opcode_def, is_alloca_op_def] >>
     rpt strip_tac >> gvs[]) >>
  `actual.vs_current_bb = initial.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_current_bb` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  `actual.vs_halted = initial.vs_halted` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_halted` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st st'` >> simp[] >> rpt strip_tac >>
     `~is_terminator i.inst_opcode` by (fs[EVERY_MEM] >> metis_tac[]) >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
  drule_all ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[instIdxIndepTheory.eval_op_inst_idx, abi_decoder_address_frame_def,
    fresh_vars_wrt_def, lookup_var_def, abi_encoder_registered_effect_def] >>
  metis_tac[]
QED

Theorem ctor_checked_array_header_index_world_entry_from:
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
    (^Ow) k ctx func site ids D N d outsz
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
  drule_all ctor_checked_array_count_header_world_reach >>
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
  drule_all ctor_checked_array_index_world_entry_from >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func header actual` >>
  fs[] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >> fs[] >>
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
  qpat_x_assum `eval_operand ip actual = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qexistsl [`actual`, `p`] >> fs[] >>
  conj_tac >- (irule abi_decode_sim_trans >> qexists `header` >> simp[]) >>
  drule_all gas_path_mem_then >> simp[]
QED

Theorem ctor_checked_array_prefix_header_index_world_entry_from:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+LENGTH vs*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func initial ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    (^Ow) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `guard_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all ctor_checked_array_prefix_world_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial guard` >>
  `guard.vs_allocas = initial.vs_allocas /\
    guard.vs_alloca_next = initial.vs_alloca_next` by fs[abi_decoder_address_frame_def] >>
  `alloca_inv guard /\ alloca_frontier_inv_from k ctx func site guard /\
    ctor_actual_scratch func ids D N guard /\ D+N <= guard.vs_alloca_next` by
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     qpat_x_assum `alloca_frontier_inv_from k ctx func site initial` mp_tac >>
     qpat_x_assum `ctor_actual_scratch func ids D N initial` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_from_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `eval_operand src guard = SOME (n2w sb) /\
    eval_operand dst guard = SOME (n2w d)` by fs[abi_decoder_address_frame_def] >>
  `guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `sb+32 <= LENGTH guard.vs_data_section` by simp[] >>
  `abi_decode_load DLOAD (n2w sb : bytes32) guard = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ initial = _` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_load_def, abi_decode_source_def] >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live guard_st.cs_next_var src /\
    abi_decoder_operand_live guard_st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  drule_all ctor_checked_array_header_index_world_entry_from >>
  disch_then (qspec_then `tv` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func guard actual` >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial guard` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  `guard.vs_call_ctx = initial.vs_call_ctx /\
    guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `(^O) k ctx func site ids D N d outsz
      guard_st.cs_next_var limit_st tv vs header_st.cs_next_id slot guard 0 0 actual` by (fs[] >> metis_tac[]) >>
  drule_at (Pat `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ctor_actual_array_observation_rebase_from >>
  disch_then (qspecl_then [`initial`, `st.cs_next_var`] mp_tac) >>
  (impl_tac >- (simp[] >>
    rpt strip_tac >> irule ctor_actual_address_old_vars >>
    goal_assum (drule_at Any) >> qexists `st.cs_next_var` >> simp[])) >>
  disch_tac >>
  qpat_x_assum `eval_operand ip actual = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists `guard` >> simp[]) >>
  `gas_path_mem ctx func initial 0 (OK actual)` by
    (drule_all gas_path_mem_then >> simp[]) >>
  qexistsl [`actual`, `slot`] >> fs[] >> metis_tac[]
QED
