Theory ctorDeployLoweringEntryCompletePrefix
Ancestors
 ctorDeployLoweringEntryArrayOps ctorDeployLoweringEntryCompleteScalar
 ctorAbiActualArrayPrepare ctorAbiActualArrayEntry ctorAbiActualArrayInvariant
 ctorDeployLoweringEntryArrayFrame ctorDeployLoweringEntryAllocation
 ctorDeployLoweringEntryRegistration ctorAbiActualFrame ctorAbiActualSites
 abiDecoderDynamicLoopSetup abiDecoderArrayHeader abiDecoderIndexInit abiDecoderArrayLoopInit
 abiDecoderReentry abiDecoderContract abiDecoderLoop abiDecoderVarSequence
 abiEncoderRegisteredEffect fragExec instIdxIndep emitHelperProps fragGasStraight fragGasPath
 venomExecSemantics venomState venomMemDefs compileEnv valueEncoding
 finite_map list words arithmetic rich_list emitHelper context exprLoweringProps venomInst valueEncodingProps

Theorem deploy_ctor_array_prefix_complete_reach:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+n*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [] initial actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_prefix_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all ctor_actual_array_prefix_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `frag_exec ctx st st' (\s. s = initial)
    (\t. fresh_vars_wrt limit_st t /\
      abi_decoder_address_frame st.cs_next_var initial t /\
      t.vs_labels = initial.vs_labels /\
      abi_encoder_registered_effect {} [] initial t /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
      t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
      t.vs_block_ctx = initial.vs_block_ctx) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, fresh_vars_wrt_def, abi_decoder_address_frame_def,
       eval_op_inst_idx, abi_encoder_registered_effect_def]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial result` >>
  qexists `result` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_array_count_header_complete_reach:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand cnt actual = SOME (abi_decode_load DLOAD p initial) /\
    mem_word_at d actual.vs_memory = abi_decode_load DLOAD p initial /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(d,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_count_header_reentry >> strip_tac >>
  drule ctor_actual_array_count_header_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand cnt t = SOME (abi_decode_load DLOAD p initial) /\
      mem_word_at d t.vs_memory = abi_decode_load DLOAD p initial /\
      fresh_vars_wrt limit_st t /\ abi_decode_frame d 32 initial t /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_labels = initial.vs_labels /\
      abi_encoder_registered_effect {} [(d,32)] initial t /\
      t.vs_allocas = initial.vs_allocas /\
      t.vs_alloca_next = initial.vs_alloca_next /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
      t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
      t.vs_block_ctx = initial.vs_block_ctx) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, fresh_vars_wrt_def, abi_decode_frame_def,
       eval_op_inst_idx, abi_encoder_registered_effect_def] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial result` >>
  qexists `result` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_index_init_ambient_code[local]:
 abi_decode_index_init st = (ip,st') ==>
 EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')
Proof
 simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
      fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
 simp[emitted_insts_def] >>
 pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
 simp[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def]
QED

val Ok = ``\k ctx func site ids D N d outsz next limit_st
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
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s /\
    s.vs_gas_readings = base.vs_gas_readings /\ s.vs_code = base.vs_code``;

Theorem deploy_ctor_array_index_complete_entry:
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
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t p. eval_operand ip t = SOME (n2w p) /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all deploy_ctor_array_index_observation >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule deploy_ctor_index_init_ambient_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\u. eval_operand ip u = SOME (n2w p) /\
      (^Ok) k ctx func site ids D N d outsz
        st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 u /\
      u.vs_outcomes = s.vs_outcomes /\ u.vs_tx_ctx = s.vs_tx_ctx /\
      u.vs_block_ctx = s.vs_block_ctx) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, eval_op_inst_idx, deploy_ctor_array_observation_inst_idx]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> qexists `p` >> simp[]
QED

Theorem deploy_ctor_array_header_index_complete_entry:
  abi_decode_array_header dst src DLOAD st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD p initial = n2w (LENGTH vs) /\
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
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_count_header_complete_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial header` >>
  `alloca_inv header /\ alloca_frontier_inv_from k ctx func site header /\
    ctor_actual_scratch func ids D N header /\ D+N <= header.vs_alloca_next` by
    metis_tac[deploy_ctor_array_allocation_state] >>
  `mload d header = n2w (LENGTH vs)` by fs[mem_word_at_eq_mload] >>
  `header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_index_complete_entry >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func header actual` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial header` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[(d,32)]`] >> simp[] >> rpt strip_tac >> decide_tac) >>
  `header.vs_call_ctx = initial.vs_call_ctx /\
    header.vs_data_section = initial.vs_data_section` by fs[abi_decode_frame_def] >>
  `(^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id p' initial 0 0 actual` by
    (irule deploy_ctor_array_observation_rebase >>
     qexistsl [`header_st.cs_next_var`, `header`] >> simp[abi_decode_frame_def] >>
     rpt strip_tac >>
     qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
     simp[abi_decoder_operand_live_def, eval_operand_def, IN_DEF]) >>
  qexistsl [`actual`, `p'`] >> simp[] >>
  irule abi_decode_sim_trans >> qexists `header` >> simp[]
QED

Theorem deploy_ctor_array_prefix_header_index_complete_entry:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\
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
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `guard_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_prefix_complete_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial guard` >>
  `guard.vs_allocas = initial.vs_allocas /\
    guard.vs_alloca_next = initial.vs_alloca_next` by fs[abi_decoder_address_frame_def] >>
  `alloca_inv guard /\ alloca_frontier_inv_from k ctx func site guard /\
    ctor_actual_scratch func ids D N guard /\ D+N <= guard.vs_alloca_next` by
    metis_tac[deploy_ctor_array_allocation_state] >>
  `eval_operand src guard = SOME (n2w sb) /\
    eval_operand dst guard = SOME (n2w d)` by
    fs[abi_decoder_address_frame_def] >>
  `guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `abi_decode_load DLOAD (n2w sb : bytes32) guard = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ initial = _` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_load_def, abi_decode_source_def] >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live guard_st.cs_next_var src /\
    abi_decoder_operand_live guard_st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  drule_all deploy_ctor_array_header_index_complete_entry >>
  disch_then (qspec_then `tv` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func guard actual` >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial guard` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  `guard.vs_call_ctx = initial.vs_call_ctx /\
    guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `(^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual` by
    (irule deploy_ctor_array_observation_rebase >>
     qexistsl [`guard_st.cs_next_var`, `guard`] >> simp[] >>
     rpt strip_tac >> irule ctor_actual_address_old_vars >>
     goal_assum (drule_at Any) >> qexists `st.cs_next_var` >> simp[]) >>
  qexistsl [`actual`, `slot`] >> simp[] >>
  irule abi_decode_sim_trans >> qexists `guard` >> simp[]
QED

Theorem deploy_ctor_array_prefix_complete_gas_path:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+n*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. gas_path ctx func initial 0 (OK actual) /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [] initial actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_prefix_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all ctor_actual_array_prefix_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY (\i. abi_decoder_reentry_opcode _) _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >>
     simp[abi_decoder_reentry_opcode_def]) >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    gvs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  drule_all concat_straight_gas_path >> strip_tac >>
  `abi_decode_sim ctx func initial
    (actual with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    metis_tac[gas_path_normal, abi_decode_sim_def] >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[fresh_vars_wrt_def, abi_decoder_address_frame_def,
       eval_op_inst_idx, abi_encoder_registered_effect_def]
QED

Theorem deploy_ctor_array_count_header_complete_gas_path:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. gas_path ctx func initial 0 (OK actual) /\
    eval_operand cnt actual = SOME (abi_decode_load DLOAD p initial) /\
    mem_word_at d actual.vs_memory = abi_decode_load DLOAD p initial /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(d,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_count_header_reentry >> strip_tac >>
  drule ctor_actual_array_count_header_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY (\i. abi_decoder_reentry_opcode _) _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >>
     simp[abi_decoder_reentry_opcode_def]) >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    gvs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  drule_all concat_straight_gas_path >> strip_tac >>
  `abi_decode_sim ctx func initial
    (actual with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    metis_tac[gas_path_normal, abi_decode_sim_def] >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def,
       eval_op_inst_idx, abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem deploy_ctor_array_index_complete_gas_path:
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
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t p. gas_path ctx func s 0 (OK t) /\ eval_operand ip t = SOME (n2w p) /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all deploy_ctor_array_index_observation >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule deploy_ctor_index_init_ambient_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY (\i. abi_decoder_reentry_opcode _) _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> disch_then (qspec_then `i` mp_tac) >>
     simp[abi_decoder_reentry_opcode_def]) >>
  `st'.cs_current_bb = st.cs_current_bb /\
   st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    gvs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_APPEND] >>
  drule_all concat_straight_gas_path >> strip_tac >>
  `abi_decode_sim ctx func s
    (t with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    metis_tac[gas_path_normal, abi_decode_sim_def] >>
  qexistsl [`t with vs_inst_idx := LENGTH st'.cs_current_insts`, `p`] >>
  fs[eval_op_inst_idx, deploy_ctor_array_observation_inst_idx]
QED

Theorem deploy_ctor_array_header_index_complete_gas_path:
  abi_decode_array_header dst src DLOAD st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD p initial = n2w (LENGTH vs) /\
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
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. gas_path ctx func initial 0 (OK actual) /\
    eval_operand ip actual = SOME (n2w slot) /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_count_header_complete_gas_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial header` >>
  `alloca_inv header /\ alloca_frontier_inv_from k ctx func site header /\
    ctor_actual_scratch func ids D N header /\ D+N <= header.vs_alloca_next` by
    metis_tac[deploy_ctor_array_allocation_state] >>
  `mload d header = n2w (LENGTH vs)` by fs[mem_word_at_eq_mload] >>
  `header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_index_complete_gas_path >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func header actual` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial header` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[(d,32)]`] >> simp[] >> rpt strip_tac >> decide_tac) >>
  `header.vs_call_ctx = initial.vs_call_ctx /\
    header.vs_data_section = initial.vs_data_section` by fs[abi_decode_frame_def] >>
  `(^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id p' initial 0 0 actual` by
    (irule deploy_ctor_array_observation_rebase >>
     qexistsl [`header_st.cs_next_var`, `header`] >> simp[abi_decode_frame_def] >>
     rpt strip_tac >>
     qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
     simp[abi_decoder_operand_live_def, eval_operand_def, IN_DEF]) >>
  `gas_path ctx func initial 0 (OK actual)` by
    (drule_all gas_path_then >> simp[]) >>
  qexistsl [`actual`, `p'`] >> simp[] >>
  irule abi_decode_sim_trans >> qexists `header` >> simp[]
QED

Theorem deploy_ctor_array_prefix_header_index_complete_gas_path:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\
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
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. gas_path ctx func initial 0 (OK actual) /\
    eval_operand ip actual = SOME (n2w slot) /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
    actual.vs_block_ctx = initial.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `guard_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_prefix_complete_gas_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial guard` >>
  `guard.vs_allocas = initial.vs_allocas /\
    guard.vs_alloca_next = initial.vs_alloca_next` by fs[abi_decoder_address_frame_def] >>
  `alloca_inv guard /\ alloca_frontier_inv_from k ctx func site guard /\
    ctor_actual_scratch func ids D N guard /\ D+N <= guard.vs_alloca_next` by
    metis_tac[deploy_ctor_array_allocation_state] >>
  `eval_operand src guard = SOME (n2w sb) /\
    eval_operand dst guard = SOME (n2w d)` by
    fs[abi_decoder_address_frame_def] >>
  `guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `abi_decode_load DLOAD (n2w sb : bytes32) guard = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ initial = _` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_load_def, abi_decode_source_def] >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live guard_st.cs_next_var src /\
    abi_decoder_operand_live guard_st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  drule_all deploy_ctor_array_header_index_complete_gas_path >>
  disch_then (qspec_then `tv` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func guard actual` >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial guard` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  `guard.vs_call_ctx = initial.vs_call_ctx /\
    guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `(^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual` by
    (irule deploy_ctor_array_observation_rebase >>
     qexistsl [`guard_st.cs_next_var`, `guard`] >> simp[] >>
     rpt strip_tac >> irule ctor_actual_address_old_vars >>
     goal_assum (drule_at Any) >> qexists `st.cs_next_var` >> simp[]) >>
  `gas_path ctx func initial 0 (OK actual)` by
    (drule_all gas_path_then >> simp[]) >>
  qexistsl [`actual`, `slot`] >> simp[] >>
  irule abi_decode_sim_trans >> qexists `guard` >> simp[]
QED
