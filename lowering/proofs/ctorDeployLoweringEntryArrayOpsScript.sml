(* Operational boundaries for shifted constructor array entry. *)
Theory ctorDeployLoweringEntryArrayOps
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployLoweringEntryArrayFrame ctorDeployLoweringEntryAllocation
  ctorDeployLoweringEntryRegistration ctorAbiActualArrayEntry
  ctorAbiActualArrayPrepare ctorAbiActualArrayInvariant ctorAbiActualFrame ctorAbiActualSites abiDecoderPrimitiveLoopEntry
  ctorAbiActualAlloc ctorAbiActualMemory ctorAbiActualWorld ctorAbiActualNarrow
  abiDecoderLoopRegisters abiDecoderExecution abiDecoderArrayBackedge
  pred_set valueEncoding valueEncodingProps
  abiDecoderIndexInit fragExec instIdxIndep abiDecoderLoop emitHelperProps
  abiDecoderArrayLoopInit abiDecoderArrayHeader abiDecoderVarSequence abiDecoderDynamicLoopSetup
  ctorDeployMemoryFrontier allocaFrontierBound allocaBudgetProps
  abiDecoderReentry abiDecoderContract abiEncoderRegisteredEffect
  venomMemDefs venomState venomExecSemantics compileEnv finite_map list words arithmetic

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

Theorem deploy_ctor_array_observation_inst_idx[simp]:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor (s with vs_inst_idx := idx) <=>
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s
Proof
  BETA_TAC >>
  simp[alloca_inv_def, alloca_frontier_inv_from_def, remaining_alloca_budget_def,
    allocas_non_overlapping_def, alloca_next_valid_def,
    ctor_actual_scratch_def, fresh_vars_wrt_def, lookup_var_def,
    abi_encoder_registered_effect_def, mload_def]
QED

Theorem deploy_ctor_array_observation_jump:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s ==>
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor (jump_to lbl s)
Proof
  BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rpt conj_tac >>
  simp_tac (srw_ss()) [jump_to_def, mload_def, lookup_var_def,
    alloca_inv_def, alloca_frontier_inv_from_def, remaining_alloca_budget_def,
    allocas_non_overlapping_def, alloca_next_valid_def, ctor_actual_scratch_def,
    fresh_vars_wrt_def, abi_encoder_registered_effect_def] >>
  first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss())
    [mload_def, lookup_var_def, alloca_inv_def, alloca_frontier_inv_from_def,
     remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def,
     ctor_actual_scratch_def, fresh_vars_wrt_def, abi_encoder_registered_effect_def])
QED

Theorem deploy_ctor_array_entry_jump:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial i i s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix ==>
  ?h. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial i i h /\
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s h
Proof
  strip_tac >> drule_all deploy_ctor_array_observation_jump >>
  disch_then (qspec_then `hdr` assume_tac) >>
  drule_all abi_decoder_loop_entry_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists `jump_to hdr s` >> simp[jump_to_def]
QED

Theorem deploy_ctor_array_index_observation:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ mload d s = n2w (LENGTH vs) /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\
    (^Ok) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `st.cs_next_id IN ids` by fs[ctor_actual_sites_def] >>
  drule_all deploy_ctor_index_labels_narrow >> strip_tac >>
  `fresh_vars_wrt limit_st t` by (irule ctor_actual_index_limit_fresh >> metis_tac[]) >>
  drule_all ctor_actual_index_var_frame >> strip_tac >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (irule ctor_actual_registered_window >>
     qexistsl [`{st.cs_next_id}`, `[]`] >> asm_simp_tac bool_ss [] >>
     simp[] >> rpt strip_tac >>
     irule (cj 2 ctor_actual_sites_scratch_contained) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
     qexistsl [`ids`, `D`, `func`, `ids`, `N`] >> simp[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{st.cs_next_id}`, `[]`] >> simp[SUBSET_DEF]) >>
  qexistsl [`t`, `p`] >> BETA_TAC >> simp[Once val_in_memory_def] >>
  conj_tac >- fs[mload_def, mem_bytes_at_def] >>
  rpt strip_tac >>
  `not_fresh_at st x` by fs[abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF] >>
  metis_tac[]
QED

Theorem deploy_ctor_array_index_entry:
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
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all deploy_ctor_array_index_observation >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\u. eval_operand ip u = SOME (n2w p) /\
      (^Ok) k ctx func site ids D N d outsz
        st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 u) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, eval_op_inst_idx, deploy_ctor_array_observation_inst_idx]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> qexists `p` >> simp[]
QED

Theorem deploy_ctor_array_count_header_reach:
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
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_count_header_reentry >> strip_tac >>
  drule ctor_actual_array_count_header_code >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
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
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, fresh_vars_wrt_def, abi_decode_frame_def,
       eval_op_inst_idx, abi_encoder_registered_effect_def] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial result` >>
  qexists `result` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_array_prefix_reach:
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
    actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_prefix_reentry >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all ctor_actual_array_prefix_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    fs[EVERY_CONJ] >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `frag_exec ctx st st' (\s. s = initial)
    (\t. fresh_vars_wrt limit_st t /\
      abi_decoder_address_frame st.cs_next_var initial t /\
      t.vs_labels = initial.vs_labels /\
      abi_encoder_registered_effect {} [] initial t /\
      t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, fresh_vars_wrt_def, abi_decoder_address_frame_def,
       eval_op_inst_idx, abi_encoder_registered_effect_def]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >>
  strip_tac >> rename1 `abi_decode_sim ctx func initial result` >>
  qexists `result` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_array_header_index_entry:
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
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_count_header_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial header` >>
  `alloca_inv header /\ alloca_frontier_inv_from k ctx func site header /\
    ctor_actual_scratch func ids D N header /\ D+N <= header.vs_alloca_next` by
    metis_tac[deploy_ctor_array_allocation_state] >>
  `mload d header = n2w (LENGTH vs)` by fs[mem_word_at_eq_mload] >>
  `header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_index_entry >>
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

Theorem deploy_ctor_array_prefix_header_index_entry:
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
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `guard_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_prefix_reach >>
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
  drule_all deploy_ctor_array_header_index_entry >>
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

Theorem deploy_ctor_array_observation_address:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  abi_decoder_address_frame body_next s t /\ next <= body_next /\
  fresh_vars_wrt limit_st t /\ t.vs_labels = s.vs_labels /\
  abi_encoder_registered_effect {} [] s t /\
  t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code ==>
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor t
Proof
  BETA_TAC >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    fs[abi_decoder_address_frame_def] >>
  `alloca_inv t = alloca_inv s /\
   alloca_frontier_inv_from k ctx func site t = alloca_frontier_inv_from k ctx func site s /\
   ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s` by
    metis_tac[deploy_ctor_array_allocation_state] >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[]`] >> simp[]) >>
  fs[abi_decoder_address_frame_def, mload_def] >> simp[] >>
  reverse conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
  rpt strip_tac >>
  `lookup_var x s = SOME w` by metis_tac[] >>
  `abi_decoder_operand_live body_next (Var x)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF] >>
     metis_tac[LESS_EQ_TRANS]) >>
  qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
  simp[eval_operand_def]
QED

Theorem deploy_ctor_array_header_observation:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  next <= first /\ first+4 <= limit_st.cs_next_var ==>
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s))
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st s` by fs[] >>
  drule_all abi_decoder_header_registers >> strip_tac >>
  qabbrev_tac `t = jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
    (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
    (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  `abi_decoder_address_frame first s t /\ t.vs_labels = s.vs_labels /\
   fresh_vars_wrt limit_st t` by
    (simp[Abbr `t`, abi_decoder_address_frame_def, abi_decoder_operand_jump,
      abi_decoder_fresh_jump] >>
     conj_tac >- simp[abi_decode_header_state_def, jump_to_def, update_var_def] >>
     simp[abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  `abi_encoder_registered_effect {} [] s t` by
    (irule ctor_actual_empty_effect >>
     simp[Abbr `t`, abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  `t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code` by
    simp[Abbr `t`, abi_decode_header_state_def, jump_to_def, update_var_def] >>
  irule deploy_ctor_array_observation_address >>
  asm_simp_tac bool_ss [] >> qexistsl [`first`, `s`] >>
  asm_simp_tac bool_ss [] >> fs[]
QED

Theorem deploy_ctor_array_header_run:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  abi_decode_loop_cfg func hdr body_lbl exit_lbl hid ip src DLOAD
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  next <= first /\ first+4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME srcaddr /\
  abi_decode_load DLOAD srcaddr s = n2w (LENGTH vs) /\
  slot < dimword (:256) /\ LENGTH vs < dimword (:256) ==>
  ?h. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h
Proof
  strip_tac >>
  `j <= LENGTH vs /\ mload slot s = n2w j` by fs[] >>
  `abi_decode_loop_ready hdr ip src DLOAD (n2w slot) srcaddr (LENGTH vs) j s` by
    simp[abi_decode_loop_ready_def, w2n_n2w] >>
  `src <> Var (STRING #"%" (toString first))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `STRING #"%" (toString first) <> STRING #"%" (toString (first+1))` by simp[] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_ready_header_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all deploy_ctor_array_header_observation >> strip_tac >>
  qexists `jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED
