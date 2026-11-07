(* Actual constructor index slots above a reserved-memory frontier. *)
Theory ctorDeployMemoryRunMemEntryShiftedIndex
Ancestors
  ctorDeployMemoryRunMemEntryShiftedAlloc ctorDeployMemoryRunMemEntryShiftedFrame
  ctorDeployMemoryFrontier ctorDeployMemoryRunMemEntryShiftedObservation
  ctorAbiActualAlloc ctorAbiActualArrayEntry ctorAbiActualFrame ctorAbiActualMemory
  actualAllocExec abiEncoderPrimitiveEffect abiEncoderRegisteredEffect
  ctorAbiActualNarrow ctorAbiActualObservations ctorAbiActualLabelAlloc ctorAbiActualSites
  abiDecoderIndexInit allocaFrontierBound allocaBudgetProps
  context compileEnv emitHelper emitHelperProps exprLoweringProps rich_list
  abiDecoderVarSequence valueEncoding abiDecoderContract
  fragExec instIdxIndep abiDecoderExecution abiDecoderLoop abiDecoderArrayHeader
  abiDecoderArrayLoopInit ctorAbiActualArrayPrepare abiDecoderDynamicLoopSetup
  abiDecoderLoopRegisters valueEncodingProps
  venomMemProps venomInstProofs1 abiDecoderReentry
  venomMemDefs venomState venomInst venomExecSemantics
  finite_map pred_set list arithmetic words

Theorem ctor_actual_word_alloca_run_from:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] /\
  inst.inst_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  ?t p.
    step_inst_base inst s = OK t /\
    eval_operand (Var out) t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    regions_disjoint (d,n) (p,32) /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv_from k ctx fn site t /\
    abi_encoder_registered_effect ids outs s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (drule_all actual_word_alloca_fresh_run_from >> strip_tac >>
      `alloca_inv t` by (irule actual_alloca_slots_preserved >> metis_tac[]) >>
      `alloca_frontier_inv_from k ctx fn site t` by
        (irule actual_alloca_frontier_preserved_from >> metis_tac[]) >>
      qexistsl [`t`, `s.vs_alloca_next`] >>
      simp[FLOOKUP_UPDATE] >>
      conj_tac
      >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      conj_tac >- simp[regions_disjoint_def] >>
      conj_tac >- (irule ctor_actual_scratch_fresh >> simp[]) >>
      simp[abi_encoder_registered_effect_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `i = inst.inst_id` >> gvs[]) >>
  PairCases_on `x` >>
  `x1 = 32 /\ regions_disjoint (d,n) (x0,x1)` by
    (gvs[ctor_actual_scratch_def] >> metis_tac[]) >>
  gvs[] >> drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `alloca_inv t` by (irule actual_alloca_slots_preserved >> metis_tac[]) >>
  `alloca_frontier_inv_from k ctx fn site t` by
    (irule actual_alloca_frontier_preserved_from >> metis_tac[]) >>
  qexistsl [`t`, `x0`] >> simp[] >>
  conj_tac >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule abi_encoder_registered_update_var
QED

Theorem ctor_actual_index_slot_bound_from:
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas id = SOME (p,32) ==>
  p < dimword (:256)
Proof
  strip_tac >> drule_all alloca_frontier_inv_from_word_bound >> strip_tac >>
  `p+32 <= s.vs_alloca_next` by
    (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >> decide_tac
QED

Theorem ctor_actual_index_sequence_from:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv_from k ctx fn site t /\
    abi_encoder_registered_effect ids outs s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >> drule ctor_actual_index_insts >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  qabbrev_tac `inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `MEM inst (fn_insts fn)` by (first_x_assum irule >> simp[Abbr `inst`]) >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id IN ids` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all ctor_actual_word_alloca_run_from >>
  disch_then (qspec_then `outs` strip_assume_tac) >>
  rename1 `step_inst_base inst s = OK allocated` >>
  `p < dimword (:256)` by (irule ctor_actual_index_slot_bound_from >> metis_tac[mk_inst_def]) >>
  `run_inst_seq (emitted_insts st st') s = OK (mstore p 0w allocated)` by
    (qpat_x_assum `step_inst_base inst s = OK allocated` mp_tac >>
     simp_tac bool_ss [Abbr `inst`] >> strip_tac >>
     asm_simp_tac bool_ss [run_inst_seq_def] >>
     simp[step_inst_base_def, exec_write2_def, mk_inst_def,
       eval_operand_def, w2n_n2w]) >>
  `abi_encoder_registered_effect ids outs allocated (mstore p 0w allocated)` by
    (irule abi_encoder_registered_slot_store >>
     qexists `st.cs_next_id` >> gvs[Abbr `inst`, mk_inst_def]) >>
  `alloca_frontier_inv_from k ctx fn site (mstore p 0w allocated) =
   alloca_frontier_inv_from k ctx fn site allocated` by
    simp[NoAsms, alloca_frontier_inv_from_def, remaining_alloca_budget_def] >>
  qexistsl [`mstore p 0w allocated`, `p`] >>
  simp[abi_decoder_operand_mstore, mload_mstore_same,
       abi_encoder_primitive_alloca_inv] >>
  conj_tac >- gvs[Abbr `inst`, mk_inst_def] >>
  irule abi_encoder_registered_effect_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_actual_index_labels_narrow_from:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ids /\
  ctor_actual_scratch fn ids d n s /\ d+n <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ctor_actual_scratch fn ids d n t /\
    alloca_inv t /\ alloca_frontier_inv_from k ctx fn site t /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `ctor_actual_scratch fn {st.cs_next_id} d n s` by
    (irule ctor_actual_scratch_restrict >> qexists `ids` >> simp[]) >>
  mp_tac (Q.INST [`ids` |-> `{st.cs_next_id}`, `outs` |-> `[]`]
    ctor_actual_index_sequence_from) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all ctor_actual_index_sequence_from >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by
    (drule ctor_actual_index_insts >> simp[mk_inst_def, abi_decoder_reentry_opcode_def]) >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  metis_tac[]
QED

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

Theorem ctor_actual_array_index_observation_from:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\
  mload d s = n2w (LENGTH vs) /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\
    (^O) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `st.cs_next_id IN ids` by fs[ctor_actual_sites_def] >>
  drule_all ctor_actual_index_labels_narrow_from >> strip_tac >>
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
  qexistsl [`t`, `p`] >> simp[Once val_in_memory_def] >>
  conj_tac >- fs[mload_def, mem_bytes_at_def] >>
  rpt strip_tac >>
  `not_fresh_at st x` by fs[abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF] >>
  metis_tac[]
QED

Theorem ctor_actual_array_index_entry_from:
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
    (^O) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_index_observation_from >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\u. eval_operand ip u = SOME (n2w p) /\
      (^O) k ctx func site ids D N d outsz
        st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 u) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, eval_op_inst_idx]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> qexists `p` >> simp[]
QED

Theorem ctor_actual_array_allocation_state_from[local]:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv_from k ctx func site t <=> alloca_frontier_inv_from k ctx func site s) /\
  (ctor_actual_scratch func ids D N t <=> ctor_actual_scratch func ids D N s)
Proof
  strip_tac >>
  simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_frontier_inv_from_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
  asm_rewrite_tac[]
QED

Theorem ctor_actual_array_header_index_entry_from:
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
    (^O) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `header_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all ctor_actual_array_count_header_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial header` >>
  `alloca_inv header /\ alloca_frontier_inv_from k ctx func site header /\
    ctor_actual_scratch func ids D N header /\ D+N <= header.vs_alloca_next` by
    metis_tac[ctor_actual_array_allocation_state_from] >>
  `mload d header = n2w (LENGTH vs)` by fs[mem_word_at_eq_mload] >>
  `header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all ctor_actual_array_index_entry_from >>
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
      st.cs_next_var limit_st tv vs header_st.cs_next_id p' initial 0 0 actual` by
    (irule ctor_actual_array_observation_rebase_from >>
     qexistsl [`header_st.cs_next_var`, `header`] >> simp[abi_decode_frame_def] >>
     rpt strip_tac >>
     qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
     simp[abi_decoder_operand_live_def, eval_operand_def, IN_DEF]) >>
  qexistsl [`actual`, `p'`] >> simp[] >>
  irule abi_decode_sim_trans >> qexists `header` >> simp[]
QED
