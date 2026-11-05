(* Observation boundaries for actual-credit loop entry and terminal recovery. *)
Theory ctorAbiActualArrayEntry
Ancestors
  ctorAbiActualArrayFinite ctorAbiActualArrayInvariant ctorAbiActualArrayBody
  ctorAbiActualArrayPrepare abiDecoderArrayHeader abiDecoderArrayLoopInit
  ctorAbiActualLabelAlloc ctorAbiActualAlloc abiDecoderIndexInit
  ctorAbiActualSites ctorAbiActualMemory ctorAbiActualFrame
  allocaBudgetProps allocaFrontierBound venomMemDefs fragExec instIdxIndep
  exprLoweringProps rich_list emitHelperProps
  venomInst venomExecSemantics finite_map pred_set
  abiDecoderPrimitiveLoopEntry abiDecoderLoop abiDecoderExecution abiDecoderReentry
  abiDecoderLoopRegisters abiDecoderContract abiDecoderDynamicLoopSetup abiEncoderRegisteredEffect
  valueEncodingProps valueEncoding venomState compileEnv words list arithmetic

Theorem ctor_actual_array_observation_exit:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) s ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d s.vs_memory
Proof
  simp[ctor_actual_array_observation_def, val_in_memory_dynarray,
    mem_word_at_eq_mload]
QED

Theorem ctor_actual_array_observation_jump:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor (jump_to lbl s)
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st s` by fs[ctor_actual_array_observation_def] >>
  irule ctor_actual_array_observation_address >> simp[] >>
  qexistsl [`next`, `s`] >> asm_simp_tac bool_ss [] >>
  simp[abi_decoder_address_frame_def, abi_decoder_operand_jump,
    abi_decoder_fresh_jump, jump_to_def, abi_encoder_registered_effect_def]
QED

Theorem ctor_actual_array_entry_jump:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial i i s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix ==>
  ?h. ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial i i h /\
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s h
Proof
  strip_tac >> drule_all ctor_actual_array_observation_jump >>
  disch_then (qspec_then `hdr` assume_tac) >>
  drule_all abi_decoder_loop_entry_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists `jump_to hdr s` >> simp[jump_to_def]
QED

Theorem ctor_actual_index_limit_fresh:
  abi_decode_index_init st = (ip,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> drule ctor_actual_index_insts >> strip_tac >>
  `!n. limit_st.cs_next_var <= n ==>
    lookup_var (STRING #"%" (toString n)) t =
    lookup_var (STRING #"%" (toString n)) s` by
    (rpt strip_tac >> irule ctor_actual_sequence_var_frame >>
     qexists `emitted_insts st st'` >> simp[mk_inst_def, is_terminator_def] >>
     `st.cs_next_var <> n` by decide_tac >> simp[ASCIInumbersTheory.toString_inj]) >>
  fs[fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >>
  rpt strip_tac >> qpat_x_assum `!n. _ ==> _ = _` (qspec_then `n` mp_tac) >>
  simp[]
QED

Theorem ctor_actual_array_index_observation:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx func site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\
  mload d s = n2w (LENGTH vs) /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\
    ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `st.cs_next_id IN ids` by fs[ctor_actual_sites_def] >>
  drule_all ctor_actual_index_labels_narrow >> strip_tac >>
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
  qexistsl [`t`, `p`] >> simp[ctor_actual_array_observation_def, Once val_in_memory_def] >>
  conj_tac >- fs[mload_def, mem_bytes_at_def] >>
  rpt strip_tac >>
  `not_fresh_at st x` by fs[abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF] >>
  metis_tac[]
QED

Theorem ctor_actual_array_observation_inst_idx[simp]:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor (s with vs_inst_idx := k) <=>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s
Proof
  simp[ctor_actual_array_observation_def, alloca_inv_def,
    alloca_frontier_inv_def, remaining_alloca_budget_def,
    allocas_non_overlapping_def, alloca_next_valid_def,
    ctor_actual_scratch_def, fresh_vars_wrt_def, lookup_var_def,
    abi_encoder_registered_effect_def, mload_def]
QED

Theorem ctor_actual_array_index_entry:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts func)) /\
  st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx func site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ mload d s = n2w (LENGTH vs) /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t p. eval_operand ip t = SOME (n2w p) /\
    ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_index_observation >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\u. eval_operand ip u = SOME (n2w p) /\
      ctor_actual_array_observation ctx func site ids D N d outsz
        st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 u) (K F)` by
    (irule frag_exec_run_inst_seq >>
     fs[inst_extends_def, eval_op_inst_idx]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> qexists `p` >> simp[]
QED

Theorem ctor_actual_array_observation_rebase:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot prepared prefix cursor s /\
  earlier <= next /\
  prepared.vs_data_section = initial.vs_data_section /\
  prepared.vs_call_ctx = initial.vs_call_ctx /\
  prepared.vs_labels = initial.vs_labels /\
  (!x w. abi_decoder_older_vars earlier x /\ lookup_var x initial = SOME w ==>
    lookup_var x prepared = SOME w) /\
  abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial prepared ==>
  ctor_actual_array_observation ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor s
Proof
  simp_tac bool_ss [ctor_actual_array_observation_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial s` by
    (irule abi_encoder_registered_effect_trans >> qexists `prepared` >> simp[]) >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_older_vars next x` by
    (fs[abi_decoder_older_vars_def, IN_DEF] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem ctor_actual_array_allocation_state[local]:
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx func site t <=> alloca_frontier_inv ctx func site s) /\
  (ctor_actual_scratch func ids D N t <=> ctor_actual_scratch func ids D N s)
Proof
  strip_tac >>
  simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_frontier_inv_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
  asm_rewrite_tac[]
QED

Theorem ctor_actual_array_header_index_entry:
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
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st header_st func /\ fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    ctor_actual_array_observation ctx func site ids D N d outsz
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
  `alloca_inv header /\ alloca_frontier_inv ctx func site header /\
    ctor_actual_scratch func ids D N header /\ D+N <= header.vs_alloca_next` by
    metis_tac[ctor_actual_array_allocation_state] >>
  `mload d header = n2w (LENGTH vs)` by fs[mem_word_at_eq_mload] >>
  `header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all ctor_actual_array_index_entry >>
  disch_then (qspecl_then [`tv`, `outsz`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func header actual` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial header` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[(d,32)]`] >> simp[] >> rpt strip_tac >> decide_tac) >>
  `header.vs_call_ctx = initial.vs_call_ctx /\
    header.vs_data_section = initial.vs_data_section` by fs[abi_decode_frame_def] >>
  `ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id p' initial 0 0 actual` by
    (irule ctor_actual_array_observation_rebase >>
     qexistsl [`header_st.cs_next_var`, `header`] >> simp[abi_decode_frame_def] >>
     rpt strip_tac >>
     qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
     simp[abi_decoder_operand_live_def, eval_operand_def, IN_DEF]) >>
  qexistsl [`actual`, `p'`] >> simp[] >>
  irule abi_decode_sim_trans >> qexists `header` >> simp[]
QED

Theorem ctor_actual_array_observation_self:
  ctor_actual_array_observation ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor s ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot s prefix cursor s
Proof
  simp_tac bool_ss [ctor_actual_array_observation_def] >> strip_tac >>
  simp[abi_encoder_registered_effect_refl]
QED

Theorem ctor_actual_array_prefix_header_index_entry:
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
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    ctor_actual_array_observation ctx func site ids D N d outsz
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
  drule_all ctor_actual_array_prefix_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial guard` >>
  `guard.vs_allocas = initial.vs_allocas /\
    guard.vs_alloca_next = initial.vs_alloca_next` by fs[abi_decoder_address_frame_def] >>
  `alloca_inv guard /\ alloca_frontier_inv ctx func site guard /\
    ctor_actual_scratch func ids D N guard /\ D+N <= guard.vs_alloca_next` by
    metis_tac[ctor_actual_array_allocation_state] >>
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
  drule_all ctor_actual_array_header_index_entry >>
  disch_then (qspec_then `tv` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func guard actual` >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial guard` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  `guard.vs_call_ctx = initial.vs_call_ctx /\
    guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual` by
    (irule ctor_actual_array_observation_rebase >>
     qexistsl [`guard_st.cs_next_var`, `guard`] >> simp[] >>
     rpt strip_tac >> irule ctor_actual_address_old_vars >>
     goal_assum (drule_at Any) >> qexists `st.cs_next_var` >> simp[]) >>
  qexistsl [`actual`, `slot`] >> simp[] >>
  irule abi_decode_sim_trans >> qexists `guard` >> simp[]
QED
