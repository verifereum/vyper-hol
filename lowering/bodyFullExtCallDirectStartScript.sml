Theory bodyFullExtCallDirectStart
Ancestors
  bodyFullExtCallBufferSetup bodyFullExtCallDirectPhase bodyFullExtCallDirectWindows
  abiEncodeValuesPhases abiBuiltinAllocation abiEncoderWindowPhase
  abiEncoderRegisteredEffect abiEncoderWindowContract entryDecodeStructure
  stateRelProj exprLoweringProps exprSimHypsDefs bodyPtrDefs loweringPosts
  loweringStateRelDefs vyperStorageFootprint context compileEnv fragExec
  fragGasOriginPtr emitHelperProps venomState venomInst ptrDiscipline
  words finite_map pred_set list arithmetic pair
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

(* Nonempty external-call requests use the space after the selector in
   the same allocation. This is the initial frame for every encoder row. *)
Theorem extcall_direct_request_start:
  compile_alloc_buffer capacity se = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand;Lit (calldata_method_id selector)] sb = ((),sm) /\
  emit_op ADD [ba.buf_operand;Lit 32w] sm = (payload,st) /\
  fn_has_code se sb func /\ fn_has_code sb sm func /\ fn_has_code sm st func /\
  fn_inst_ids_distinct func /\ LENGTH selector = 4 /\ 32 <= capacity /\ capacity < dimword (:256) /\
  local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?r p w t G' tn' inst.
    ba.buf_operand = Var r /\ payload = Var p /\ not_fresh_at st r /\ not_fresh_at st p /\
    lookup_var r t = SOME w /\ ptr_covers G' tn' r t capacity /\
    eval_operand payload t = SOME (n2w (w2n w+32)) /\ ptr_covers G' tn' p t (capacity-32) /\
    FLOOKUP t.vs_allocas se.cs_next_id = SOME (w2n w,capacity) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = se.cs_next_id /\ inst.inst_outputs = [r] /\
    not_local_ptr ce ee.scopes r /\ se.cs_next_id < st.cs_next_id /\
    lo <= w2n w /\ w2n w + capacity <= t.vs_alloca_next /\
    read_memory (w2n w+28) 4 t = selector /\
    (!i. w2n w+28 <= i /\ i < w2n w+32 ==> i NOTIN tn'.t_mem) /\
    wb_frame ce ee ee se s t /\ ghost_kept_at lo ce ee se G tn s G' tn' /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = st.cs_current_bb /\
    t.vs_inst_idx = LENGTH st.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee G' tn' t) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  drule_then (assume_tac o cj 2) abi_builtin_alloc_buffer_shape >>
  drule_then assume_tac emit_op_next_id >>
  `ci_mono se sb /\ ci_mono sb sm /\ ci_mono sm st` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `se.cs_next_var <= sm.cs_next_var /\ se.cs_next_id < st.cs_next_id` by
    (fs[ci_mono_def] >>
     qpat_assum `emit_op ALLOCA _ se = _` (mp_tac o MATCH_MP emit_op_next_id) >>
     decide_tac) >>
  `?(inst:instruction) r.
     ba.buf_operand = Var r /\ MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = se.cs_next_id /\ inst.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r` by
    (mp_tac (Q.INST [`cut` |-> `se`, `st` |-> `se`, `en` |-> `sb`,
       `n` |-> `n2w capacity`, `out` |-> `ba.buf_operand`, `scopes` |-> `ee.scopes`]
       extcall_direct_alloca_site) >>
     asm_simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel hz ctx func ce cx ee s`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `ctx_has_dalloca ctx ==>
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp` by
    (qpat_assum `stmt_state_rel hz ctx func ce cx ee s`
       (mp_tac o MATCH_MP stmt_state_rel_fmp_room) >>
     simp[fmp_room_def] >> rpt strip_tac >> res_tac >> decide_tac) >>
  mp_tac (Q.INST [`sa` |-> `se`, `sc` |-> `sm`, `cenv` |-> `ce`,
    `es` |-> `ee`, `shared` |-> `ba`, `n` |-> `capacity`, `bs` |-> `selector`, `H0` |-> `hz`]
    extcall_direct_request_buffer) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >>
  disch_then (qx_choosel_then [`rr`,`w`,`u`,`Gu`,`tu`] strip_assume_tac) >>
  `rr = r` by metis_tac[operand_11] >> qpat_x_assum `rr = r` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (qspec_then `hz` (drule_then
         (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1)))) >>
  `alloca_inv u /\ alloca_room ctx func u` by
    metis_tac[stmt_state_rel_local_ptrs_alloca,stmt_state_rel_alloca_room] >>
  `emit_op ADD [Var r;Lit 32w] sm = (payload,st)` by
    (qpat_assum `ba.buf_operand = Var r` (fn th =>
       qpat_assum `emit_op ADD [ba.buf_operand; Lit 32w] sm = _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [th]))) >>
  mp_tac (Q.INST [`s` |-> `u`, `st` |-> `sm`, `en` |-> `st`,
    `dst` |-> `r`, `head` |-> `payload`, `b` |-> `w2n (w:bytes32)`, `off` |-> `32`,
    `cap` |-> `capacity`, `n` |-> `capacity-32`, `G` |-> `Gu`, `tn` |-> `tu`]
    abi_encode_values_head_address) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [eval_operand_def] >> decide_tac) >>
  disch_then (qx_choosel_then [`p`,`t`,`G'`,`tn'`] strip_assume_tac) >>
  mp_tac (Q.INST [`front` |-> `se`, `s` |-> `u`, `st` |-> `sm`, `en` |-> `st`,
    `shared` |-> `se.cs_next_id`, `b` |-> `w2n (w:bytes32)`, `cap` |-> `capacity`,
    `G` |-> `Gu`, `tn` |-> `tu`, `ids` |-> `{}`, `outs` |-> `[]`]
    extcall_direct_row_phase) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> metis_tac[]) >>
  strip_tac >>
  `FLOOKUP t.vs_allocas se.cs_next_id = SOME (w2n w,capacity)` by
    metis_tac[window_phase_effect,abi_encoder_registered_effect_allocated] >>
  `not_fresh_at st r` by
    metis_tac[ci_mono_def,freshWritesTheory.not_fresh_at_mono] >>
  `lookup_var r t = SOME w /\ ptr_covers G' tn' r t capacity` by
    metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  mp_tac (Q.INST [`front` |-> `se`, `st` |-> `se`, `H` |-> `hz`]
    extcall_direct_row_frame_trans) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >>
  strip_tac >>
  `read_memory (w2n w+28) 4 t = selector` by
    (qpat_assum `t.vs_memory = u.vs_memory` (fn th =>
       PURE_REWRITE_TAC [memoryReadPropsTheory.read_memory_eq_mem_bytes_at,th]) >>
     qpat_assum `read_memory (w2n w+28) 4 u = selector`
       (ACCEPT_TAC o REWRITE_RULE [memoryReadPropsTheory.read_memory_eq_mem_bytes_at])) >>
  `!i. w2n w+28 <= i /\ i < w2n w+32 ==> i NOTIN tn'.t_mem` by
    (qpat_assum `tn'.t_mem = tu.t_mem` (fn th => PURE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`r`,`p`,`w`,`t`,`G'`,`tn'`,`inst`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY decide_tac >> POP_ASSUM_LIST (K ALL_TAC) >> NO_TAC
QED
