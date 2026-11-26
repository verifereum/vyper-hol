Theory bodyAbiTuplePhaseStateMods
Ancestors
  bodyAbiTupleBufferStateMods bodyAbiEncodeRegisteredFrameMods
  bodyFullExtCallDirectPhase abiEncodeValuesPhases abiEncoderWindowPhase
  abiEncoderRegisteredEffect exprSimAbiEncodeExecFrame bodyMemoryDefs
  exprSimWordArgs wordArgsPtr stateRelProj freshWrites exprLoweringProps
  list pair arithmetic
Libs horizonTypeLib

(* Move the live observation to the given exit, keeping the capture fixed.
   The saved-interval fact is supplied independently by the caller. *)
Theorem abi_tuple_phase_state_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  ci_mono a c /\ window_phase ctx func a c ids outs u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
  EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP v.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tv.t_mem ==> i IN tu.t_mem) /\
  (!b n. ((b = 0 /\ n = lo) \/
          (?name. local_region ce ee.scopes s name b n) \/
          (?aid. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
    mem_bytes_at b n v.vs_memory = mem_bytes_at b n s.vs_memory /\
    (!i. b <= i /\ i < b+n /\ i IN tv.t_mem ==> i IN tn.t_mem)) ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >>
  `EVERY (\(p,n). pbase <= p /\ p+n <= pbase+capacity) outs /\
   EVERY (\(p,n). pbase+dst_offset <= p) outs` by
    (qpat_assum `EVERY _ outs` mp_tac >> simp_tac bool_ss [EVERY_MEM, FORALL_PROD, UNCURRY_DEF] >>
     rpt strip_tac >>
     qpat_assum `!p n. MEM (p,n) outs ==> _` (drule_then strip_assume_tac) >>
     decide_tac) >>
  drule_all_then strip_assume_tac abi_encode_registered_phase_frame_mods >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ s`
    (drule_then assume_tac) >>
  `alloca_inv u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac abi_encode_saved_prefix_frame >>
  `!x w n. not_fresh_at a x /\ eval_operand (Var x) u = SOME w /\
    ptr_covers Gu tu x u n ==> eval_operand (Var x) v = SOME w /\ ptr_covers Gv tv x v n` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_values_pointer_frame >>
     qhdtm_assum `window_phase` (irule_at Any) >>
     qexistsl_tac [`tu`,`Gu`] >> asm_rewrite_tac[]) >>
  `eval_operand (Var root) v = SOME (n2w pbase) /\ ptr_covers Gv tv root v capacity` by
    (first_x_assum irule >> asm_rewrite_tac[]) >>
  `eval_operand (Var dst) v = SOME (n2w (pbase+dst_offset)) /\
   ptr_covers Gv tv dst v (capacity-dst_offset)` by
    (first_x_assum irule >> asm_rewrite_tac[]) >>
  `wb_frame ce ee ee se s v` by
    (irule (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.wb_frame_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee se u v` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee se G tn s Gv tv` by
    (irule (horizonTypeLib.at_horizon_named "H" wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee se s u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee se Gu tu u Gv tv` (irule_at Any) >> simp[]) >>
  `return_buf_frame d ce c v` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce a u` (irule_at Any) >>
     fs[ci_mono_def] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at a x ==> (!w. lookup_var x u = SOME w ==> _) /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `not_fresh_at c root /\ not_fresh_at c dst` by
    (conj_tac >> irule not_fresh_at_mono >> qexists_tac `a` >> fs[ci_mono_def]) >>
  `v.vs_accounts = u.vs_accounts /\ v.vs_transient = u.vs_transient /\
   v.vs_immutables = u.vs_immutables` by
    (drule window_phase_effect >> simp[abi_encoder_registered_effect_def]) >>
  qhdtm_x_assum `abi_encode_exec_frame`
    (strip_assume_tac o REWRITE_RULE[abi_encode_exec_frame_def]) >>
  qhdtm_x_assum `ci_mono` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
  PURE_REWRITE_TAC[abi_tuple_buffer_state_mods_def] >> asm_rewrite_tac[] >> decide_tac
QED
