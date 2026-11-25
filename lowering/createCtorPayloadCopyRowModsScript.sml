(* Project the positional post at the observed private snapshot endpoint. *)
Theory createCtorPayloadCopyRowMods
Ancestors
  createCtorPrivateSnapshotMods createCtorSnapshotTypingMods
  bodyFullExtCallPackingReady loweringPosts vyperAST

Theorem ctor_payload_snapshot_copy_post_mods:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,sb) /\
  exprs_can_mutate ce xs /\ ~is_word_type (lowered_value_type ce e) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
    (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
       ptr_buf_ok ce e op G s) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok ce e p.ptr_operand G s) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx raw ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
         eval_operand (vv_operand vv) s = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory rt val (w2n w) mem))) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  return_buf_frame d ce sa s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  RTC (\u r. (u.vs_current_bb,u.vs_inst_idx) <>
                (sb.cs_current_bb,LENGTH sb.cs_current_insts) /\
       ?i ms. ctor_segment_fetch func u = SOME i /\
              sm.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
              gas_origin_edge F explicit ctx func u ms (OK r)) s t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ctor_segment_fetch func t = SOME last /\ last.inst_opcode <> PHI /\
  sb.cs_next_id <= last.inst_id ==>
  ?Gt tt. !H. valid_horizon cx st0 H ee.storage_trace ==>
    extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [saved]
      sa sb es s0 G0 tn0 H (INL [v] : value list + exception) ee Gt tt t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  `storage_trace_domain cx st0 ee.storage_trace` by
    (drule extcall_packing_observed_domain >> simp[]) >>
  `~is_word_type (expr_type e)` by
    (drule ctor_snapshot_word_types_mods >> simp[]) >>
  `~is_word_type (post_value_type ce e)` by
    (Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
     >- (pop_assum strip_assume_tac >> gvs[post_value_type_def, expr_type_def] >> rw[])
     >> metis_tac[post_value_type_not_int_call]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,sb)` by fs[] >>
  `eval_expr cx e (es with gas_obs := es.gas_obs) = (INL raw,ee)` by simp[] >>
  `!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G s` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:exception``] ctor_private_snapshot_actual_mods) >>
  simp[] >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED
