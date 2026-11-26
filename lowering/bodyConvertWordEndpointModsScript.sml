(* Linked VV post for the readonly scalar Convert suffix. *)
Theory bodyConvertWordEndpointMods
Ancestors
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyFullPostsMods
  assignTuplePtrLoadStep stateFrame allocasBelowFmpUpdatesProps exprSimProps
  exprSimMemDefs loweringPosts loweringShapeDefs bodyPtrDefs
  compileEnv vyperAST vyperInterpreter vyperState venomState

Theorem convert_word_endpoint_mods:
  expr_post_mods H ctx func ce cx e es sa sm s0 ee v1 x t /\
  ghost_inv_at_mods D lo d ce cx ee G tn t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  is_word_type dst /\ evaluate_type (get_tenv cx) dst = SOME dtv /\
  value_has_type dtv v /\ eval_operand out s = SOME (typed_val_to_w256 dtv v) /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  state_frame s = state_frame (t with vs_inst_idx := s.vs_inst_idx) /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!z. not_fresh_at sm z ==> lookup_var z s = lookup_var z t /\
       FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  op_taint tnf out = {} /\ op_prov Gf out = NONE /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next ==>
  vv_post_mods H ctx func ce cx (TypeBuiltin dst Convert dst [e])
    es sa sb s0 ee (Value v) (StackValue dst out) s /\
  vv_store_bound cx dst lt ee (Value v) (StackValue dst out) s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_inv_at_mods D lo d ce cx ee Gf tnf s /\
  ptr_vv_ok cx dst (Value v) (StackValue dst out) ee Gf tnf s /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gf tnf
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    metis_tac[not_fresh_at_mono] >>
  `s = (t with vs_inst_idx := s.vs_inst_idx) with vs_vars := s.vs_vars` by
    metis_tac[state_frame_eq_reconstruct] >>
  `s.vs_memory = t.vs_memory /\ s.vs_data_section = t.vs_data_section /\
   s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next /\
   s.vs_call_ctx = t.vs_call_ctx /\ s.vs_accounts = t.vs_accounts /\
   s.vs_transient = t.vs_transient /\ s.vs_immutables = t.vs_immutables /\
   (allocas_below_fmp s <=> allocas_below_fmp t)` by
    (pop_assum SUBST1_TAC >> simp[allocas_below_fmp_updates]) >>
  qpat_x_assum `s = _` kall_tac >>
  `stmt_state_rel H ctx func ce cx ee s` by
    (irule stmt_state_rel_old_vars_frame_ptr >> qexistsl_tac [`t`,`sm`] >>
     asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >>
  `immutable_frame_mods func ce cx ee s` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`ee`,`t`,`sm`] >>
     simp[] >> metis_tac[]) >>
  simp[vv_store_bound_stack_word,ptr_vv_ok_def,read_result_def,return_def,
       ptr_val_ok_word] >>
  conj_tac
  >- (simp[vv_post_mods_def,vv_holds_mods_def,vv_holds_def,vv_at_def,
           vv_place_ptr_mods_def,vv_place_ptr_def,vv_storage_live_def,
           expr_type_def,read_result_def,return_def,expr_val_rel_def,expr_val_at_def] >>
      rpt conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz t.vs_memory = _` irule >>
          conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `aid` >> simp[])
      >- (irule locals_kept_mem_tail >> qexists_tac `t` >> simp[]) >>
      drule_all pure_frame_state_cong >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qexistsl_tac [`G`,`ee`,`t`,`sm`,`tn`] >> simp[] >> metis_tac[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >>
  simp[] >> metis_tac[]
QED
