(* Physical initialization of an inactive local, before source activation. *)
Theory bodyIntCallFamStmtMutationInactiveStore
Ancestors
  bodyIntCallFamAggArray bodyIntCallJointAggCore exprSimAlloc
  emitHelperProps bodyIntCallJointContract exprLoweringProps
  compileEnv

Theorem intcall_inactive_mstore_resources:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  emit_void MSTORE [Var p; op] sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME w /\ eval_operand op s = SOME wd /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  fp.jc_lo <= b /\ b <= w2n w /\ w2n w + 32 <= b+k /\
  (!n a z. local_region ce es.scopes s n a z ==>
             regions_disjoint b k a z) ==>
  ?u. u = (mstore (w2n w) wd s with
               vs_inst_idx := LENGTH sb.cs_current_insts) /\
      typed_copy_effect fp.jc_ctx fp.jc_func sa sb s u (w2n w) 32 /\
      intcall_expr_res fp ce env es sb u
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  drule_all intcall_mstore_effect >>
  disch_then (qspec_then `fp.jc_ctx` assume_tac) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es
     (mstore (w2n w) wd s)` by
    (irule literal_mstore_state_rel >>
     goal_assum (drule_at Any) >> fs[regions_disjoint_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule emitted_insts_emit_void >> simp[]) >>
  qexists `mstore (w2n w) wd s with
               vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac >- REFL_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule intcall_joint_res_copy >>
  simp[stmt_state_rel_inst_idx] >>
  qexistsl [`w2n w`, `32`, `s`, `sa`] >>
  simp[] >>
  fs[intcall_frame_ok_def, regions_disjoint_def] >> rpt strip_tac >>
  qpat_x_assum `!a k. fp.jc_prot a k ==> a + k <= fp.jc_lo` drule >>
  decide_tac
QED
