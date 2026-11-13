(* Joint resources at the actual transient-lock endpoint.  The fixed frame's
   operand and memory origins are not changed by this transport. *)
Theory bodyIntCallNRRoot
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore bodyIntCallNRRootProbe
  transientLockFrameProps transientLockProps nonreentrantEquiv
  exprLoweringProps loweringStateRelDefs loweringPosts venomState intCallFrame
  vyperScopePreservation vyperStatePreservation

Theorem intcall_joint_res_defined_frame:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  state_rel fp.jc_func ce fp.jc_cx ee t /\
  expr_sim_inv ce fp.jc_cx env ee /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
  t.vs_memory = s.vs_memory /\ sa.cs_next_var <= sb.cs_next_var /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) ==>
  intcall_joint_res fp ce env ee sb t
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_res_def] >>
  `local_ptrs_rel fp.jc_func ce es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p t = lookup_var p s` by
    (rpt strip_tac >>
     fs[local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >>
     first_x_assum (qspec_then `Var p` mp_tac) >> simp[eval_operand_def]) >>
  `!n b sz. local_region ce ee.scopes t n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> gvs[] >> irule local_region_lookup_cong >> metis_tac[]) >>
  `immutable_alloca_sep fp.jc_func ce fp.jc_cx ee t` by
    (irule immutable_alloca_sep_fields >>
     qexistsl [`s`,`es`] >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `immutable_base_zero ce t` by
    (fs[stmt_state_rel_def, immutable_base_zero_def] >> metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee t` by
    (irule stmt_state_rel_allocas_frame >> simp[] >>
     qexistsl [`es`,`s`] >> simp[]) >>
  `allocas_above fp.jc_lo t` by
    (fs[intcall_expr_res_def, allocas_above_def] >> metis_tac[]) >>
  simp[intcall_joint_res_def] >> conj_tac
  >- (irule bodyIntCallJointCallCoreTheory.intcall_joint_res_frame >> simp[] >>
      qexistsl [`es`,`s`,`sa`] >> simp[] >>
      fs[intcall_expr_res_def, intcall_frame_ok_def, allocas_above_def] >>
      metis_tac[eval_operand_def]) >>
  fs[intcall_joint_res_def]
QED

Theorem intcall_actual_lock_joint_res:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  nonreentrant_slot_separated fp.jc_cx /\
  fp.jc_cx.nonreentrant_slot = SOME key /\ fresh_vars_wrt sa s /\
  compile_nonreentrant_lock key T view sa = ((),sb) /\
  acquire_nonreentrant_lock fp.jc_cx.txn.target key view es = (INL (),ee) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  expr_sim_inv ce fp.jc_cx env ee ==>
  intcall_joint_res fp ce env ee sb t
Proof
  strip_tac >>
  drule intcall_transient_lock_run_frame >> disch_then drule >> strip_tac >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  drule compile_nonreentrant_lock_transient_counter >> strip_tac >>
  `state_rel fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def] >>
  `tload (n2w key) s <> 1w` by
    gvs[transient_lock_code_execution, AllCaseEqs()] >>
  drule_all compile_nonreentrant_lock_source_correct >> strip_tac >>
  gvs[] >>
  `ee.scopes = es.scopes /\ ee.immutables = es.immutables` by
    metis_tac[acquire_nonreentrant_lock_scopes,
              acquire_nonreentrant_lock_immutables] >>
  irule intcall_joint_res_defined_frame >> simp[] >>
  qexistsl [`es`,`s`,`sa`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      gvs[transient_lock_code_execution, AllCaseEqs()] >>
      irule transient_lock_checked_operand >> simp[]) >>
  gvs[venom_state_component_equality]
QED
