(* Counted persistent/transient word stores with joint resources. *)
Theory bodyIntCallFamStmtMutationAugStorageStore
Ancestors
  bodyIntCallFamStmtMutationResourceLanding bodyIntCallJointContract
  placeStore vyperScopePreservation emitHelperProps exprLoweringProps
  compileEnv venomState stmtSimReturn loweringStateRelDefs

Theorem intcall_storage_place_word_store_path:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  write_place fp.jc_cx (StoragePlace tr slot tv) v es = (INL (),ee) /\
  storage_place_region fp.jc_cx (StoragePlace tr slot tv) /\
  is_word_type ty /\ evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  value_has_type tv v /\ expr_sim_inv ce fp.jc_cx env' ee /\
  ce_locals_declared ce env' /\ locals_alloc_ok ce env' /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sa = ((),sb) /\
  eval_operand dst s = SOME slot /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  ~s.vs_call_ctx.cc_static /\ fn_has_code sa sb fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_joint_res fp ce env' ee sb u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. lookup_var x u = lookup_var x s) /\
      u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
      u.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee
    (if tr then tstore slot (typed_val_to_w256 tv v) s
     else sstore slot (typed_val_to_w256 tv v) s)` by
    (irule place_store_word_backend_state >> metis_tac[]) >>
  `ee.scopes = es.scopes /\ ee.immutables = es.immutables` by
    metis_tac[write_storage_place_scopes_immutables] >>
  `sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[emitted_insts_emit_void,arithmeticTheory.LESS_EQ_REFL] >>
  `local_ptrs_reserved ce sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `intcall_joint_res fp ce env' ee sb
    ((if tr then tstore slot (typed_val_to_w256 tv v) s
      else sstore slot (typed_val_to_w256 tv v) s) with
       vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule intcall_joint_res_storage_landing >>
     simp[stmt_state_rel_inst_idx] >>
     qexistsl [`env`,`es`,`s`,`sa`] >>
     Cases_on `tr` >> gvs[tstore_def,sstore_def,lookup_var_def]) >>
  qspecl_then [`fp.jc_ctx`,`fp.jc_func`,
    `if tr then LocTransient else LocStorage`] mp_tac place_store_emit_run >>
  Cases_on `tr` >> gvs[] >> disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `intcall_joint_res fp ce env' ee sb u` >>
  qexists `u` >>
  gvs[Abbr `u`,tstore_def,sstore_def,lookup_var_def]
QED
