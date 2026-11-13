(* Unlock-aware transport from the joint return contract to the caller. *)
Theory bodyIntCallNrExit
Ancestors
  bodyIntCallSeamDefs bodyIntCallPackageStateTransport
  bodyIntCallJointContract stmtSimReturn compileEnv loweringStateRelDefs
  exprSimDefs nonreentrantEquiv vyperInterpreter vyperState
  bodyIntCallPackageRootResource

Theorem intcall_stmt_return_transient_exit:
  !fp v ee r cx owner rtv cenv retc t n m rb func nr key mut.
  fp.jc_root_ce.ce_nonreentrant = (nr,key,T,is_view_mut mut) /\
  cx.nonreentrant_slot = SOME key /\
  intcall_stmt_exit fp (INR (ReturnException v)) ee r /\
  fp.jc_cx = (cx with stk updated_by CONS owner) /\
  fp.jc_ret_tv = rtv /\
  fp.jc_root_ce.ce_module_vars = cenv.ce_module_vars /\
  fp.jc_root_ce.ce_module = cenv.ce_module /\
  fp.jc_root_ce.ce_is_ctor = cenv.ce_is_ctor /\
  fp.jc_root_ce.ce_returns_count = retc /\ fp.jc_morig = t /\
  (!a k. fp.jc_prot a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m ==> regions_disjoint a k off asz) /\
  OPTION_MAP FST fp.jc_rb = rb ==>
  intcall_callee_exit func cenv cx mut nr rtv retc rb n m t (INL v) ee r
Proof
  rpt gen_tac >> strip_tac >>
  fs[intcall_stmt_exit_def]
  >- (Cases_on `r` >> gvs[expr_exit_def]) >>
  drule_all intret_q_source_epilogue >> strip_tac >>
  gvs[result_rel_def] >>
  Cases_on `nr` >> Cases_on `mut` >>
  gvs[is_view_mut_def, release_nonreentrant_lock_execution, return_def] >>
  simp[intcall_callee_exit_def, unlock_if_nr_def,
       release_nonreentrant_lock_execution, return_def] >>
  (conj_tac >-
    (irule state_rel_empty_scopes_env >>
     qexistsl [`fp.jc_root_ce`, `fp.jc_func`] >>
     fs[state_rel_call_stack]) >>
   conj_tac >- metis_tac[] >>
   rpt strip_tac >>
   qmatch_asmsub_rename_tac `FST rbpair` >>
   PairCases_on `rbpair` >> gvs[])
QED
