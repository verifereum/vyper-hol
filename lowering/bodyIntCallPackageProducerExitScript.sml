(* Transport the resource-carrying explicit return to the caller boundary. *)
Theory bodyIntCallPackageProducerExit
Ancestors
  bodyIntCallSeamDefs bodyIntCallPackageStateTransport
  bodyIntCallPackageRootResource bodyIntCallJointContract stmtSimReturn
  compileEnv loweringStateRelDefs exprSimDefs

Theorem intcall_stmt_return_callee_exit:
  !fp v ee r cx owner rtv cenv rc t n m rb func.
  intcall_stmt_exit fp (INR (ReturnException v)) ee r /\
  fp.jc_cx = (cx with stk updated_by CONS owner) /\
  fp.jc_ret_tv = rtv /\
  fp.jc_root_ce.ce_module_vars = cenv.ce_module_vars /\
  fp.jc_root_ce.ce_module = cenv.ce_module /\
  fp.jc_root_ce.ce_is_ctor = cenv.ce_is_ctor /\
  fp.jc_root_ce.ce_returns_count = rc /\ fp.jc_morig = t /\
  (!a k. fp.jc_prot a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m ==> regions_disjoint a k off asz) /\
  OPTION_MAP FST fp.jc_rb = rb ==>
  intcall_callee_exit func cenv cx rtv rc rb n m t (INL v) ee r
Proof
  rpt gen_tac >>
  simp[intcall_stmt_exit_def, intret_q_def] >> strip_tac
  >- (Cases_on `r` >> gvs[expr_exit_def]) >>
  gvs[result_rel_def] >>
  rename1 `state_rel _ _ _ _ landed` >>
  `state_rel func cenv cx (ee with scopes := []) landed` by
    (irule state_rel_empty_scopes_env >>
     qexistsl [`fp.jc_root_ce`, `fp.jc_func`] >>
     fs[state_rel_call_stack]) >>
  simp[intcall_callee_exit_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> rename1 `fp.jc_rb = SOME pair` >>
  PairCases_on `pair` >> gvs[]
QED

Theorem intcall_joint_res_void_return:
  intcall_joint_res fp ce env ee sb u /\ fp.jc_ret_tv = NoneTV /\
  fp.jc_root_ce.ce_returns_count = 0 /\ fp.jc_rb = NONE ==>
  intcall_stmt_exit fp (INR (ReturnException NoneV)) ee
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u)
Proof
  strip_tac >>
  fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `state_rel fp.jc_func ce fp.jc_cx (ee with scopes := []) u` by
    (irule state_rel_scopes_nil >> fs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `state_rel fp.jc_func fp.jc_root_ce fp.jc_cx (ee with scopes := []) u` by
    (irule state_rel_empty_scopes_env >> qexistsl [`ce`, `fp.jc_func`] >>
     fs[bodySimTheory.same_frame_def, compile_env_component_equality]) >>
  simp[intcall_stmt_exit_def, intret_q_def, result_rel_def, intret_vals_match_def]
QED
