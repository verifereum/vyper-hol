(* Unlock-aware statement producer boundary for an internal callee. *)
Theory bodyIntCallNrBodyOutcome
Ancestors
  bodyIntCallNrExit bodyIntCallPackageProducerOutcome
  bodyIntCallPackageHandler bodyIntCallJointContract stmtSimReturn
  bodyIntCallPackageStateTransport bodyIntCallSeamDefs
  compileEnv loweringStateRelDefs exprSimDefs venomState
  loweringPosts gasSummary vyperTypeEvalSoundness
Libs
  monadsyntax

Theorem intcall_joint_void_return_nr:
  intcall_joint_res fp ce env ee sb u /\ fp.jc_ret_tv = NoneTV /\
  fp.jc_root_ce.ce_returns_count = 0 /\ fp.jc_rb = NONE ==>
  intcall_stmt_exit fp (INR (ReturnException NoneV)) ee
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (return_unlock_state fp.jc_root_ce u))
Proof
  strip_tac >>
  fs[intcall_joint_res_def, intcall_expr_res_def] >>
  `state_rel fp.jc_func ce fp.jc_cx (ee with scopes := []) u` by
    (irule state_rel_scopes_nil >> fs[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `state_rel fp.jc_func fp.jc_root_ce fp.jc_cx (ee with scopes := []) u` by
    (irule state_rel_empty_scopes_env >> qexistsl [`ce`, `fp.jc_func`] >>
     fs[bodySimTheory.same_frame_def, compile_env_component_equality]) >>
  simp[intcall_stmt_exit_def] >> disj2_tac >>
  conj_tac >- (irule intret_q_intro >>
    qexistsl [`<|iret_values := []; iret_adopt_fmp := NONE|>`, `u`] >>
    simp[result_rel_def, intret_vals_match_def]) >>
  qabbrev_tac `info = fp.jc_root_ce.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0 /\ ~info3` >> Cases_on `info2` >>
  gvs[return_unlock_state_def, tstore_def, sstore_def, eval_operand_def,
      lookup_var_def] >>
  rpt strip_tac >>
  qpat_x_assum `!op. fp.jc_reserved op ==> _` drule >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem intcall_producer_callee_outcome_nr:
  fp.jc_root_ce.ce_nonreentrant = (nr,key,T,is_view_mut mut) /\
  cx.nonreentrant_slot = SOME key /\
  intcall_stmts_producer fp ss /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  supported_stmts fp.jc_tops bindings ss /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
    occurs_abi_decode_target target fp.jc_tops) /\
  type_stmts env fp.jc_ret_ty ss = SOME env' /\
  IS_SOME (type_stmts (env with bare_global_assignable := FEMPTY) fp.jc_ret_ty ss) /\
  stmts_exprs_ok ce ss /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_stmts ss) /\
  stmts_env ce NoLoop (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
    ss sa = (ce',sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmts fp.jc_cx ss) (stmt_res_ok NoLoop) es /\
  intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (fp.jc_ret_ty = NoneT \/ stmts_no_fallthrough ss) /\
  (!ce env ee u. intcall_joint_res fp ce env ee sb u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~block_is_terminated sb /\ fp.jc_ret_ty = NoneT ==>
    gas_path fp.jc_ctx fp.jc_func u 0
      (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
        (return_unlock_state fp.jc_root_ce u))) /\
  fp.jc_cx = (cx with stk updated_by CONS owner) /\ fp.jc_ret_tv = rtv /\
  fp.jc_root_ce.ce_module_vars = cenv.ce_module_vars /\
  fp.jc_root_ce.ce_module = cenv.ce_module /\
  fp.jc_root_ce.ce_is_ctor = cenv.ce_is_ctor /\
  fp.jc_root_ce.ce_returns_count = nret /\ fp.jc_morig = t /\
  (!a k. fp.jc_prot a k <=> a + k <= t.vs_alloca_next /\
    !aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m ==> regions_disjoint a k off asz) /\
  OPTION_MAP FST fp.jc_rb = rb ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (try (ignore_bind (eval_stmts fp.jc_cx ss) (return NoneV)) handle_function)
    (es,s) (\res ee u. F) (intcall_callee_exit func cenv cx mut nr rtv nret rb n m t)
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qpat_x_assum `intcall_stmts_producer fp ss`
    (assume_tac o SRULE [intcall_stmts_producer_def]) >>
  qpat_x_assum `!bindings ce ce' env env' lctx es sa sb s. _`
    (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`bindings`, `env'`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  irule gas_outcome_function_body >>
  conj_tac >- (rpt strip_tac >> simp[intcall_callee_exit_def] >>
    disj1_tac >> first_assum ACCEPT_TAC) >>
  goal_assum (drule_at Any) >>
  conj_tac >- suspend "normal" >>
  rpt strip_tac >> irule intcall_stmt_return_transient_exit >>
  goal_assum (drule_at Any) >> qexistsl [`key`, `owner`] >> simp[]
QED

Resume intcall_producer_callee_outcome_nr[normal]:
  rpt strip_tac >> gvs[stmt_lands_def] >>
  `fp.jc_ret_ty = NoneT` by
    (Cases_on `fp.jc_ret_ty = NoneT` >> gvs[] >>
     fs[gas_marked_exec_def] >>
     qpat_x_assum `!tail. eval_stmts _ _ _ = _` (qspec_then `[]` mp_tac) >>
     metis_tac[cj 2 no_fallthrough_eval_no_success]) >>
  `fp.jc_ret_tv = NoneTV /\ fp.jc_root_ce.ce_returns_count = 0 /\
    fp.jc_rb = NONE` by
    (fs[intcall_frame_ok_def, returns_stack_count_def,
        vyperValueTheory.evaluate_type_def] >> Cases_on `fp.jc_rb` >> gvs[]) >>
  fs[stmt_lands_def] >>
  (qexists `IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
    (return_unlock_state fp.jc_root_ce u)` >>
  conj_tac >- (qpat_x_assum `!ce env ee u. _` irule >> simp[] >>
    qexistsl [`ce'`, `mid with gas_obs := []`, `env'`] >> simp[]) >>
  conj_tac >- simp[fragExecTheory.exit_result_def] >>
  irule intcall_stmt_return_transient_exit >>
  goal_assum (drule_at Any) >> qexistsl [`key`, `owner`] >> simp[] >>
  irule intcall_joint_void_return_nr >> simp[] >>
  qexistsl [`ce'`, `env'`, `sb`] >> simp[])
QED
Finalise intcall_producer_callee_outcome_nr
