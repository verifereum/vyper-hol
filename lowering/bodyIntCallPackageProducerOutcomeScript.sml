(* Eliminate a statement producer and its function handler at the caller boundary. *)
Theory bodyIntCallPackageProducerOutcome
Ancestors
  bodyIntCallPackageBodyOutcome bodyIntCallPackageProducerExit
  bodyIntCallJointContract bodyIntCallSeamDefs
Libs
  monadsyntax

Theorem intcall_producer_callee_outcome:
  intcall_stmts_producer fp ss /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  supported_stmts fp.jc_tops bindings ss /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) ss ==>
    occurs_abi_decode_target target fp.jc_tops) /\
  type_stmts env fp.jc_ret_ty ss = SOME env' /\
  IS_SOME (type_stmts (env with bare_global_assignable := FEMPTY) fp.jc_ret_ty ss) /\
  EVERY (stmt_exprs_ok ce) ss /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_stmts ss) /\
  stmts_env ce NoLoop (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
    ss sa = (ce',sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmts fp.jc_cx ss) (stmt_res_ok NoLoop) es /\
  intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (fp.jc_ret_ty = NoneT \/ stmts_no_fallthrough ss) /\
  (if block_is_terminated sb then ((),sb)
   else if fp.jc_ret_ty = NoneT then emit_inst RET [fp.jc_rpc] [] sb
   else emit_inst INVALID [] [] sb) = ((),sf) /\
  fn_has_code sb sf fp.jc_func /\
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
    (es,s) (\res ee u. F) (intcall_callee_exit func cenv cx rtv nret rb n m t)
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qpat_x_assum `intcall_stmts_producer fp ss`
    (assume_tac o SRULE [intcall_stmts_producer_def]) >>
  qpat_x_assum `!bindings ce ce' env env' lctx es sa sb s. _`
    (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`bindings`, `env'`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  drule_at (Pat `gas_outcome _ _ _ _ _ _ _`) gas_outcome_internal_body >>
  disch_then (qspecl_then [`sf`, `sb`,
    `intcall_callee_exit func cenv cx rtv nret rb n m t`] mp_tac) >>
  impl_tac >-
    (simp[] >> conj_tac
     >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     conj_tac >- (rpt strip_tac >> irule intcall_stmt_return_callee_exit >>
       goal_assum (drule_at Any) >> qexists `owner` >> simp[]) >>
     rpt strip_tac >> pure_rewrite_tac[intcall_callee_exit_def] >>
     disj1_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED
