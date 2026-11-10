(* Consume a resource-carrying body outcome through its implicit epilogue. *)
Theory bodyIntCallPackageBodyOutcome
Ancestors
  bodyIntCallPackageHandler bodyIntCallPackageEpilogue bodyIntCallJointContract
  stmtSimDefs loweringPosts
Libs
  monadsyntax

Theorem gas_outcome_internal_body:
  intcall_frame_ok fp /\
  (fp.jc_ret_ty = NoneT \/ stmts_no_fallthrough ss) /\
  (if block_is_terminated sb then ((),sb)
   else if fp.jc_ret_ty = NoneT then emit_inst RET [fp.jc_rpc] [] sb
   else emit_inst INVALID [] [] sb) = ((),sf) /\
  fn_has_code sb sf fp.jc_func /\
  gas_outcome F tops (fp.jc_ctx,fp.jc_func) (eval_stmts fp.jc_cx ss)
    (es,s0) Q (intcall_stmt_exit fp) /\
  (!res ee u. Q res ee u ==>
    stmt_lands NoLoop sb res u /\ ~u.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb) /\
    ?ce env. intcall_joint_res fp ce env ee sb u) /\
  (!v ee r. intcall_stmt_exit fp (INR (ReturnException v)) ee r ==>
    R (INL v) ee r) /\
  (!res ee r. expr_exit res r ==> R res ee r) ==>
  gas_outcome F tops (fp.jc_ctx,fp.jc_func)
    (try (ignore_bind (eval_stmts fp.jc_cx ss) (return NoneV)) handle_function)
    (es,s0) (\res ee u. F) R
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  irule gas_outcome_function_body >>
  conj_tac >- simp[] >> qexistsl [`Q`, `fp`] >> simp[] >> rpt strip_tac >>
  `stmt_lands NoLoop sb res u /\ ~u.vs_halted /\
    ~block_is_terminated sb /\ ?ce env. intcall_joint_res fp ce env
      (mid with gas_obs := []) sb u` by
    (first_x_assum drule >> simp[stmt_lands_def] >> metis_tac[]) >>
  drule_all intcall_normal_epilogue >> strip_tac >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
