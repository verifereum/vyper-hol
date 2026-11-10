(* Producer dispatch for the selected external return. *)
Theory externalReturnSelectedPrefix
Ancestors externalReturnCountedBoundary externalReturnIntcallStack
  externalReturnIntcallForce externalReturnIntcallProducer
  exprOperandVar exprLoweringProps exprSimDefs stmtSimReturn
  gasOutcome gasSummary exprLowering vyperAST compileEnv

Theorem return_prefix_code_resources:
  lower_value compile_expr ce ct e sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
  local_ptrs_reserved ce sb /\
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> conj_tac
  >- (drule_all return_lower_value_code_slices >> strip_tac >>
      `ci_mono sm sb` by
        (mp_tac ci_mono_unwrap_value >>
         disch_then (qspecl_then [`ce`,`vv`,`sm`] mp_tac) >> simp[]) >>
      irule local_ptrs_reserved_next_var >>
      qexists_tac `sm` >> gvs[ci_mono_def]) >>
  metis_tac[compile_lower_value_var]
QED

Theorem return_prefix_post_weaken[local]:
  gas_outcome F tops (ctx,func) source start P R /\
  (!res ee t. P res ee t ==> Q res ee t) ==>
  gas_outcome F tops (ctx,func) source start Q R
Proof
  Cases_on `start` >>
  simp[gas_outcome_def, gas_summary_at_def] >> metis_tac[]
QED


Theorem return_selected_forced_prefix:
  lower_value compile_expr ce ct e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  expr_sim ctx func ce cx ct e es /\ expr_vv_sim ctx func ce cx ct e es /\
  gas_admissible (eval_stmt cx (Return (SOME e))) (stmt_res_ok lctx) es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee s. ?v. res = INL v /\
      expr_post ctx func ce cx e es sa sb s0 ee v op s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ((!ann fid args drv. e <> Call ann (IntCall fid) args drv) \/
       (?ann fid args drv. e = Call ann (IntCall fid) args drv) \/
       (?ann fid args drv pvs. e = Call ann (IntCall fid) args drv /\
          ce.ce_func_info (nsid_to_string fid) = (0,0,pvs) /\ op = Lit 0w)))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `?ann fid args drv. e = Call ann (IntCall fid) args drv`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      drule_all return_lower_value_code_slices >> strip_tac >>
      drule_all return_compile_intcall_output >> strip_tac >> gvs[]
      >- (drule_all return_intcall_located_force >> strip_tac >>
          irule return_prefix_post_weaken >> goal_assum (drule_at Any) >>
          simp[] >> metis_tac[]) >>
      gvs[unwrap_value_def, comp_return_def] >>
      drule_all return_intcall_stack_force >> strip_tac >>
      irule return_prefix_post_weaken >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[]) >>
  drule return_forced_admissible >> strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_def] >> disch_then drule_all >> strip_tac >>
  irule return_prefix_post_weaken >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
