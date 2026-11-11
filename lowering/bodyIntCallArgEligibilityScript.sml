(* Static call-argument eligibility and successful source endpoints. *)
Theory bodyIntCallArgEligibility
Ancestors
  bodySim exprSimSource exprSimHyps exprSimHypsDefs supportedExprTraverse
  vyperTypeCallStackSoundness vyperTypeSystem vyperTypeCallGraph allocLimits list

Theorem expr_body_pre_intcall_arg:
  expr_body_pre cenv cx env (Call ann (IntCall (src,name)) args dflt) es0 /\
  MEM e args /\ expr_sim_inv cenv cx env ee ==>
  expr_body_pre cenv cx env e ee
Proof
  rpt strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
      byte_widths_expr_def, alloc_limits_expr_def,
      supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
    alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem,
    call_evaluation_safe_mono, MEM]
QED

Theorem expr_body_pre_intcall_args_after:
  expr_body_pre cenv cx env (Call ann (IntCall (src,name)) args dflt) es0 /\
  MEM h args /\ expr_sim_inv cenv cx env es /\
  eval_expr cx h es = (INL raw,ee) ==>
  EVERY (\e. expr_body_pre cenv cx env e (ee with gas_obs := [])) args
Proof
  strip_tac >>
  `expr_body_pre cenv cx env h es` by
    (irule expr_body_pre_intcall_arg >> metis_tac[]) >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  irule expr_body_pre_intcall_arg >> simp[] >> metis_tac[]
QED

Theorem body_results_head_vv_sim:
  body_inv tops ctx cenv cx /\ body_results_ok cx (e::rest) /\
  expr_body_pre cenv cx env e es ==>
  expr_vv_sim ctx func cenv cx (expr_type e) e es
Proof
  simp[body_results_ok_def, body_expr_ok_def] >> metis_tac[]
QED

Theorem body_results_success_tail:
  body_results_ok cx (e::rest) /\
  eval_expr cx e es = (INL raw,ee) ==>
  body_results_ok cx rest
Proof
  simp[body_results_ok_def] >> metis_tac[]
QED
