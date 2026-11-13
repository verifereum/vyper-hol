(* Body-facing source boundaries for strict widened place assignment. *)
Theory placeAssignBodyPremisesMem
Ancestors
  bodyAssignPlace bodyMemoryPreds placeAssignSourceClassification
  exprSimIfExpCompat exprSimMemDefs exprSimSource exprSimHypsDefs exprSimDefs
  exprSimHyps placeAssignAllocationBounds
  gasSummary gasContext stmtSimDefs
  vyperExprNoControl

Theorem assign_relayout_raw_value:
  expr_body_pre ce cx env e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  !st pv ee. eval_expr cx e st = (INL pv,ee) ==> ?v. pv = Value v
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `well_typed_expr env e /\
   sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[expr_body_pre_def, expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule_all ifexp_lowered_type_classify >> strip_tac >> gvs[] >>
  PairCases_on `fid` >> rpt gen_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.lift_option_type_def,
       vyperStateTheory.lift_sum_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem assign_relayout_raw_rhs_outcome_mem:
  expr_body_pre ce cx env e es /\
  expr_vv_sim_mem ctx func ce cx (expr_type e) e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  compile_expr ce (expr_type e) e a = (vv,b) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce a /\ stmt_state_rel ctx func ce cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = a.cs_current_bb /\
  s0.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?v. res = INL (Value v) /\
      vv_post ctx func ce cx e es a b s0 ee (Value v) vv t /\
      vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv t /\
      t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!st pv ee. eval_expr cx e st = (INL pv,ee) ==> ?v. pv = Value v` by
    metis_tac[assign_relayout_raw_value] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then drule_all >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` assume_tac >>
      fs[gas_marked_exec_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem assign_place_marked_rhs_target_pre_mem:
  expr_body_pre ce cx env e es /\
  target_indices_pre ce cx env bt /\ ~immutable_root cx bt /\
  (!ss pv ee. eval_expr cx e ss = (INL pv,ee) ==>
    body_base_target_mem_ok cx bt) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL (Value v)) ee r ==>
  target_pre ce cx env bt (ee with gas_obs := []) /\
  body_base_target_mem_ok cx bt
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> strip_tac >>
  simp[targetPlaceSimTheory.target_pre_def] >> metis_tac[]
QED
