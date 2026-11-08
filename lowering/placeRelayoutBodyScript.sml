(* Body-facing raw-RHS and target composition for widened assignments. *)
Theory placeRelayoutBody
Ancestors
  placeRelayoutSemantic placeRelayoutFrag placeRelayoutGasCompose
  placeRelayoutCode bodyPlacePremises exprSimAggregateBodySource
  exprSimDefs exprSimHypsDefs loweringPosts stmtSimDefs compileEnv
  targetPlaceSimCases gasSummary gasSummaryCompose exprSimSubscriptMap

Theorem widened_place_raw_rhs_outcome:
  expr_body_pre cenv cx env e es /\
  expr_vv_sim ctx func cenv cx (expr_type e) e es /\
  ~(lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  compile_expr cenv (expr_type e) e sa = (vv,sv) /\
  fn_has_code sa sv func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?v. res = INL (Value v) /\
      vv_post ctx func cenv cx e es sa sv s0 ee (Value v) vv t /\
      t.vs_current_bb = sv.cs_current_bb /\
      t.vs_inst_idx = LENGTH sv.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!st pv ee. eval_expr cx e st = (INL pv,ee) ==> ?v. pv = Value v` by
    metis_tac[placeRelayoutRawSourceTheory.strict_widened_rhs_delayed_read] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[placeRelayoutGasSourceTheory.assign_place_raw_rhs_admissible] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_def] >> disch_then drule_all >>
  strip_tac >>
  drule gas_outcome_source_invariant >>
  disch_then (qspec_then
    `\res. !pv. res = INL pv ==> ?v. pv = Value v` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> gvs[] >> metis_tac[])) >> strip_tac >>
  irule gas_outcome_conseq >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED
