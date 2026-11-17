(* Normal counted prefixes introduce the shared expression judgment. *)
Theory exprSimValues
Ancestors
  exprSimDefs gasNormalPrefix gasOutcome gasSummary gasContext
  loweringPosts exprLowering emitHelper compileEnv loweringSlice vyperState
  gasStorage vyperStorageTrace vyperStorageFootprint

Theorem expr_sim_values:
  !ctx func cenv cx ty e es.
    (!st0 sa sb op s0.
       lower_value compile_expr cenv ty e sa = (op, sb) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\
       gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
       (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es s0 /\
         storage_well_formed_on cx es (FST H)) /\ ~s0.vs_halted /\
       s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
       ?marks v ee t.
         gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
           (es,s0) marks (INL v) ee (OK t) /\
         !H. valid_horizon cx st0 H ee.storage_trace ==>
           gas_value_prefix H F (ctx,func,cenv,cx) (ty,e)
             (sa,sb,op) (es,s0) marks (v,ee,t)) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >> first_x_assum drule_all >> rpt strip_tac >>
  PURE_REWRITE_TAC[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  PURE_REWRITE_TAC[gas_summary_at_def] >>
  qexistsl_tac [`INL v`, `ee`, `OK t`] >> simp[] >>
  disj1_tac >> rpt strip_tac >> first_x_assum drule >> simp[gas_value_prefix_def]
QED

(* As expr_sim_values, when the witnesses need a valid horizon of the
   starting trace: a start outside the storage domain stays outside it. *)
Theorem expr_sim_values_domain:
  !ctx func cenv cx ty e es.
    (!st0 sa sb op s0.
       lower_value compile_expr cenv ty e sa = (op, sb) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv sa /\
       gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
       (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es s0 /\
         storage_well_formed_on cx es (FST H)) /\ ~s0.vs_halted /\
       s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
       (?H. valid_horizon cx st0 H es.storage_trace) ==>
       ?marks v ee t.
         gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
           (es,s0) marks (INL v) ee (OK t) /\
         !H. valid_horizon cx st0 H ee.storage_trace ==>
           gas_value_prefix H F (ctx,func,cenv,cx) (ty,e)
             (sa,sb,op) (es,s0) marks (v,ee,t)) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (PURE_REWRITE_TAC[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      rw[gas_bad_storage_at_def] >>
      `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
        (irule storage_trace_frame_bind_all >>
         simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      `~storage_trace_domain cx st0 (es with gas_obs := tail).storage_trace` by
        simp[] >>
      Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := tail)` >>
      simp[] >> metis_tac[storage_trace_frame_preserves_bad_domain]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by fs[storage_trace_domain_def] >>
  first_x_assum (qspecl_then [`st0`, `sa`, `sb`, `op`, `s0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  PURE_REWRITE_TAC[gas_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  PURE_REWRITE_TAC[gas_summary_at_def] >>
  qexistsl_tac [`INL v`, `ee`, `OK t`] >> simp[] >>
  disj1_tac >> rpt strip_tac >> first_x_assum drule >> simp[gas_value_prefix_def]
QED
