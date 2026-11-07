(* Counted sequencing for the captured captured, index, and readonly suffix. *)
Theory exprSimSubscriptArrayCompose
Ancestors
  exprSimSubscriptArraySuffix gasOutcome gasSummary gasSummaryCompose gasExemptCert
  exprSimDefs exprSimSubscriptArraySource exprSimMemorySource vyperState list

Theorem framed_array_summary_after_prefix[local]:
  gas_marked_exec memory (ctx,func) a (es,s0) left (INL v) mid (OK t) /\
  gas_summary_at memory (ctx,func) right (k v)
    (mid with gas_obs := [],t) Q R ==>
  gas_summary_at memory (ctx,func) (left ++ right) (bind a k) (es,s0) Q R
Proof
  simp[gas_summary_at_def] >> rpt strip_tac >>
  qexistsl_tac [`res`,`es_end`,`r`] >>
  simp[] >> metis_tac[gas_marked_exec_bind_normal]
QED

Theorem framed_array_index_outcome_compose:
  gas_marked_exec F (ctx,func) (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL captured) mid (OK t) /\
  gas_outcome F tops (ctx,func) (b : evaluation_state -> value evaluation_result)
    (mid with gas_obs := [],t)
    (\res ee u. ?v. res = INL v /\ V v ee u)
    (\res ee out. ?exc. res = INR exc /\ R (INR exc) ee out) /\
  (!imarks raw v u.
     gas_marked_exec F (ctx,func) b (mid with gas_obs := [],t)
       imarks (INL v) raw (OK u) /\ V v (raw with gas_obs := []) u ==>
     gas_summary_at F (ctx,func) [] (k captured v) (raw with gas_obs := [],u) Q R) ==>
  gas_outcome F tops (ctx,func) (bind a (\r. bind b (k r))) (es,s0) Q R
Proof
  strip_tac >> fs[gas_outcome_def] >>
  qexists_tac `left ++ marks`
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit")
  >> suspend "exempt"
QED

Resume framed_array_index_outcome_compose[normal]:
  gvs[] >> disj1_tac >>
  irule framed_array_summary_after_prefix >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  pure_once_rewrite_tac[GSYM APPEND_NIL] >>
  irule framed_array_summary_after_prefix >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume framed_array_index_outcome_compose[exit]:
  gvs[] >> disj1_tac >>
  irule framed_array_summary_after_prefix >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC
QED
Resume framed_array_index_outcome_compose[exempt]:
  disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  pure_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  first_assum ACCEPT_TAC
QED
Finalise framed_array_index_outcome_compose

(* The suffix callback retains the static Code-or-Fixed provenance and
   captured-base post; neither is inferred from the runtime operand. *)
Theorem framed_array_after_base:
  gas_marked_exec F (ctx,func) (eval_expr cx obj)
    (es,s0) left (INL captured) mid (OK t) /\
  expr_sim ctx func cenv cx ty idx (mid with gas_obs := []) /\
  lower_value compile_expr cenv ty idx sm = (iop,si) /\
  fn_has_code sm si func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (mid with gas_obs := []) /\
  stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!imarks raw v u.
     gas_marked_exec F (ctx,func) (bind (eval_expr cx idx) (read_result cx))
       (mid with gas_obs := [],t) imarks (INL v) raw (OK u) /\
     expr_post ctx func cenv cx idx (mid with gas_obs := []) sm si t
       (raw with gas_obs := []) v iop u /\
     u.vs_current_bb = si.cs_current_bb /\
     u.vs_inst_idx = LENGTH si.cs_current_insts ==>
     gas_summary_at F (ctx,func) []
       (select_result cx (expr_type obj) captured (ValueSubscript v))
       (raw with gas_obs := [],u) Q (\res ee out. expr_exit res out)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    Q (\res ee out. expr_exit res out)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sm`,`si`,`iop`,`t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  irule (BETA_RULE (Q.ISPEC `\r v. select_result cx (expr_type obj) r (ValueSubscript v)`
    (Q.GEN `k` framed_array_index_outcome_compose))) >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  qexists_tac `\v ee u.
    expr_post ctx func cenv cx idx (mid with gas_obs := []) sm si t ee v iop u /\
    u.vs_current_bb = si.cs_current_bb /\
    u.vs_inst_idx = LENGTH si.cs_current_insts` >> simp[] >>
  `(!res out. (?exc. res = (INR exc : value + exception) /\
        expr_exit (INR exc : eval_result + exception) out) = expr_exit res out)` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED

(* Source observations are consumed by executions, but not by endpoint posts. *)
Theorem expr_post_initial_gas:
  expr_post ctx func cenv cx e (es with gas_obs := gs) sa sb s0 ee v op s <=>
  expr_post ctx func cenv cx e es sa sb s0 ee v op s
Proof
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.locals_kept_def,
       loweringPostsTheory.popped_kept_def]
QED

Theorem read_result_success_gas_iff[local]:
  read_result cx r (ee with gas_obs := gs) = (INL v,ee with gas_obs := gs) <=>
  read_result cx r ee = (INL v,ee)
Proof
  eq_tac >> strip_tac
  >- (drule read_result_gas_obs >>
      disch_then (qspec_then `ee.gas_obs` mp_tac) >> simp[]) >>
  drule read_result_gas_obs >> simp[]
QED

Theorem stmt_state_rel_source_gas[local]:
  stmt_state_rel ctx func cenv cx (ee with gas_obs := gs) s <=>
  stmt_state_rel ctx func cenv cx ee s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       compileEnvTheory.state_rel_gas_obs,
       exprLoweringPropsTheory.immutable_alloca_sep_def]
QED

Theorem vv_at_source_gas[local]:
  vv_at cenv cx ty sa sb (ee with gas_obs := gs) r vv s <=>
  vv_at cenv cx ty sa sb ee r vv s
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_at_def, read_result_success_gas_iff,
       loweringPostsTheory.expr_val_at_def]
QED

Theorem read_storage_success_gas_iff[local]:
  read_storage_slot cx tr w tvt (ee with gas_obs := gs) =
    (INL v,ee with gas_obs := gs) <=>
  read_storage_slot cx tr w tvt ee = (INL v,ee)
Proof
  qspec_then `PlaceR (StoragePlace tr w tvt)` mp_tac
    (Q.GEN `r` read_result_success_gas_iff) >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.read_place_def]
QED

Theorem vv_holds_source_gas[local]:
  vv_holds cenv cx ty r vv (ee with gas_obs := gs) s <=>
  vv_holds cenv cx ty r vv ee s
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_holds_def, read_result_success_gas_iff] >>
  Cases_on `p.ptr_location` >>
  simp[loweringPostsTheory.immutable_holds_def,
       loweringPostsTheory.storage_holds_def, read_result_success_gas_iff,
       read_storage_success_gas_iff, vyperStorageBackendTheory.get_storage_def]
QED

Theorem vv_own_source_gas[local]:
  vv_own cenv cx ty sa sb (ee with gas_obs := gs) r vv s <=>
  vv_own cenv cx ty sa sb ee r vv s
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_own_def, loweringPostsTheory.expr_val_own_def,
       read_result_success_gas_iff]
QED

Theorem vv_post_final_gas:
  vv_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := gs) r vv s <=>
  vv_post ctx func cenv cx e es sa sb s0 ee r vv s
Proof
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.locals_kept_def,
       loweringPostsTheory.popped_kept_def, stmt_state_rel_source_gas,
       vv_holds_source_gas, vv_at_source_gas, vv_own_source_gas]
QED
