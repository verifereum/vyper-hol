(* Counted sequencing for the captured captured, index, and readonly suffix. *)
Theory exprSimSubscriptArrayCompose
Ancestors
  exprSimSubscriptArraySuffix gasOutcome gasSummary gasSummaryCompose gasExemptCert
  exprSimDefs exprSimSubscriptArraySource exprSimMemorySource vyperState list
  gasStorage

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

(* The index's run and the suffix are each checked on every horizon valid
   where they end; a trace outside every horizon is a bad-storage outcome. *)
Theorem framed_array_index_outcome_compose:
  gas_marked_exec F (ctx,func) (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL captured) mid (OK t) /\
  gas_outcome F tops (ctx,func) cx st0
    (b : evaluation_state -> value evaluation_result)
    (mid with gas_obs := [],t)
    (\H res ee u. ?v. res = INL v /\ V H v ee u)
    (\H res ee out. ?exc. res = INR exc /\ R H (INR exc) ee out) /\
  (!v. storage_trace_frame (k captured v)) /\
  (!imarks raw v u.
     gas_marked_exec F (ctx,func) b (mid with gas_obs := [],t)
       imarks (INL v) raw (OK u) /\
     (!H. valid_horizon cx st0 H raw.storage_trace ==>
        V H v (raw with gas_obs := []) u) ==>
     gas_outcome F tops (ctx,func) cx st0 (k captured v)
       (raw with gas_obs := [],u) Q R) ==>
  gas_outcome F tops (ctx,func) cx st0 (bind a (\r. bind b (k r))) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ b _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- suspend "bad"
  >- suspend "summary"
  >> suspend "exempt"
QED

Resume framed_array_index_outcome_compose[bad]:
  rewrite_tac[gas_outcome_def] >> qexists_tac `left ++ marks` >>
  disj1_tac >> irule gas_bad_storage_at_bind_right >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  irule gas_bad_storage_at_bind_left >> simp[]
QED

Resume framed_array_index_outcome_compose[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `left ++ marks` >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`fin`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  pure_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >>
  first_assum ACCEPT_TAC
QED

Resume framed_array_index_outcome_compose[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def]) >>
  disch_then (qx_choose_then `res` (qx_choose_then `ee1`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  reverse (Cases_on `storage_trace_domain cx st0 ee1.storage_trace`)
  >- (disch_then kall_tac >>
      rewrite_tac[gas_outcome_def] >> qexists_tac `left ++ marks` >>
      disj1_tac >> irule gas_bad_storage_at_bind_right >>
      goal_assum (drule_at Any) >> BETA_TAC >>
      irule gas_bad_storage_at_bind_left >> simp[] >>
      irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee1.storage_trace)
     ee1.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
      (assume_tac o SIMP_RULE (srw_ss()) []) >>
    `?v. res = INL v` by metis_tac[] >> gvs[] >>
    rename1 `gas_marked_exec _ _ b _ marks (INL v) ee1 (OK u)` >>
    qpat_x_assum `!imarks raw v u. _`
      (qspecl_then [`marks`, `ee1`, `v`, `u`] mp_tac) >>
    impl_tac >- simp[] >>
    disch_then (qx_choose_then `right` strip_assume_tac o
                REWRITE_RULE [gas_outcome_def]) >>
    rewrite_tac[gas_outcome_def] >> qexists_tac `left ++ (marks ++ right)`
    >- (disj1_tac >> irule gas_bad_storage_at_bind_right >>
        goal_assum (drule_at Any) >> BETA_TAC >>
        irule gas_bad_storage_at_bind_right >>
        goal_assum (drule_at Any) >> goal_assum drule)
    >- (disj2_tac >> disj1_tac >>
        irule framed_array_summary_after_prefix >>
        goal_assum (drule_at Any) >> BETA_TAC >>
        irule framed_array_summary_after_prefix >>
        goal_assum (drule_at Any) >> goal_assum drule) >>
    rename1 `gas_exempt_cert _ _ _ _ _ right (err,ee) (leaf,fin)` >>
    disj2_tac >> disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`fin`] >>
    pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
    irule gas_exempt_cert_bind_result >>
    goal_assum (drule_at Any) >> BETA_TAC >>
    pure_rewrite_tac[bind_assoc] >>
    irule gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >>
    fs[ignore_bind_def]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `?exc. res = INR exc` by metis_tac[] >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `left ++ marks` >>
  disj2_tac >> disj1_tac >>
  irule framed_array_summary_after_prefix >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
  qexistsl_tac [`INR exc`, `ee1`, `r`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> simp[]
QED

Finalise framed_array_index_outcome_compose

(* The suffix callback retains the static Code-or-Fixed provenance and
   captured-base post; neither is inferred from the runtime operand. *)
Theorem framed_array_after_base:
  ~subscript_reads_base cx obj idx ==>
  gas_marked_exec F (ctx,func) (eval_expr cx obj)
    (es,s0) left (INL captured) mid (OK t) /\
  expr_sim ctx func cenv cx ty idx (mid with gas_obs := []) /\
  lower_value compile_expr cenv ty idx sm = (iop,si) /\
  fn_has_code sm si func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
    (mid with gas_obs := []) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) t /\
     storage_well_formed_on cx (mid with gas_obs := []) (FST H)) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!imarks raw v u.
     gas_marked_exec F (ctx,func) (bind (eval_expr cx idx) (read_result cx))
       (mid with gas_obs := [],t) imarks (INL v) raw (OK u) /\
     (!H. valid_horizon cx st0 H raw.storage_trace ==>
        expr_post H ctx func cenv cx idx (mid with gas_obs := []) sm si t
          (raw with gas_obs := []) v iop u) /\
     u.vs_current_bb = si.cs_current_bb /\
     u.vs_inst_idx = LENGTH si.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) cx st0
       (select_result cx (expr_type obj) captured (ValueSubscript v))
       (raw with gas_obs := [],u) Q (\H res ee out. expr_exit res out)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (eval_expr cx (Subscript ann obj idx)) (es,s0)
    Q (\H res ee out. expr_exit res out)
Proof
  disch_tac >> strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`si`,`iop`,`t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th => pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  irule (BETA_RULE (Q.ISPEC `\r v. select_result cx (expr_type obj) r (ValueSubscript v)`
    (Q.GEN `k` framed_array_index_outcome_compose))) >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  qexists_tac `\H v ee u.
    expr_post H ctx func cenv cx idx (mid with gas_obs := []) sm si t ee v iop u /\
    u.vs_current_bb = si.cs_current_bb /\
    u.vs_inst_idx = LENGTH si.cs_current_insts` >>
  simp[vyperStorageTraceTheory.storage_trace_frame_select] >>
  `(!res out. (?exc. res = (INR exc : value + exception) /\
        expr_exit (INR exc : eval_result + exception) out) = expr_exit res out)` by
    (gen_tac >> Cases_on `res` >> simp[] >> rename1 `INR exc` >>
     qspec_then `Value` (mp_tac o REWRITE_RULE [FUN_EQ_THM]) expr_exit_success_map >>
     disch_then (qspec_then `INR exc : value + exception` mp_tac) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 raw.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.storage_trace_frame_select]) >>
  qpat_assum `!H. valid_horizon _ _ H raw.storage_trace ==> _`
    (qspec_then `storage_trace_horizon raw.storage_trace` mp_tac) >>
  impl_tac >- fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  strip_tac >>
  qpat_x_assum `!imarks raw v u. _` irule >> simp[] >>
  goal_assum drule
QED

(* Source observations are consumed by executions, but not by endpoint posts. *)
Theorem expr_post_initial_gas:
  expr_post H ctx func cenv cx e (es with gas_obs := gs) sa sb s0 ee v op s <=>
  expr_post H ctx func cenv cx e es sa sb s0 ee v op s
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
  stmt_state_rel H ctx func cenv cx (ee with gas_obs := gs) s <=>
  stmt_state_rel H ctx func cenv cx ee s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_gas_obs,
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
  vv_post H ctx func cenv cx e es sa sb s0 (ee with gas_obs := gs) r vv s <=>
  vv_post H ctx func cenv cx e es sa sb s0 ee r vv s
Proof
  `storage_well_formed_on cx (ee with gas_obs := gs) (FST H) <=>
   storage_well_formed_on cx ee (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
     simp[]) >>
  simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.locals_kept_def,
       loweringPostsTheory.popped_kept_def, stmt_state_rel_source_gas,
       vv_holds_source_gas, vv_at_source_gas, vv_own_source_gas]
QED
