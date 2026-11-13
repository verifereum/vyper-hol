(* Counted mixed word/value-vv operand composition. *)
Theory bodyMemBopRestWordCompose
Ancestors
  exprSimBopRestWordCompose exprSimMemDefs exprSimBopRestWordFacts
  exprSimBopRestWordTail gasSummaryCompose gasExemptCert exprBopSimProps
  exprSimHypsDefs localPtrsProps exprSimProps
  gasStorage vyperStorageTrace vyperStorageFootprint

Theorem rest_word_mixed_outcome_mem:
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  compile_expr cenv (expr_type e2) e2 s1 = (vv,sm) /\
  compile_var_array_membership cenv x vv (expr_type e2) (bop = In) sm = (out,ct) /\
  fn_has_code sa s1 func /\ fn_has_code s1 sm func /\ fn_has_code sm ct func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    expr_res_ok es /\
  expr_sim_mem ctx func cenv cx (expr_type e1) e1 es /\
  (!left v1 mid t.
    gas_marked_exec T (ctx,func) (bind (eval_expr cx e1) (read_result cx))
      (es,s0) left (INL v1) mid (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_post H ctx func cenv cx e1 es sa s1 s0 (mid with gas_obs := []) v1 x t) /\
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    expr_store_bound cx (expr_type e1) v1 x t /\
    t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
    expr_vv_sim_mem ctx func cenv cx (expr_type e2) e2 (mid with gas_obs := []) /\
    gas_admissible (eval_expr cx e2) expr_vv_res_ok (mid with gas_obs := []) /\
    MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes /\
    !right tv fin u.
      gas_marked_exec T (ctx,func) (eval_expr cx e2)
        (mid with gas_obs := [],t) right (INL tv) fin (OK u) /\
      (!H. valid_horizon cx st0 H fin.storage_trace ==>
         vv_post H ctx func cenv cx e2 (mid with gas_obs := []) s1 sm t
           (fin with gas_obs := []) tv vv u) /\
      (?H. valid_horizon cx st0 H fin.storage_trace) /\
      vv_store_bound cx (expr_type e2) (lowered_value_type cenv e2)
        (fin with gas_obs := []) tv vv u /\
      u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next ==>
      ?v2 suffix last q v.
        (!tail. read_result cx tv (fin with gas_obs := tail) =
          (INL v2,fin with gas_obs := tail)) /\
        gas_marked_exec T (ctx,func)
          (\ee. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 ee,ee))
          (fin with gas_obs := [],u) suffix (INL v) last (OK q) /\
        (!H. valid_horizon cx st0 H fin.storage_trace ==>
           vv_post H ctx func cenv cx e2 (mid with gas_obs := []) s1 sm t
             (last with gas_obs := []) tv vv q) /\
        expr_val_rel cx ann v out q /\
        expr_val_at cenv cx ann sa ct (last with gas_obs := []) v out q /\
        q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts /\
        alloca_history func q /\ u.vs_alloca_next <= q.vs_alloca_next) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx)) (es,s0)
    (\H res ee q. ?v. res = INL v /\
      expr_post H ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
        es sa ct s0 ee v out q /\
      q.vs_current_bb = ct.cs_current_bb /\ q.vs_inst_idx = LENGTH ct.cs_current_insts /\
      alloca_history func q /\ s0.vs_alloca_next <= q.vs_alloca_next)
    (\H res ee r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[bop_first_admissible] >>
  `!v1 v2. storage_trace_frame
      (\es2. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es2, es2))` by
    simp[storage_trace_frame_def, exprBopSimDefsTheory.bop_result_def] >>
  `storage_trace_frame (bind (eval_expr cx e1) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `storage_trace_frame (eval_expr cx e2)` by simp[evaluate_storage_trace_frame] >>
  `storage_trace_frame (bind (eval_expr cx e2) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qexists `marks` >> disj1_tac >>
      pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_bad_storage_at_bind_left >> simp[] >>
      (rw[] >> irule storage_trace_frame_bind_all >> simp[storage_trace_frame_read_result]))
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists `marks` >> disj1_tac >>
           pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
           irule gas_bad_storage_at_bind_left >>
           reverse conj_tac
           >- (irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
           rw[] >> irule storage_trace_frame_bind_all >>
           simp[storage_trace_frame_read_result])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "left_normal"
      >> suspend "left_exit") >>
  suspend "left_exempt"
QED

Resume rest_word_mixed_outcome_mem[left_exit]:
  Cases_on `res`
  >- (qpat_x_assum `(\res ee r. _) _ _ _`
        (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac o
         SIMP_RULE (srw_ss()) []) >> gvs[]) >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists `marks` >> disj2_tac >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INR exc`, `es_end`, `r`] >> conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gnvs[] >> first_assum ACCEPT_TAC
QED

Resume rest_word_mixed_outcome_mem[left_exempt]:
  qexists `marks` >> disj2_tac >> disj2_tac >>
  drule (REWRITE_RULE [ETA_AX] bop_first_exempt_cert) >> metis_tac[]
QED

Resume rest_word_mixed_outcome_mem[left_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
    (drule_then strip_assume_tac) >>
  rename1 `expr_post _ _ _ _ _ e1 _ _ _ _ _ v1 _ t` >>
  qpat_x_assum `res = INL v1` SUBST_ALL_TAC >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  `?obs. es_end.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (bind (eval_expr cx e1) _)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    simp[valid_horizon_def] >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     expr_post H ctx func cenv cx e1 es sa s1 s0 (es_end with gas_obs := [])
       v1 x t` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> ?v. _` drule >> simp[]) >>
  qpat_x_assum `!left v1 mid t. _`
    (qspecl_then [`marks`, `v1`, `es_end`, `t`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     stmt_state_rel H ctx func cenv cx (es_end with gas_obs := []) t /\
     storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       drule >> simp[loweringPostsTheory.expr_post_def]) >>
  `~t.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def,
      fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `s1`, `sm`, `vv`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qexists `marks ++ marks'` >> disj1_tac >>
      pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_bad_storage_at_bind_right >>
      qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _` (irule_at Any) >>
      simp[] >> irule gas_bad_storage_at_bind_left >> simp[] >>
      irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_read_result])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gasSummaryTheory.gas_summary_at_def]) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end'.storage_trace`)
       >- (qexists `marks ++ marks'` >> disj1_tac >>
           pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
           irule gas_bad_storage_at_bind_right >>
           qpat_assum `gas_marked_exec _ _ _ (es, s0) _ _ _ _` (irule_at Any) >>
           simp[] >> irule gas_bad_storage_at_bind_left >> simp[] >>
           irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_read_result] >>
           irule gas_bad_storage_at_counted_prefix >> metis_tac[])) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end'.storage_trace)
         es_end'.storage_trace` by fs[storage_trace_domain_def]
      >- suspend "right_normal"
      >> suspend "right_exit") >>
  suspend "right_exempt"
QED

Resume rest_word_mixed_outcome_mem[right_exit]:
  Cases_on `res`
  >- (qpat_x_assum `(\res ee r. _) _ _ _`
        (qspec_then `storage_trace_horizon es_end'.storage_trace` mp_tac o
         SIMP_RULE (srw_ss()) []) >> gvs[]) >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR exc) _ _` >>
  qexists `marks ++ marks'` >> disj2_tac >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INR exc`, `es_end'`, `r`] >> conj_tac
  >- (pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
      irule gas_marked_exec_bind_normal >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL v1) _ _` (irule_at Any) >>
      BETA_TAC >> irule gas_marked_exec_bind_exception >>
      irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >>
  qpat_x_assum `(\res ee r. _) _ _ _`
    (qspec_then `storage_trace_horizon es_end'.storage_trace` mp_tac o
     SIMP_RULE (srw_ss()) []) >>
  simp[] >> strip_tac >>
  Cases_on `exc` >> Cases_on `r` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[exprSimDefsTheory.expr_exit_def]
QED

Resume rest_word_mixed_outcome_mem[right_exempt]:
  qexists `marks ++ marks'` >> disj2_tac >> disj2_tac >>
  irule_at Any rest_word_raw_second_exempt_cert >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any)
QED

Resume rest_word_mixed_outcome_mem[right_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?tv. _`
    (drule_then strip_assume_tac) >>
  rename1 `vv_post _ _ _ _ _ e2 _ _ _ _ _ tv _ u` >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  qpat_x_assum `r = OK u` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H es_end'.storage_trace ==>
     vv_post H ctx func cenv cx e2 (es_end with gas_obs := []) s1 sm t
       (es_end' with gas_obs := []) tv vv u` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H es_end'.storage_trace ==> ?tv. _`
       drule >> simp[]) >>
  `?obs'. es_end'.storage_trace = es_end.storage_trace ++ obs'` by
    (qpat_assum `gas_marked_exec _ _ (eval_expr cx e2) _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` assume_tac) >>
     qpat_assum `storage_trace_frame (eval_expr cx e2)`
       (fn th => drule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                   storage_trace_frame_prefix) th)) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end'.storage_trace ==>
       valid_horizon cx st0 H es_end.storage_trace` by
    simp[valid_horizon_def] >>
  qpat_x_assum `!right tv fin u. _`
    (qspecl_then [`marks'`, `tv`, `es_end'`, `u`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `last.storage_trace = es_end'.storage_trace` by
    (qpat_x_assum `gas_marked_exec _ _ (\ee. _) _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
     qpat_x_assum `_ with gas_obs := _ = _`
       (mp_tac o Q.AP_TERM `\s:evaluation_state. s.storage_trace`) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H last.storage_trace ==>
     expr_post H ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
       es sa ct s0 (last with gas_obs := []) v out q` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H es_end'.storage_trace` by metis_tac[] >>
     `valid_horizon cx st0 H es_end.storage_trace` by metis_tac[] >>
     `valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
     `expr_post H ctx func cenv cx e1 es sa s1 s0 (es_end with gas_obs := []) v1 x t`
       by metis_tac[] >>
     `vv_post H ctx func cenv cx e2 (es_end with gas_obs := []) s1 sm t
        (last with gas_obs := []) tv vv q` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
     irule rest_word_mixed_post >>
     qpat_assum `expr_post H _ _ _ _ e1 _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `vv_post H _ _ _ _ e2 _ _ _ _ _ _ _ q` (irule_at Any) >> simp[]) >>
  `s0.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  qexists `marks ++ marks' ++ suffix` >> disj2_tac >> disj1_tac >>
  irule rest_word_mixed_tail_summary >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise rest_word_mixed_outcome_mem
