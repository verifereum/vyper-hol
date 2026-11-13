(* Outcome combinators for statement forms whose source wrapper is fixed
   (Expr, scoped bodies); shared by the full body leaves. *)
Theory gasOutcomeFullStmts
Ancestors
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr fragGasOrigin
  fragGasMode fragGasPath fragExec gasOutcome gasExemptCert gasSummary
  gasSummaryCompose gasStorage fragGasPathMem stmtSimExpr stmtSimIfProps
  bodyDeclMemoryCompose
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState list

Theorem origin_ptr_path_zero_prefix[local]:
  gas_origin_ptr_path cx st [] (OK s1, G1, tn1) /\
  gas_origin_ptr_path cx (s1, G1, tn1) marks out ==>
  gas_origin_ptr_path cx st marks out
Proof
  PairCases_on `out` >> strip_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ [] _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[]
QED

(* A step that consumes no GAS reading runs ahead of a full outcome on
   every horizon. *)
Theorem gas_outcome_full_zero_prefix:
  (!H. gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
         (s0, G0, tn0) [] (OK s1, G1, tn1)) /\
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s1, G1, tn1) Q R ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  `gas_path_mem ctx func s0 0 (OK s1)` by
    (qpat_assum `!H. gas_origin_ptr_path _ _ [] _`
       (qspec_then `ARB` assume_tac) >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- gvs[gas_bad_storage_at_def] >>
      qexistsl_tac [`H`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `!H. gas_origin_ptr_path _ _ [] _`
        (qspec_then `H` assume_tac) >>
      drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> gvs[] >>
      rpt strip_tac >> res_tac >> simp[] >>
      metis_tac[origin_ptr_path_zero_prefix]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`,
                `finish'`] >>
  conj_tac >- (irule gas_exempt_cert_zero_prefix_mem >> metis_tac[]) >>
  qexists_tac `H` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!H. gas_origin_ptr_path _ _ [] _` (qspec_then `H` assume_tac) >>
  drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]
QED

Theorem expr_stmt_bad_storage[local]:
  gas_bad_storage_at cx st0 (eval_expr cx e) es s marks ==>
  gas_bad_storage_at cx st0 (eval_stmt cx (Expr e)) es s marks
Proof
  strip_tac >>
  `eval_stmt cx (Expr e) =
     bind (eval_expr cx e)
       (\tv. type_check (~is_HashMapRef tv) "Expr HashMapRef")` by
    simp[Once evaluate_def] >>
  pop_assum SUBST1_TAC >> irule gas_bad_storage_at_bind_left >>
  simp[storage_trace_frame_checks]
QED

Theorem gas_outcome_full_expr_stmt:
  !DF lo explicit ctx func PG tops cx st0 e es s G tn Q R Q' R'.
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (eval_expr cx e) (es, s, G, tn) Q R /\
    (!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv, ee) ==>
                ~is_HashMapRef tv) /\
    (!H gs res ee G' tn' t.
       eval_expr cx e (es with gas_obs := gs) = (res, ee) /\
       Q H res ee G' tn' t /\ ~t.vs_halted ==>
       ?tv. res = INL tv /\ Q' H (INL ()) ee G' tn' t) /\
    (!H res ee gt r. R H res ee gt r ==>
                     ?exc. res = INR exc /\ R' H (INR exc) ee gt r) ==>
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (eval_stmt cx (Expr e)) (es, s, G, tn) Q' R'
Proof
  rpt strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_expr _ _) _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac
      >- (irule expr_stmt_bad_storage >> first_assum ACCEPT_TAC) >>
      metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[expr_stmt_exempt]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!tail. eval_expr _ _ (_ with gas_obs := _ ++ tail) = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE std_ss [APPEND_NIL])) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> gvs[]
  (* the expression ends normally on a value: the statement returns () *)
  >- (`~t.vs_halted` by
        metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                  gas_marked_path_exec, gas_path_normal] >>
      `?tv. res = INL tv` by
        (qpat_assum `!H gs res ee G' tn' t. _ /\ _ /\ _ ==> _`
           (drule_all_then strip_assume_tac) >> simp[]) >>
      gvs[] >>
      `~is_HashMapRef tv` by metis_tac[] >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`INL ()`, `ee`, `OK t`, `G'`, `tn'`] >>
      conj_tac >- (gen_tac >> irule eval_expr_stmt_success >> metis_tac[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> res_tac >> fs[fragExecTheory.exit_result_def] >>
      metis_tac[]) >>
  (* the expression exits: so does the statement *)
  qpat_assum `!H res ee gt r. R _ _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
  conj_tac >- (gen_tac >> irule eval_expr_stmt_exception >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> res_tac >> gvs[fragExecTheory.exit_result_def] >>
  res_tac >> gvs[]
QED

Theorem gas_bad_storage_at_finally[local]:
  gas_bad_storage_at cx st0 f es s0 marks /\ storage_trace_frame g ==>
  gas_bad_storage_at cx st0 (finally f g) es s0 marks
Proof
  rewrite_tac[gas_bad_storage_at_def] >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  qmatch_goalsub_abbrev_tac `finally f g esx` >>
  Cases_on `f esx` >> rename1 `f esx = (res, ee)` >>
  Cases_on `res` >> asm_simp_tac (srw_ss()) [finally_def] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `SND (h ee)` >>
  `storage_trace_frame h` by
    simp[Abbr `h`, storage_trace_frame_ignore_bind,
         storage_trace_frame_return, storage_trace_frame_raise] >>
  Cases_on `h ee` >> simp[] >>
  metis_tac[storage_trace_frame_preserves_bad_domain]
QED

Theorem scope_cleanup_bad_storage[local]:
  gas_bad_storage_at cx st0 (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes) s0 marks /\ ~s0.vs_halted ==>
  gas_bad_storage_at cx st0
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope))
    es s0 marks
Proof
  strip_tac >>
  `gas_marked_exec T (ARB, ARB) push_scope (es, s0) [] (INL ())
     (es with scopes := FEMPTY :: es.scopes) (OK s0)` by
    simp[if_push_scope_marked] >>
  simp[ignore_bind_def] >>
  `marks = [] ++ marks` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_bad_storage_at_bind_right >>
  first_assum (irule_at Any) >> simp[] >>
  irule gas_bad_storage_at_finally >>
  fs[gas_bad_storage_at_def, storage_trace_frame_pop_scope]
QED

(* The branch's statements under a pushed scope, then the pop. *)
Theorem gas_outcome_full_scope_cleanup:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes, s0, G0, tn0) Q R /\
  es.gas_obs = [] /\ ~s0.vs_halted ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope))
    (es, s0, G0, tn0)
    (\H res ee G tn t. ?sc.
       Q H res (ee with scopes := sc :: ee.scopes) G tn t /\
       !n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE)
    (\H res ee gt r. ?sc. R H res (ee with scopes := sc :: ee.scopes) gt r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac >- (irule scope_cleanup_bad_storage >> fs[]) >>
      fs[] >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (drule if_branch_cert_scopes >> strip_tac >>
      rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `leaf_pg`,
                    `leaf_g`, `leaf_tn`, `finish'`] >>
      conj_tac >- (
        irule eval_stmt_if_scoped_cert >> simp[if_push_scope_marked] >>
        qmatch_goalsub_abbrev_tac `gas_exempt_cert _ _ _ _ (esx, _)` >>
        `esx = es with scopes := FEMPTY :: es.scopes` by
          simp[Abbr `esx`, evaluation_state_component_equality] >>
        simp[]) >>
      qexists_tac `H` >> fs[]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `gas_marked_exec T (ctx, func) (eval_stmts cx ss)
     (es with scopes := FEMPTY :: es.scopes, s0) marks res ee r` by
    (rewrite_tac[gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
  drule if_branch_marked_scopes >> strip_tac >>
  drule_all if_branch_marked_cleanup >> strip_tac >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `ee with scopes := rest`, `r`, `G'`, `tn'`] >>
  conj_tac >- fs[gas_marked_exec_def] >>
  conj_tac >- fs[] >>
  rpt strip_tac >> fs[] >> res_tac >>
  `ee with gas_obs := [] =
   (ee with <|scopes := rest; gas_obs := []|>) with scopes := sc :: rest` by
    simp[evaluation_state_component_equality] >>
  pop_assum (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th])) >>
  fs[] >> metis_tac[]
QED
