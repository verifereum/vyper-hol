(* Outcome combinators for statement forms whose source wrapper is fixed;
   shared by the full body leaves. *)
Theory gasOutcomeFullStmts
Ancestors
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr fragGasOrigin
  fragGasMode fragGasPath fragExec gasOutcome gasExemptCert gasSummary
  gasSummaryCompose gasStorage fragGasPathMem stmtSimExpr
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState list

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
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> irule expr_stmt_bad_storage >> first_assum ACCEPT_TAC)
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >> metis_tac[expr_stmt_exempt]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
  Cases_on `storage_trace_domain cx st0 ee.storage_trace`
  >~ [`~storage_trace_domain _ _ _`]
  >- (disj1_tac >> irule expr_stmt_bad_storage >>
      irule gas_bad_storage_at_endpoint >> metis_tac[]) >>
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
      rpt strip_tac >> res_tac >> fs[fragExecTheory.exit_result_def] >>
      metis_tac[]) >>
  (* the expression exits: so does the statement *)
  qpat_assum `!H res ee gt r. R _ _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >>
  conj_tac >- (gen_tac >> irule eval_expr_stmt_exception >> metis_tac[]) >>
  rpt strip_tac >> res_tac >> gvs[fragExecTheory.exit_result_def] >>
  res_tac >> gvs[]
QED
