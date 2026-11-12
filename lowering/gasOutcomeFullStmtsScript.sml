(* Outcome combinators for statement forms whose source wrapper is fixed
   (Expr, scoped bodies); shared by the full body leaves. *)
Theory gasOutcomeFullStmts
Ancestors
  gasOutcomeFullCompose gasOutcomeFull fragGasOriginPtr fragGasOrigin
  fragGasMode fragGasPath fragExec gasOutcome gasExemptCert gasSummary
  gasSummaryCompose stmtSimExpr stmtSimIfProps vyperInterpreter vyperState
  list

Theorem gas_outcome_full_expr_stmt:
  !D lo explicit ctx func PG tops cx e es s G tn Q R Q' R'.
    gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (eval_expr cx e)
      (es, s, G, tn) Q R /\
    (!gs tv ee. eval_expr cx e (es with gas_obs := gs) = (INL tv, ee) ==>
                ~is_HashMapRef tv) /\
    (!gs res ee G' tn' t.
       eval_expr cx e (es with gas_obs := gs) = (res, ee) /\
       Q res ee G' tn' t /\ ~t.vs_halted ==>
       ?tv. res = INL tv /\ Q' (INL ()) ee G' tn' t) /\
    (!res ee gt r. R res ee gt r ==>
                   ?exc. res = INR exc /\ R' (INR exc) ee gt r) ==>
    gas_outcome_full (D, lo, explicit, ctx, func, PG) tops
      (eval_stmt cx (Expr e)) (es, s, G, tn) Q' R'
Proof
  rewrite_tac[gas_outcome_full_def] >> rpt strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >>
      `~t.vs_halted` by
        metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                  gas_marked_path_exec, gas_path_normal] >>
      qpat_assum `!tail. eval_expr _ _ (_ with gas_obs := _ ++ tail) = _`
        (qspec_then `[]` (assume_tac o SIMP_RULE std_ss [APPEND_NIL])) >>
      qpat_x_assum `!gs res ee G' tn' t. _ /\ _ /\ _ ==> _`
        (drule_all_then strip_assume_tac) >> gvs[] >>
      qexistsl_tac [`INL ()`, `ee`, `OK t`, `G'`, `tn'`] >> simp[] >>
      gen_tac >> irule eval_expr_stmt_success >> metis_tac[])
  >- (disj1_tac >>
      qpat_x_assum `!res ee gt r. R _ _ _ _ ==> _`
        (drule_then strip_assume_tac) >> gvs[] >>
      qexistsl_tac [`INR exc`, `ee`, `r`, `G'`, `tn'`] >> simp[] >>
      metis_tac[eval_expr_stmt_exception]) >>
  disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `leaf_pg`, `leaf_g`, `leaf_tn`, `finish'`] >>
  simp[] >> irule expr_stmt_exempt >> simp[]
QED

(* The branch's statements under a pushed scope, then the pop. *)
val if_scope_cleanup_normal_tac =
  `gas_marked_exec T (ctx, func) (eval_stmts cx ss)
     (es with scopes := FEMPTY :: es.scopes, s0) marks res ee r` by
    (rewrite_tac[gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
  drule if_branch_marked_scopes >> strip_tac >>
  drule_all if_branch_marked_cleanup >> strip_tac >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`res`, `ee with scopes := rest`, `r`, `G'`, `tn'`] >>
  (conj_tac >- fs[gas_marked_exec_def]) >>
  `ee with gas_obs := [] =
   (ee with <|scopes := rest; gas_obs := []|>) with scopes := sc :: rest` by
    simp[evaluation_state_component_equality] >>
  pop_assum (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th])) >>
  fs[] >> metis_tac[];

Theorem gas_outcome_full_scope_cleanup:
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops (eval_stmts cx ss)
    (es with scopes := FEMPTY :: es.scopes, s0, G0, tn0) Q R /\
  es.gas_obs = [] /\ ~s0.vs_halted ==>
  gas_outcome_full (D, lo, explicit, ctx, func, PG) tops
    (ignore_bind push_scope (finally (eval_stmts cx ss) pop_scope))
    (es, s0, G0, tn0)
    (\res ee G tn t. ?sc.
       Q res (ee with scopes := sc :: ee.scopes) G tn t /\
       !n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE)
    (\res ee gt r. ?sc. R res (ee with scopes := sc :: ee.scopes) gt r)
Proof
  rewrite_tac[gas_outcome_full_def] >> strip_tac
  >- if_scope_cleanup_normal_tac
  >- if_scope_cleanup_normal_tac >>
  drule if_branch_cert_scopes >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `leaf_pg`,
                `leaf_g`, `leaf_tn`, `finish'`] >> simp[] >>
  irule eval_stmt_if_scoped_cert >> simp[if_push_scope_marked] >>
  qmatch_goalsub_abbrev_tac `gas_exempt_cert _ _ _ _ (esx, _)` >>
  `esx = es with scopes := FEMPTY :: es.scopes` by
    simp[Abbr `esx`, evaluation_state_component_equality] >>
  simp[]
QED
