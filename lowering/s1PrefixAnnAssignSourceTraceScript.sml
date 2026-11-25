(* The source declaration adds no request after evaluating its RHS. *)
Theory s1PrefixAnnAssignSourceTrace
Ancestors
  s1PrefixDefs stmtSimDeclSource vyperInterpreter vyperState

Theorem annassign_prefix_from_rhs_trace:
  evaluate_type (get_tenv cx) typ = SOME dtv /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
    cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
    cx st0 (eval_stmt cx (AnnAssign id typ e)) (es,s,G,tn)
Proof
  strip_tac >> drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  rewrite_tac[gas_prefix_full_def] >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN assume_tac)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `start = es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail` >>
  Cases_on `bind (eval_expr cx e) (read_result cx) start` >>
  rename1 `_ = (result,mid)` >>
  qpat_x_assum `bind (bind _ _) (new_variable _ _) _ = _` mp_tac >>
  simp[Once bind_def] >> Cases_on `result` >> simp[] >> strip_tac
  >- (`ee.storage_trace = mid.storage_trace` by
       (qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
        simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
             type_check_def, assert_def] >>
        Cases_on `lookup_scopes id mid.scopes` >> Cases_on `mid.scopes` >>
        simp[raise_def, set_scopes_def, return_def] >> strip_tac >> gvs[]) >>
      unabbrev_all_tac >> metis_tac[]) >>
  gvs[] >> unabbrev_all_tac >> metis_tac[]
QED
