(* Source cleanup adapters keep the target endpoint and its ghost unchanged. *)
Theory forPtrRangeRound
Ancestors forPtrRangeCallback forPtrRounds bodyPtrDefs loweringPosts exprSimDefs
  gasSummaryComposePtr fragGasPathPtr gasOutcome vyperInterpreter vyperState
Libs monadsyntax

Theorem for_body_cleanup_exec_ptr:
  gas_marked_exec_ptr D (ctx,func) PG (eval_stmts cx stmts)
    (es,s,G0,tn0) marks res ee G tn r /\ ee.scopes = sc :: rest ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (finally (try (do eval_stmts cx stmts; return F od)
                  handle_loop_exception) pop_scope)
    (es,s,G0,tn0) marks
    (case res of INL u => INL F
     | INR ex => if ex = BreakException then INL T
                 else if ex = ContinueException then INL F else INR ex)
    (ee with scopes := rest) G tn r
Proof
  simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
  gen_tac >> simp[finally_def, try_def, ignore_bind_def, bind_def] >>
  Cases_on `res` >> simp[return_def, pop_scope_def, bind_def] >>
  rename1 `handle_loop_exception ex` >>
  Cases_on `ex = BreakException` >> Cases_on `ex = ContinueException` >>
  gvs[handle_loop_exception_def, return_def, raise_def, bind_def, pop_scope_def]
QED

Theorem for_body_exit_cleanup_ptr:
  (!tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r) ==>
  ?ex. res = INR ex /\ ex <> BreakException /\ ex <> ContinueException /\
    !tail. stmt_exit_ptr RetQ ((ee with scopes := rest) with gas_obs := tail)
      (INR ex) gt r
Proof
  strip_tac >>
  `res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException` by
    (rpt conj_tac >> strip_tac >> gvs[] >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     Cases_on `r` >> simp[stmt_exit_ptr_def, expr_exit_def]) >>
  Cases_on `res` >> gvs[stmt_exit_ptr_def]
QED

Theorem for_exec_zero_suffix_ptr:
  gas_marked_exec_ptr D (ctx,func) PG source (es,s,G0,tn0)
    marks res ee G tn (OK t) /\
  gas_path_ptr D 0 ctx func PG G tn t 0 gf tf r ==>
  gas_marked_exec_ptr D (ctx,func) PG source (es,s,G0,tn0)
    marks res ee gf tf r
Proof
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED

(* Retain source evidence at normal posts so scope and P-preservation
   consumers need not unfold counted-path executions. *)
Theorem for_outcome_source_evidence_ptr:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\
      ?obs. source (es with gas_obs := obs) = (res,ee)) R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >>
      gvs[gas_summary_ptr_at_marked, gas_marked_exec_ptr_def] >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`res`, `es_end`] >> simp[] >>
      disj1_tac >> qexists_tac `gas_explicit marks s.vs_gas_readings` >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

(* Source-only facts enrich normal posts without inspecting execution. *)
Theorem for_outcome_semantic_post_ptr:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G0,tn0) Q R /\
  (!obs res ee G tn t.
    source (es with gas_obs := obs) = (res,ee) /\ Q res ee G tn t ==>
    Sem res ee) ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\ Sem res ee) R
Proof
  strip_tac >> dxrule for_outcome_source_evidence_ptr >> strip_tac >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

(* A checked administrative suffix may change the target and its ghost,
   but performs no source read and leaves source exceptions untouched. *)
Theorem for_outcome_zero_suffix_ptr:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G0,tn0) Q R /\
  (!res ee G tn t. Q res ee G tn t ==>
    ?gf tf u. gas_path_ptr D 0 ctx func PG G tn t 0 gf tf (OK u) /\
      Q' res ee gf tf u) ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G0,tn0) Q' R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_ptr_at_marked]
      >- (first_x_assum drule >> strip_tac >>
          drule_all for_exec_zero_suffix_ptr >> strip_tac >>
          goal_assum (drule_at Any) >> simp[]) >>
      goal_assum (drule_at Any) >> simp[]) >>
  disj2_tac >> metis_tac[]
QED
