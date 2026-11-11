(* Outcome cleanup for checked For rounds; certificates remain source-level. *)
Theory forPtrRoundCleanup
Ancestors forPtrRangeRound gasExemptCert gasSummaryComposePtr gasSummaryCompose
  fragGasPathPtr
  gasSummary vyperState vyperInterpreter
Libs monadsyntax

Theorem for_body_cleanup_exempt_cert:
  !body finish. gas_exempt_cert D tops (ctx,func)
    (ignore_bind (body : evaluation_state -> unit evaluation_result) (return ()))
    (es,s) marks (err,ee) (leaf,finish) /\ ee.scopes = sc :: rest ==>
  gas_exempt_cert D tops (ctx,func)
    (ignore_bind
      (finally (try (do body; return F od) handle_loop_exception) pop_scope)
      (return ()))
    (es,s) marks (err,ee with scopes := rest) (leaf,finish)
Proof
  rpt strip_tac >>
  rewrite_tac[ignore_bind_finally_unit, ignore_bind_try_unit,
              ignore_bind_return_twice] >>
  irule gas_exempt_cert_cleanup >> qexists_tac `ee` >>
  conj_tac >- simp[pop_scope_def, return_def] >>
  irule gas_exempt_cert_handler >> qexists_tac `ee` >>
  simp[handle_loop_exception_def, ignore_bind_def, bind_def, raise_def]
QED

Theorem for_round_exempt_cert_ptr:
  !body finish. gas_marked_exec_ptr D (ctx,func) PG (push_scope_with_var id tv v)
    (es,s,G0,tn0) [] (INL ())
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: es.scopes) G tn (OK t) /\
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (body : evaluation_state -> unit evaluation_result) (return ()))
    (es with <|scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: es.scopes; gas_obs := []|>,t) marks (err,ee) (leaf,finish) /\
  ee.scopes = sc :: rest ==>
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind
      (do push_scope_with_var id tv v;
          finally (try (do body; return F od) handle_loop_exception) pop_scope od)
      (return ()))
    (es,s) marks (err,ee with scopes := rest) (leaf,finish)
Proof
  rpt strip_tac >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_unit >> simp[] >> disch_then irule >>
  rewrite_tac[GSYM ignore_bind_def] >>
  irule for_body_cleanup_exempt_cert >> goal_assum (drule_at Any) >> simp[]
QED

Theorem for_body_marked_scope_ptr:
  es.scopes <> [] /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_stmts cx stmts)
    (es,s,G0,tn0) marks res ee G tn r ==>
  ee.scopes <> []
Proof
  simp[gas_marked_exec_ptr_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
  drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_dom >>
  simp[vyperEvalPreservesScopesTheory.preserves_scopes_dom_def] >>
  Cases_on `ee.scopes` >> gvs[] >> Cases_on `es.scopes` >> gvs[]
QED

Theorem for_body_exempt_scope:
  !finish. es.scopes <> [] /\
  gas_exempt_cert D tops (ctx,func)
    (ignore_bind (eval_stmts cx stmts) (return ()))
    (es,s) marks (err,ee) (leaf,finish) ==>
  ee.scopes <> []
Proof
  rpt strip_tac >> drule gas_exempt_cert_execution >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def, AllCaseEqs()] >> strip_tac >>
  drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_dom >>
  simp[vyperEvalPreservesScopesTheory.preserves_scopes_dom_def] >>
  Cases_on `ee.scopes` >> gvs[] >> Cases_on `es.scopes` >> gvs[]
QED

Theorem for_body_cleanup_outcome_ptr:
  es.scopes <> [] /\
  gas_outcome_ptr D tops (ctx,func) PG (eval_stmts cx stmts)
    (es,s,G0,tn0) Q R /\
  (!res ee G tn t.
    Q res ee G tn t ==>
    Q' (case res of INL u => INL F
        | INR ex => if ex = BreakException then INL T
                    else if ex = ContinueException then INL F else INR ex)
      (ee with scopes := TL ee.scopes) G tn t) /\
  (!res ee gt r.
    R res ee gt r ==>
    R' (case res of INL u => INL F
        | INR ex => if ex = BreakException then INL T
                    else if ex = ContinueException then INL F else INR ex)
      (ee with scopes := TL ee.scopes) gt r) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (finally (try (do eval_stmts cx stmts; return F od)
                  handle_loop_exception) pop_scope)
    (es,s,G0,tn0) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (gvs[gas_summary_ptr_at_marked] >> suspend "marked") >>
  suspend "exempt"
QED

Resume for_body_cleanup_outcome_ptr[marked]:
  markerLib.RESUME_TAC >> (
  `es_end.scopes <> []` by (drule_all for_body_marked_scope_ptr >> simp[]) >>
  Cases_on `es_end.scopes` >> gvs[] >>
  drule_all for_body_cleanup_exec_ptr >> strip_tac >>
  qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >>
  simp[] >> first_x_assum drule >> simp[])
QED

Resume for_body_cleanup_outcome_ptr[exempt]:
  `ee.scopes <> []` by (drule_all for_body_exempt_scope >> simp[]) >>
  Cases_on `ee.scopes` >> gvs[] >>
  qexists_tac `marks` >> disj2_tac >>
  drule_all for_body_cleanup_exempt_cert >> metis_tac[]
QED
Finalise for_body_cleanup_outcome_ptr
