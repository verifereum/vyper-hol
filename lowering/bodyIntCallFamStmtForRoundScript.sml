(* Arbitrary-post transport through a source loop round. *)
Theory bodyIntCallFamStmtForRound
Ancestors
  stmtForRangeMemoryRound stmtSimForRounds stmtSimDeclGas gasOutcome gasSummary
  gasSummaryCompose gasExemptCert gasContext fragGasMode
  vyperInterpreter vyperState vyperEvalPreservesScopes finite_map list
Libs
  monadsyntax

Theorem intcall_for_round_outcome:
  gas_outcome memory tops (ctx,func) (eval_stmts cx stmts)
    (esk with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes,s) Q R /\
  ~s.vs_halted /\
  (!res ee t gs. Q res ee t /\
    eval_stmts cx stmts
      ((esk with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv;
                          value := v; popped := []|>)) :: esk.scopes)
       with gas_obs := gs) = (res,ee) ==>
    (res = INL () \/ res = INR BreakException \/ res = INR ContinueException) /\
    ee.scopes <> [] /\
    ?u. gas_marked_path memory ctx func t 0 (OK u) /\
      H (INL (res = INR BreakException)) (ee with scopes := TL ee.scopes) u) /\
  (!res ee r gs. R res ee r /\
    eval_stmts cx stmts
      ((esk with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv;
                          value := v; popped := []|>)) :: esk.scopes)
       with gas_obs := gs) = (res,ee) ==>
    ee.scopes <> [] /\ ?ex. res = INR ex /\
      ex <> BreakException /\ ex <> ContinueException /\
      X (INR ex) (ee with scopes := TL ee.scopes) r) ==>
  gas_outcome memory tops (ctx,func)
    (do push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx stmts; return F od)
                     handle_loop_exception) pop_scope od)
    (esk,s) H X
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "normal"
  >- suspend "exit" >>
  suspend "exempt"
QED

Resume intcall_for_round_outcome[normal]:
  gvs[] >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  qpat_x_assum `!res ee t gs. Q _ _ _ /\ _ ==> _` drule >>
  disch_then (qspec_then `gas_explicit marks s.vs_gas_readings` mp_tac) >>
  impl_tac >- gvs[vyperStateTheory.evaluation_state_component_equality] >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `es_end.scopes` >- gvs[] >>
  drule_all for_round_marked >> disch_then assume_tac >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL (res = INR BreakException)`,
                `es_end with scopes := t'`, `OK u`] >>
  simp[] >>
  fs[gas_marked_exec_def] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED
Resume intcall_for_round_outcome[exit]:
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  qpat_x_assum `!res ee r gs. R _ _ _ /\ _ ==> _` drule >>
  disch_then (qspec_then `gas_explicit marks s.vs_gas_readings` mp_tac) >>
  impl_tac >- gvs[evaluation_state_component_equality] >>
  strip_tac >>
  Cases_on `es_end.scopes` >- gvs[] >>
  drule_all for_round_marked >> simp[] >> strip_tac >>
  qexists_tac `marks` >> disj1_tac >>
  rename1 `es_end.scopes = sc :: rest` >>
  qexistsl_tac [`INR ex`, `es_end with scopes := rest`, `r`] >>
  fs[gas_marked_exec_def]
QED
Resume intcall_for_round_outcome[exempt]:
  `ee.scopes <> []` by
    (drule gas_exempt_cert_execution >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[ignore_bind_def, bind_def] >>
     Cases_on `eval_stmts cx stmts
       ((esk with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv;
                           value := v; popped := []|>)) :: esk.scopes)
        with gas_obs := gas_explicit marks s.vs_gas_readings)` >>
     rename1 `_ = (res,st)` >> Cases_on `res` >> simp[] >> strip_tac >>
     gvs[] >> drule eval_stmts_preserves_scopes_len >> simp[] >>
     strip_tac >> Cases_on `ee.scopes` >> gvs[]) >>
  Cases_on `ee.scopes` >> gvs[] >>
  rename1 `ee.scopes = sc :: rest` >>
  `gas_marked_exec memory (ctx,func) (push_scope_with_var id tyv v)
    (esk,s) [] (INL ())
    (esk with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes) (OK s)` by
    (simp[gas_marked_exec_def, push_scope_with_var_def, return_def,
          evaluation_state_component_equality] >>
     irule gas_marked_path_from_mem >>
     simp[fragGasPathMemTheory.gas_path_mem_rules]) >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  drule gas_exempt_cert_bind_unit >> simp[] >> disch_then irule >>
  rewrite_tac[GSYM ignore_bind_def, ignore_bind_finally_unit,
              ignore_bind_try_unit, ignore_bind_return_twice] >>
  irule gas_exempt_cert_cleanup >> qexists_tac `ee` >>
  simp[pop_scope_def, return_def, evaluation_state_component_equality] >>
  irule gas_exempt_cert_handler >> qexists_tac `ee` >>
  simp[handle_loop_exception_def, ignore_bind_def, bind_def,
       raise_def, return_def] >>
  `!st gs scs. st with <|scopes := scs; gas_obs := gs|> =
                st with <|gas_obs := gs; scopes := scs|>`
    by simp[evaluation_state_component_equality] >>
  qpat_x_assum `!st gs scs. _` (fn th => pure_once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM ignore_bind_def] >>
  gvs[]
QED
Finalise intcall_for_round_outcome
