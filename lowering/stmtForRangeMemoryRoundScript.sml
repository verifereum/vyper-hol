(* Source loop-round interfaces for counted memory fragments. *)
Theory stmtForRangeMemoryRound
Ancestors
  stmtSimForLoop
  stmtSimForRounds stmtSimDeclGas stmtSimDefs exprSimDefs gasContext gasSummary vyperInterpreter vyperState
  vyperEvalPreservesScopes gasExemptCert gasOutcome fragGasMode fragGasPathMem list finite_map
  gasStorage vyperStorageFootprint vyperStorageTrace
Libs
  monadsyntax

Theorem for_round_body_admissible:
  !cx tyv id stmts v vs lctx esk ex inc.
    gas_admissible (eval_for cx tyv id stmts (Value v :: vs)) (stmt_res_ok lctx) esk ==>
    gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop ex inc))
      (esk with scopes :=
        (FEMPTY |+ (id, <| assignable := F; type := tyv;
                          value := v; popped := [] |>)) :: esk.scopes)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[gas_admissible_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[stmt_res_ok_def] >>
  rename1 `eval_stmts cx stmts _ = (INR err, ee)` >>
  Cases_on `err = BreakException` >- simp[stmt_res_ok_def] >>
  Cases_on `err = ContinueException` >- simp[stmt_res_ok_def] >>
  `ee.scopes <> []` by
    (drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
     Cases_on `ee.scopes` >> gvs[]) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  rewrite_tac[gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[eval_for_cons_value_round, push_scope_with_var_def, return_def,
       ignore_bind_def, bind_def, finally_def, try_def,
       handle_loop_exception_def] >>
  `esk with <|scopes updated_by
     CONS (FEMPTY |+ (id, <|assignable := F; type := tyv;
                            value := v; popped := []|>)); gas_obs := gs|> =
   esk with <|gas_obs := gs; scopes :=
     (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes|>`
    by simp[evaluation_state_component_equality] >>
  qpat_x_assum `_ = esk with <|gas_obs := gs; scopes := _|>`
    (fn th => pure_rewrite_tac[th]) >>
  simp[raise_def] >>
  Cases_on `ee.scopes` >> gvs[pop_scope_def, return_def, raise_def] >>
  simp[stmt_res_ok_def]
QED

Theorem for_round_marked:
  gas_marked_exec memory (ctx,func) (eval_stmts cx stmts)
    (esk with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes,s)
    marks res ee r /\ ee.scopes = sc :: rest ==>
  gas_marked_exec memory (ctx,func)
    (do push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx stmts; return F od)
                     handle_loop_exception) pop_scope od)
    (esk,s) marks
    (case res of INL u => INL F
     | INR e => if e = ContinueException then INL F
                else if e = BreakException then INL T else INR e)
    (ee with scopes := rest) r
Proof
  strip_tac >>
  `!st. st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv;
                             value := v; popped := []|>)) =
    st with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                         value := v; popped := []|>)) :: st.scopes`
    by simp[evaluation_state_component_equality] >>
  gvs[gas_marked_exec_def] >> gen_tac >>
  simp[push_scope_with_var_def, ignore_bind_def, bind_def, return_def] >>
  simp[finally_def, try_def, bind_def, return_def,
       handle_loop_exception_def] >>
  Cases_on `res`
  >- simp[ignore_bind_def, bind_def, pop_scope_def, return_def] >>
  rename1 `INR err` >> Cases_on `err` >>
  simp[ignore_bind_def, bind_def, pop_scope_def, return_def, raise_def]
QED

Theorem for_round_cert:
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (eval_stmts cx stmts) (return ()))
    ((esk with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes)
     with gas_obs := [],s)
    marks (err,ee) (leaf,finish_state) /\
  ee.scopes = sc :: rest /\ ~s.vs_halted ==>
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind
      (do push_scope_with_var id tyv v;
          finally (try (do eval_stmts cx stmts; return F od)
                       handle_loop_exception) pop_scope od) (return ()))
    (esk,s) marks (err,ee with scopes := rest) (leaf,finish_state)
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (push_scope_with_var id tyv v)
    (esk,s) [] (INL ())
    (esk with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes) (OK s)` by
    (simp[gas_marked_exec_def, push_scope_with_var_def, return_def,
          evaluation_state_component_equality] >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
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
  first_assum ACCEPT_TAC
QED

(* A body run that left the storage domain makes the whole round one. *)
Theorem for_round_bad_mem[local]:
  gas_bad_storage_at cx st0 (eval_stmts cx stmts)
    (esk with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes) s marks /\
  ~s.vs_halted ==>
  gas_bad_storage_at cx st0
    (do push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx stmts; return F od)
                     handle_loop_exception) pop_scope od) esk s marks
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (push_scope_with_var id tyv v)
    (esk,s) [] (INL ())
    (esk with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes) (OK s)` by
    (simp[gas_marked_exec_def, push_scope_with_var_def, return_def,
          evaluation_state_component_equality] >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  PURE_ONCE_REWRITE_TAC[ignore_bind_def] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`]
    gasStorageTheory.gas_bad_storage_at_bind_right)) >>
  qpat_assum `gas_marked_exec _ _ (push_scope_with_var _ _ _) _ _ _ _ _`
    (irule_at Any) >>
  simp[gasStorageTheory.gas_bad_storage_at_def] >> gen_tac >>
  qmatch_goalsub_abbrev_tac `finally _ _ st` >>
  `?xs. (SND (finally (try (ignore_bind (eval_stmts cx stmts) (return F))
            handle_loop_exception) pop_scope st)).storage_trace =
         (SND (eval_stmts cx stmts st)).storage_trace ++ xs` by
    (irule finally_try_trace >>
     simp[vyperStorageTraceTheory.storage_trace_frame_loop_handler,
          vyperStorageTraceTheory.storage_trace_frame_pop_scope]) >>
  qpat_x_assum `gas_bad_storage_at _ _ _ _ _ _` mp_tac >>
  simp[gasStorageTheory.gas_bad_storage_at_def] >>
  disch_then (qspec_then `tail` mp_tac) >>
  simp[Abbr `st`] >>
  metis_tac[vyperStorageFootprintTheory.storage_trace_domain_prefix]
QED

Theorem for_round_outcome_mem:
  gas_outcome T tops (ctx,func) cx st0 (eval_stmts cx stmts)
    (esk with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: esk.scopes,s)
    B (\H res ee r. !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r) /\
  ~s.vs_halted /\
  (!res ee t gs.
     (?H. valid_horizon cx st0 H ee.storage_trace) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> B H res ee t) /\
     eval_stmts cx stmts
       ((esk with scopes :=
         (FEMPTY |+ (id, <|assignable := F; type := tyv;
                           value := v; popped := []|>)) :: esk.scopes)
        with gas_obs := gs) = (res,ee) ==>
     (res = INL () \/ res = INR BreakException \/ res = INR ContinueException) /\
     ee.scopes <> [] /\
     ?u. gas_path_mem ctx func t 0 (OK u) /\
         !H. valid_horizon cx st0 H ee.storage_trace ==>
           Q H (INL (res = INR BreakException)) (ee with scopes := TL ee.scopes) u) ==>
  gas_outcome T tops (ctx,func) cx st0
    (do push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx stmts; return F od)
                     handle_loop_exception) pop_scope od)
    (esk,s) Q
    (\H res ee r. ?ex. res = INR ex /\
                 !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) (INR ex) r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >> strip_tac
  >- suspend "bad"
  >- suspend "normal"
  >- suspend "exit" >>
  suspend "exempt"
QED

Resume for_round_outcome_mem[bad]:
  qexists_tac `marks` >> disj1_tac >> irule for_round_bad_mem >> simp[]
QED

Resume for_round_outcome_mem[normal]:
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (qexists_tac `marks` >> disj1_tac >> irule for_round_bad_mem >> simp[] >>
      irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `?He. valid_horizon cx st0 He es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  qpat_x_assum `!res ee t gs. _`
    (qspecl_then [`res`, `es_end with gas_obs := []`, `t`,
                  `gas_explicit marks s.vs_gas_readings`] mp_tac) >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  Cases_on `es_end.scopes` >> gvs[] >>
  drule_all for_round_marked >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `Q _ (INL broke) _ u` >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL broke`,
                `es_end with scopes := t'`, `OK u`] >>
  simp[Abbr `broke`] >>
  gvs[gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED

Resume for_round_outcome_mem[exit]:
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (qexists_tac `marks` >> disj1_tac >> irule for_round_bad_mem >> simp[] >>
      irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `?He. valid_horizon cx st0 He es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `!tail. stmt_exit (RetQ He) (es_end with gas_obs := tail) res r` by
    (fs[] >> metis_tac[]) >>
  Cases_on `res` >- gvs[stmt_exit_def, expr_exit_def] >>
  rename1 `stmt_exit (RetQ He) _ (INR err) r` >>
  Cases_on `err = BreakException`
  >- (Cases_on `r` >> gvs[stmt_exit_def, expr_exit_def]) >>
  Cases_on `err = ContinueException`
  >- (Cases_on `r` >> gvs[stmt_exit_def, expr_exit_def]) >>
  `es_end.scopes <> []` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
     drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
     Cases_on `es_end.scopes` >> gvs[]) >>
  Cases_on `es_end.scopes` >> gvs[] >>
  drule_all for_round_marked >> simp[] >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR err`, `es_end with scopes := t`, `r`] >>
  simp[] >> disj2_tac >>
  gvs[stmt_exit_def] >> metis_tac[]
QED

Resume for_round_outcome_mem[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
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
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := t`, `leaf`, `target`] >>
  irule for_round_cert >> simp[] >>
  `!st gs scs. st with <|gas_obs := gs; scopes := scs|> =
                st with <|scopes := scs; gas_obs := gs|>`
    by simp[evaluation_state_component_equality] >>
  qpat_x_assum `!st gs scs. _` (fn th => pure_once_rewrite_tac[th]) >>
  first_assum ACCEPT_TAC
QED
Finalise for_round_outcome_mem

(* A zero-observation target entry can precede any counted source outcome,
   including an exempt certificate. *)
Theorem for_marked_zero_prefix_mem[local]:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_marked_exec T (ctx,func) source (es,s1) marks res ee r ==>
  gas_marked_exec T (ctx,func) source (es,s0) marks res ee r
Proof
  strip_tac >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[]) >>
  fs[gas_marked_exec_def, gas_marked_path_def] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem for_cert_zero_prefix_mem[local]:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_exempt_cert T tops (ctx,func) source (es,s1)
    marks (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert T tops (ctx,func) source (es,s0)
    marks (err,ee) (leaf,finish_state)
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (return ()) (es,s0) [] (INL ()) es (OK s1)` by
    simp[gas_marked_exec_def, gas_marked_path_def, return_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u. source`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> simp[]
QED

Theorem for_outcome_zero_prefix_mem:
  gas_path_mem ctx func s0 0 (OK s1) /\
  gas_outcome T tops (ctx,func) cx st0 source (es,s1) Q R ==>
  gas_outcome T tops (ctx,func) cx st0 source (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      `s1.vs_gas_readings = s0.vs_gas_readings` by
        (drule gas_path_mem_ok_suffix >> simp[]) >>
      fs[gasStorageTheory.gas_bad_storage_at_def])
  >- (disj2_tac >> disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      metis_tac[for_marked_zero_prefix_mem]) >>
  disj2_tac >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
  irule for_cert_zero_prefix_mem >> qexists_tac `s1` >> simp[]
QED

Theorem for_round_false_source_mem:
  gas_marked_exec memory (ctx,func)
    (do push_scope_with_var id tyv v;
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
                pop_scope od) (ei,s) marks (INL F) mid r ==>
  ?gs r2 es2 sc rest.
    eval_stmts cx stmts
      (ei with <|scopes := (FEMPTY |+ (id,
        <|assignable := F; type := tyv; value := v; popped := []|>)) :: ei.scopes;
                 gas_obs := gs|>) = (r2,es2) /\
    (r2 = INL () \/ r2 = INR ContinueException) /\
    es2.scopes = sc :: rest /\
    (es2 with scopes := rest) = (mid with gas_obs := [])
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  simp[push_scope_with_var_def, ignore_bind_def, bind_def, return_def] >>
  `!st. st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)) =
    st with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)) :: st.scopes`
    by simp[evaluation_state_component_equality] >>
  pure_asm_rewrite_tac[] >>
  simp[finally_def, try_def, bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `eval_stmts cx stmts E` >>
  Cases_on `eval_stmts cx stmts E` >> rename1 `eval_stmts cx stmts E = (res,ee)` >>
  `ee.scopes <> []` by
    (drule eval_stmts_preserves_scopes_len >> simp[Abbr `E`] >>
     strip_tac >> Cases_on `ee.scopes` >> gvs[]) >>
  Cases_on `ee.scopes` >- gvs[] >>
  simp[finally_def, try_def, ignore_bind_def, bind_def, return_def,
       handle_loop_exception_def] >>
  Cases_on `res` >- suspend "normal" >>
  rename1 `INR err` >> Cases_on `err` >>
  simp[pop_scope_def, return_def, raise_def] >> suspend "continue"
QED
Resume for_round_false_source_mem[normal]:
  Cases_on `x` >> simp[pop_scope_def, return_def] >> strip_tac >>
  qexistsl_tac [`gas_explicit marks s.vs_gas_readings`, `INL ()`, `ee`, `h`, `t`] >>
  gvs[Abbr `E`]
QED
Resume for_round_false_source_mem[continue]:
  strip_tac >>
  qexistsl_tac [`gas_explicit marks s.vs_gas_readings`, `INR ContinueException`, `ee`, `h`, `t`] >>
  gvs[Abbr `E`]
QED
Finalise for_round_false_source_mem

Theorem for_outcome_consequence_mem:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s) Q R /\
  (!H res ee t. Q H res ee t ==> Q' H res ee t) /\
  (!H res ee r. R H res ee r ==> R' H res ee r) ==>
  gas_outcome memory tops (ctx,func) cx st0 source (es,s) Q' R'
Proof
  rw[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `marks` >> metis_tac[]
QED
