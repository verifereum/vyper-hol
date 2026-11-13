Theory stmtForArrayMemoryRoundSupport
Ancestors
  stmtSimForArrayLoop stmtForArrayMemoryBodyEntry stmtForArrayMemorySupport bodyMemoryDefs
  loweringPosts compileEnv venomState allocaHistory
  finite_map list gasSummary gasOutcome gasSummaryCompose gasExemptCert stmtSimForRounds
  fragGasMode fragGasPathMem stmtSimDeclGas gasStorage vyperStorageFootprint
  vyperInterpreter vyperState
Libs
  monadsyntax

(* return_buf_frame_frame already supplies compiler/environment transport. *)
Theorem array_body_mem_post_projection:
  cenv_top_ext cenv bc ei.scopes /\
  eval_stmts cx stmts ei = (r,es2) /\
  es2.scopes = sc :: rest /\
  (!x. x IN FDOM sc ==> lookup_scopes x rest = NONE) /\
  cenv.ce_return_buf = bc.ce_return_buf /\
  (?ce.
    stmt_lands lctx sb1 r t /\ ~t.vs_halted /\
    (r = INL () ==> ~block_is_terminated sb1 /\ ce = bc') /\
    cenv_top_ext bc ce es2.scopes /\
    stmt_state_rel H ctx func ce cx es2 t /\
    storage_well_formed_on cx es2 (FST H) /\
    (!x w. not_fresh_at sb0 x /\ lookup_var x s_body = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s_body.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    return_buf_frame d ce sb1 t /\ alloca_history func t /\
    s_body.vs_alloca_next <= t.vs_alloca_next) ==>
  stmt_lands lctx sb1 r t /\ ~t.vs_halted /\
  (r = INL () ==> ~block_is_terminated sb1) /\
  stmt_state_rel H ctx func cenv cx (es2 with scopes := rest) t /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x s_body = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s_body.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  return_buf_frame d cenv sb1 t /\ alloca_history func t /\
  s_body.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx (es2 with scopes := rest) t` by
    (irule array_body_scope_projection >> conj_tac
     >- (qexists_tac `sc` >> simp[]) >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     qexistsl_tac [`bc`, `ce`] >> simp[]) >>
  `ce.ce_return_buf = cenv.ce_return_buf` by
    (fs[cenv_top_ext_def] >>
     qpat_x_assum `_ = bc`
       (mp_tac o AP_TERM ``\e:compile_env. e.ce_return_buf``) >> simp[]) >>
  `return_buf_frame d cenv sb1 t` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`ce`, `t`, `sb1`] >> simp[]) >>
  simp[]
QED

Theorem array_round_source_result:
  eval_stmts cx stmts
    (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes) = (r,ee) /\ ee.scopes = sc :: rest ==>
  (do push_scope_with_var id tv v;
      finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
        pop_scope od) ei =
  ((case r of INL u => INL F
     | INR e => if e = ContinueException then INL F
                else if e = BreakException then INL T else INR e),
   ee with scopes := rest)
Proof
  strip_tac >>
  `ei with scopes updated_by
     CONS (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) =
   ei with scopes :=
     (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>)) :: ei.scopes`
    by simp[evaluation_state_component_equality] >>
  simp[push_scope_with_var_def, ignore_bind_def, bind_def, return_def,
       finally_def, try_def, evaluation_state_fn_updates] >>
  Cases_on `r` >> gvs[bind_def, return_def, raise_def,
    handle_loop_exception_def, pop_scope_def] >>
  Cases_on `y = ContinueException` >> simp[return_def, raise_def] >>
  Cases_on `y = BreakException` >> simp[return_def, raise_def]
QED

Theorem array_round_exempt_cleanup:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmts cx stmts) (return ())) (ep,s)
    marks (err,ee) (leaf,fin) /\ ee.scopes = sc :: rest ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind
      (finally (try (ignore_bind (eval_stmts cx stmts) (return F))
        handle_loop_exception) pop_scope) (return ())) (ep,s)
    marks (err,ee with scopes := rest) (leaf,fin)
Proof
  strip_tac >>
  rewrite_tac[ignore_bind_finally_unit, ignore_bind_try_unit,
    ignore_bind_return_twice] >>
  irule gas_exempt_cert_cleanup >> qexists_tac `ee` >>
  conj_tac
  >- simp[pop_scope_def, return_def, evaluation_state_fn_updates] >>
  irule gas_exempt_cert_handler >> qexists_tac `ee` >>
  simp[handle_loop_exception_def, raise_def, ignore_bind_def, bind_def]
QED

Theorem array_round_marked_exec:
  gas_marked_exec memory (ctx,func) (eval_stmts cx stmts)
    (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes,s) marks r ee rr /\ ee.scopes = sc :: rest ==>
  gas_marked_exec memory (ctx,func)
    (do push_scope_with_var id tv v;
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (ei,s) marks
    (case r of INL u => INL F
       | INR e => if e = ContinueException then INL F
                  else if e = BreakException then INL T else INR e)
    (ee with scopes := rest) rr
Proof
  simp[gas_marked_exec_def] >> strip_tac >> gen_tac >>
  irule array_round_source_result >>
  simp[evaluation_state_fn_updates] >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  simp[evaluation_state_fn_updates]
QED

Theorem array_round_exempt:
  ~s.vs_halted /\
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (eval_stmts cx stmts) (return ()))
    (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes,s) marks (err,ee) (leaf,fin) /\
  ee.scopes = sc :: rest ==>
  gas_exempt_cert T tops (ctx,func)
    (ignore_bind (do push_scope_with_var id tv v;
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (return ())) (ei,s)
    marks (err,ee with scopes := rest) (leaf,fin)
Proof
  strip_tac >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule (SRULE [] (Q.INST [`left` |-> `[]`] (SPEC_ALL gas_exempt_cert_bind_unit))) >>
  qexistsl_tac [
    `ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes`, `s`] >>
  simp[] >> reverse conj_tac
  >- (simp[gas_marked_exec_def, push_scope_with_var_def, return_def, evaluation_state_component_equality,
        gas_marked_path_def] >> irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  rewrite_tac[GSYM ignore_bind_def] >>
  irule array_round_exempt_cleanup >>
  simp[] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED


(* The round cleanup only pops a scope, so a bad body trace stays bad. *)
Theorem array_round_push_exec[local]:
  ~s.vs_halted ==>
  gas_marked_exec T (ctx,func) (push_scope_with_var id tv v) (ei,s) [] (INL ())
    (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes) (OK s)
Proof
  simp[gas_marked_exec_def, push_scope_with_var_def, return_def,
       evaluation_state_component_equality, gas_marked_path_def] >>
  strip_tac >> irule (cj 1 gas_path_mem_rules) >> simp[]
QED

Theorem array_body_round_outcome_mem:
  ~s.vs_halted /\
  gas_outcome T tops (ctx,func) cx st0 (eval_stmts cx stmts)
    (ei with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes,s) B E /\
  (!gs r ee. eval_stmts cx stmts
    (ei with <|scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes; gas_obs := gs|>) = (r,ee) ==>
    ?sc rest. ee.scopes = sc :: rest) /\
  (!gs r ee t. eval_stmts cx stmts
    (ei with <|scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes; gas_obs := gs|>) = (r,ee) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> B H r ee t) ==>
    ?sc rest b u. ee.scopes = sc :: rest /\
    (case r of INL x => INL F
       | INR e => if e = ContinueException then INL F
                  else if e = BreakException then INL T else INR e) = INL b /\
    gas_marked_path T ctx func t 0 (OK u) /\
    (b ==> !H. valid_horizon cx st0 H ee.storage_trace ==>
             Done H (ee with scopes := rest) u) /\
    (~b ==> Next (ee with scopes := rest) u)) /\
  (!gs r ee rr sc rest. eval_stmts cx stmts
    (ei with <|scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tv; value := v; popped := []|>))
        :: ei.scopes; gas_obs := gs|>) = (r,ee) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> E H r ee rr) /\
    ee.scopes = sc :: rest ==>
    ?e. r = INR e /\ e <> BreakException /\ e <> ContinueException /\
        !H. valid_horizon cx st0 H ee.storage_trace ==>
          X H e (ee with scopes := rest) rr) ==>
  gas_outcome T tops (ctx,func) cx st0
    (do push_scope_with_var id tv v;
        finally (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
          pop_scope od) (ei,s)
    (\H res ee t. ?b. res = INL b /\ (b ==> Done H ee t) /\ (~b ==> Next ee t))
    (\H res ee rr. ?e. res = INR e /\ X H e ee rr)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      simp[Once ignore_bind_def] >>
      irule (SRULE [] (Q.INST [`left` |-> `[]`]
        gasStorageTheory.gas_bad_storage_at_bind_right)) >>
      irule_at Any array_round_push_exec >> simp[] >>
      irule array_body_cleanup_bad >>
      fs[gasStorageTheory.gas_bad_storage_at_def])
  >- suspend "summary" >>
  drule gas_exempt_cert_execution >> strip_tac >>
  `?sc rest. ee.scopes = sc :: rest` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> strip_tac >>
     gvs[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
     qpat_x_assum `!gs r ee. eval_stmts _ _ _ = _ ==> _` drule >>
     simp[] >> metis_tac[]) >>
  rename1 `gas_exempt_cert _ _ _ _ _ _ _ (leaf,fin)` >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `fin`] >>
  irule array_round_exempt >> simp[] >> metis_tac[]
QED

Resume array_body_round_outcome_mem[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
  disch_then (qx_choose_then `res` (qx_choose_then `es_end`
    (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
  qhdtm_assum `gas_marked_exec`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[evaluation_state_fn_updates] >> strip_tac >>
  `?sc rest. es_end.scopes = sc :: rest` by
    (qpat_x_assum `!gs r ee. eval_stmts _ _ _ = _ ==> _` drule >> simp[]) >>
  qpat_assum `gas_marked_exec _ _ (eval_stmts _ _) _ _ _ _ _`
    (fn th => assume_tac (MATCH_MP (GEN_ALL array_round_marked_exec)
       (CONJ th (ASSUME ``es_end.scopes = sc :: rest``)))) >>
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (strip_tac >> qexists_tac `marks` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
      goal_assum (drule_at Any) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
     es_end.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  strip_tac
  >- (gvs[] >>
      qpat_x_assum `!gs r ee t. _ /\ _ /\ _ ==> _` drule >>
      disch_then (qspec_then `t` mp_tac) >> impl_tac
      >- (simp[] >> metis_tac[]) >>
      strip_tac >> gvs[] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`INL b`, `es_end with scopes := rest`, `OK u`] >>
      simp[evaluation_state_fn_updates] >>
      fs[gas_marked_exec_def] >>
      drule_all gas_marked_path_then >> simp[]) >>
  qpat_x_assum `!gs r ee rr sc rest. _` drule >>
  disch_then (qspecl_then [`r`, `sc`, `rest`] mp_tac) >> impl_tac
  >- (simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR e`, `es_end with scopes := rest`, `r`] >>
  gvs[evaluation_state_fn_updates]
QED

Finalise array_body_round_outcome_mem

Theorem array_round_outcome_prefix_mem:
  gas_marked_path T ctx func s0 0 (OK s1) /\
  gas_outcome T tops (ctx,func) cx st0 source (es,s1) Q R ==>
  gas_outcome T tops (ctx,func) cx st0 source (es,s0) Q R
Proof
  strip_tac >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> fs[gasStorageTheory.gas_bad_storage_at_def] >> gen_tac >>
      first_x_assum (qspec_then `tail` mp_tac) >> asm_rewrite_tac[])
  >- (disj2_tac >> disj1_tac >> fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      fs[gas_marked_exec_def] >>
      metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  `gas_marked_exec T (ctx,func) (return ()) (es,s0) [] (INL ()) es (OK s1)` by
    simp[gas_marked_exec_def, return_def] >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u:unit. ignore_bind source (return ())`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> gvs[]
QED
