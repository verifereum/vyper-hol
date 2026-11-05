Theory stmtForArrayMemoryRoundSupport
Ancestors
  stmtSimForArrayLoop stmtForArrayMemoryBodyEntry bodyMemoryDefs
  loweringPosts compileEnv venomState allocaHistory
  finite_map list gasSummary gasOutcome gasSummaryCompose gasExemptCert stmtSimForRounds
  fragGasMode fragGasPathMem stmtSimDeclGas
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
    stmt_state_rel ctx func ce cx es2 t /\
    (!x w. not_fresh_at sb0 x /\ lookup_var x s_body = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s_body.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    return_buf_frame d ce sb1 t /\ alloca_history func t /\
    s_body.vs_alloca_next <= t.vs_alloca_next) ==>
  stmt_lands lctx sb1 r t /\ ~t.vs_halted /\
  (r = INL () ==> ~block_is_terminated sb1) /\
  stmt_state_rel ctx func cenv cx (es2 with scopes := rest) t /\
  (!x w. not_fresh_at sb0 x /\ lookup_var x s_body = SOME w ==>
         lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s_body.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  return_buf_frame d cenv sb1 t /\ alloca_history func t /\
  s_body.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (es2 with scopes := rest) t` by
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

