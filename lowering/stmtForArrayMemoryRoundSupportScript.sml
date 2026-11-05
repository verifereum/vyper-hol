Theory stmtForArrayMemoryRoundSupport
Ancestors
  stmtSimForArrayLoop stmtForArrayMemoryBodyEntry bodyMemoryDefs
  loweringPosts compileEnv venomState allocaHistory
  finite_map list gasSummaryCompose gasExemptCert stmtSimForRounds
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
