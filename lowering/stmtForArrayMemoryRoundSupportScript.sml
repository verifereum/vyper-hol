Theory stmtForArrayMemoryRoundSupport
Ancestors
  stmtSimForArrayLoop stmtForArrayMemoryBodyEntry bodyMemoryDefs
  loweringPosts compileEnv venomState allocaHistory
  finite_map list

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
