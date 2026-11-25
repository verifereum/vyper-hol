(* Request-prefix companion to bodyFullForHandlers. *)
Theory s1PrefixForHandlers
Ancestors
  s1PrefixPreds bodyFullForHandlers s1PrefixDefs vyperInterpreter vyperState

val _ = Parse.hide "body";

Theorem for_body_cleanup_prefix:
  !DF lo d ctx func PG tops cx st0 body es s G tn Q R.
  es.scopes <> [] /\
  gas_outcome_full (DF,lo,d,ctx,func,PG) tops cx st0
    (eval_stmts cx body) (es,s,G,tn) Q R /\
  gas_prefix_full (DF,lo,d,ctx,func,PG)
      cx st0 (eval_stmts cx body)
      (es,s,G,tn) ==>
  gas_prefix_full (DF,lo,d,ctx,func,PG)
      cx st0 (finally (try (do eval_stmts cx body; return F od)
       handle_loop_exception) pop_scope)
      (es,s,G,tn)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN assume_tac)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tail res ee obs_pre rq outcome sfx H. _`
    (qspec_then `tail` assume_tac) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `finally _ _ start` >>
  rename1 `eval_stmts cx stmts` >>
  Cases_on `eval_stmts cx stmts start` >> rename1 `_ = (result,mid)` >>
  Cases_on `result` >> Cases_on `mid.scopes` >>
  simp[finally_def, try_def, ignore_bind_def, bind_def, return_def,
       raise_def, pop_scope_def] >>
  rw[handle_loop_exception_def, COND_RATOR, return_def, raise_def,
     bind_def, pop_scope_def] >>
  gvs[]
QED
