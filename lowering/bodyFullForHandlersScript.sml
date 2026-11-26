(* Raw source cleanup and exceptional full-post transport for For bodies. *)
Theory bodyFullForHandlers
Ancestors
  bodyFullForControl bodyPtrDefs exprSimDefs stmtSimForArrayLoop
  createSizeExit gasOutcomeFullStmts gasOutcomeFull gasExemptCert gasSummary gasStorage
  fragGasOriginPtr fragGasOrigin vyperEvalPreservesScopes vyperInterpreter
  vyperState vyperStorageFootprint list

Theorem for_full_exit_scopes_gas_obs:
 !RetQ H cx ee (res:unit+exception) gt r ctx sc g.
 ((!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs:=tail) res gt r) /\
  halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s.
    (r=Halt s \/ ?ir. r=IntRet ir s) ==> allocas_below_fmp s)) ==>
 ((!tail. stmt_exit_ptr (RetQ H)
    ((ee with <|scopes:=sc;gas_obs:=g|>) with gas_obs:=tail) res gt r) /\
  halt_exit H cx (ee with <|scopes:=sc;gas_obs:=g|>) res r /\
  (ctx_has_dalloca ctx ==> !s.
    (r=Halt s \/ ?ir. r=IntRet ir s) ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >>
      simp[stmt_exit_ptr_def]) >>
  conj_tac >- (irule halt_exit_scopes_gas_obs >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem for_body_cleanup_full:
 !DF lo d ctx func PG tops cx st0 body es s G tn Q R.
 es.scopes <> [] /\
 gas_outcome_full (DF,lo,d,ctx,func,PG) tops cx st0
   (eval_stmts cx body) (es,s,G,tn) Q R ==>
 gas_outcome_full (DF,lo,d,ctx,func,PG) tops cx st0
   (finally (try (do eval_stmts cx body; return F od)
      handle_loop_exception) pop_scope) (es,s,G,tn)
   (\H res' ee G tn t. ?res sc.
      res' = (case res of INL u => INL F | INR ex =>
        if ex = BreakException then INL T else
        if ex = ContinueException then INL F else INR ex) /\
      Q H res (ee with scopes := sc::ee.scopes) G tn t)
   (\H res' ee gt r. ?res sc.
      res' = (case res of INL u => INL F | INR ex =>
        if ex = BreakException then INL T else
        if ex = ContinueException then INL F else INR ex) /\
      R H res (ee with scopes := sc::ee.scopes) gt r)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts` >>
  irule (INST_TYPE [alpha |-> ``:unit``] gas_outcome_full_handler_transport) >>
  qexistsl_tac [`Q`, `R`, `es`, `eval_stmts cx stmts`] >>
  simp[array_body_cleanup_bad] >> conj_tac
  >- suspend "exempt" >> suspend "ordinary"
QED

Resume for_body_cleanup_full[exempt]:
  rpt gen_tac >> strip_tac >>
  drule gas_exempt_cert_execution >> strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >>
  drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
  Cases_on `ee.scopes` >> gvs[] >>
  rename1 `ee.scopes = sc :: rest` >>
  pure_rewrite_tac[GSYM ignore_bind_def] >>
  qexistsl_tac [`err`, `ee with scopes := rest`] >>
  irule loop_body_cleanup_exempt_cert >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume for_body_cleanup_full[ordinary]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!tail. _` (qspec_then `[]` assume_tac) >>
  drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
  Cases_on `ee.scopes` >> gvs[] >>
  rename1 `ee.scopes = sc :: rest` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `gas_marked_exec T (ctx,func) (eval_stmts cx stmts)
     (es,s) marks res ee r` by
    (rewrite_tac[gas_marked_exec_def] >>
     metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase]) >>
  drule_all loop_body_cleanup_exec >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_exec T _ _ _ _ mapped _ _` >>
  qexistsl_tac [`marks`, `mapped`, `ee with scopes := rest`, `r`, `G'`, `tn'`] >>
  conj_tac >- fs[gas_marked_exec_def] >>
  simp[] >> rpt strip_tac >>
  `ee with <|scopes := sc :: rest; gas_obs := []|> =
   ee with gas_obs := []` by simp[evaluation_state_component_equality] >>
  simp[Abbr `mapped`]
  >- (disj1_tac >> qexistsl_tac [`res`, `sc`] >> fs[]) >>
  disj2_tac >> simp[] >> conj_tac
  >- (simp[create_size_exit_ok_def] >> strip_tac >>
      qpat_assum `create_size_exit_ok _ _ _`
        (mp_tac o REWRITE_RULE [create_size_exit_ok_def]) >>
      simp[] >> disch_then SUBST1_TAC >> simp[]) >>
  qexistsl_tac [`res`, `sc`] >> fs[]
QED

Finalise for_body_cleanup_full
