(* The external-call address is the value child, viewed as a singleton
   argument list. Its actual scoped and native witnesses need no rebasing. *)
Theory entryCreateExtAddress
Ancestors
  entryCreateFocusSpec bodyFullExtCallTargetOutcome fragGasOriginPtrExec
  gasStorage vyperState vyperInterpreter exprSimDefs exprSimFullBundleProps
  s1PrefixDefs loweringPosts exprLowering entryCreateBodyCut entryCreateCompletedCut
  compileEnv fragExec

Theorem extcall_singleton_ignored[local]:
  ignore_bind (eval_exprs cx [e]) (return ()) =
  ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ())
Proof
  simp[FUN_EQ_THM,ignore_bind_def] >> qx_gen_tac `st` >>
  once_rewrite_tac[bind_def] >>
  Cases_on `vyperState$bind (eval_expr cx e) (read_result cx) st` >>
  rename1 `_ = (raw : value + exception, mid : evaluation_state)` >>
  Cases_on `raw` >> simp[extcall_singleton_source]
QED

Theorem extcall_singleton_cut[local]:
  create_operand_cut a b E C f tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s) ==>
  create_operand_cut a b E C f tops cx st0 (eval_exprs cx [e]) (es,s)
Proof
  simp[create_operand_cut_def,create_body_cut_def,extcall_singleton_source] >>
  rpt gen_tac >> disch_tac >> rpt strip_tac >>
  first_x_assum (drule_then (drule_then mp_tac)) >>
  disch_then (qspecl_then [`H`,`tail`] mp_tac) >>
  qmatch_goalsub_abbrev_tac `FST input` >>
  PairCases_on `input` >>
  simp[] >> rename1 `sum_CASE raw _ _` >> Cases_on `raw` >>
  fs[create_cut_failure_def]
QED

Theorem extcall_address_scoped_outcome[local]:
  expr_type addr = BaseT AddressT /\ expr_body_pre cenv cx env addr es /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sb) /\
  return_buf_frame d cenv sa s0 /\
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb
    (bind (eval_expr cx addr) (read_result cx)) (es,s0,G0,tn0)
    (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx addr (es,sa,sb,s0,ao,G0,tn0))
    (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sb
    (eval_exprs cx [addr]) (es,s0,G0,tn0)
    (extcall_address_post (DF,lo,d,ctx,func) cenv cx env addr
       (es,sa,sb,s0,ao,G0,tn0))
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `post_value_type cenv addr = BaseT AddressT` by
    simp[post_value_type_word,is_word_type_def] >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
  simp[extcall_singleton_ignored]
  >- (disj1_tac >> fs[gas_bad_storage_at_def,extcall_singleton_source] >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`sum_CASE res (\v. INL [v]) INR`,`ee`,`r`,`G'`,`tn'`] >>
      simp[extcall_singleton_source] >> rpt strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> simp[]
      >- (fs[expr_sim_full_post_def,expr_sim_full_endpoint_def] >> gvs[] >>
          `~t.vs_halted` by
            (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
          simp[exit_result_def] >> irule extcall_address_post_intro >> simp[] >>
          qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
          qpat_assum `!tail. _ = (INL _,_)`
            (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL])))
      >> disj2_tac >> Cases_on `res` >> gvs[create_operand_exit_post_def,halt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type])
  >> disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem extcall_address_scoped_cut:
  expr_type addr = BaseT AddressT /\ expr_body_pre cenv cx env addr es /\
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (BaseT AddressT) addr es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) cenv cx (BaseT AddressT) addr es
    (st0,sa,sb,sha,shb,ao,s0,G0,tn0) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (bind (eval_expr cx addr) (read_result cx)) (es,s0) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (eval_exprs cx [addr]) (es,s0,G0,tn0)
    (extcall_address_post (DF,lo,d,ctx,func) cenv cx env addr
      (es,sa,sb,s0,ao,G0,tn0)) (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (eval_exprs cx [addr]) (es,s0)
Proof
  strip_tac >> reverse conj_tac >- metis_tac[extcall_singleton_cut] >>
  fs[expr_sim_scoped_def] >> first_x_assum (drule_then assume_tac) >>
  irule extcall_address_scoped_outcome >>
  fs[expr_sim_full_pre_def]
QED
