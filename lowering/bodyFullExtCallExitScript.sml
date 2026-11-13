(* Exceptional external-call branches on the joint judgment. *)
Theory bodyFullExtCallExit
Ancestors
  bodyFullExtCallPrecheckExit bodyFullExtCallFailurePath gasOutcomeFullCompose
  exprSimExtCallCase vyperInterpreter vyperState

Theorem extcall_precheck_exit_full:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
   else comp_return ()) sp = ((),s1) /\
  fn_has_code sp s1 func /\
  t.vs_current_bb = sp.cs_current_bb /\
  t.vs_inst_idx = LENGTH sp.cs_current_insts /\ ~t.vs_halted /\
  stmt_state_rel H0 ctx func cenv cx ee t /\
  accounts_runtime_well_typed ee.accounts /\
  eval_operand addr_op t = SOME aw /\ w2w aw = target /\
  op_taint tn addr_op = {} /\ allocas_from lo t /\ ~ctx_has_dalloca ctx /\
  ~ext_call_precheck_ok skip ret_type target ee.accounts ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        value_opt' <- frame_call_value cx value_opt;
        returnData <- eval_ext_call_effects cx target calldata value_opt'
          gas accounts;
        k returnData od)
    (ee,t,G,tn) Q (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all extcall_precheck_exit_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] strip_assume_tac) >>
  irule gas_outcome_full_exit >> simp[] >>
  qexistsl_tac [`G'`,`ee`,`r`,
    `INR (Error (RuntimeError "ExtCall target has no code"))`,`tn'`] >>
  simp[get_accounts_def, bind_def, ignore_bind_def, return_def,
    check_def, assert_def, raise_def]
QED
