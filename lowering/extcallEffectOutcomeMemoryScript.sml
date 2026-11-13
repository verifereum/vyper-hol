(* The source oracle action and its same-path memory-counted outcome. *)
Theory extcallEffectOutcomeMemory
Ancestors
  extcallEffectMemory extcallFinishMemory exprSimExtCallCase exprSimDefs
  exprLoweringProps loweringStateRelDefs gasSummary fragGasMode
  vyperInterpreter vyperState vyperCallOutcome venomState fragExec
Libs monadsyntax

val extcall_oracle_branch_pre =
  fst (dest_imp (concl (SPEC_ALL extcall_oracle_branch_mem)));

Theorem extcall_oracle_effect_summary_mem:
  ^extcall_oracle_branch_pre /\
  ext_call_precheck_ok skip rt target ee.accounts ==>
  gas_summary_at T (ctx,func) []
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip rt target accounts)
          "ExtCall target has no code";
        value <- frame_call_value cx vo;
        eval_ext_call_effects cx target data value gas_budget accounts
     od) (ee,s)
    (\res ee' t. ?bs. res = INL bs /\ alloca_history func t /\
      extcall_returned ctx func ce cx rt es sa s0 sr addr buf cap target
        has def dt opt bs ee' t)
    (\res ee' r. expr_exit res r)
Proof
  strip_tac >>
  `~cx.txn.is_static /\ IS_SOME ee.outcomes` by
    fs[extcall_request_ready_def, stmt_state_rel_def, state_rel_def] >>
  mp_tac (Q.INST [`es` |-> `ee`,`es1` |-> `ee1`,`gas` |-> `gas_budget`]
    (SPEC_ALL extcall_effect_source_run)) >>
  impl_tac >- simp[] >> disch_tac >>
  drule_all extcall_oracle_branch_mem >>
  disch_then (qx_choose_then `r` assume_tac) >>
  Cases_on `oc.co_success`
  >- suspend "success" >> suspend "revert"
QED

Resume extcall_oracle_effect_summary_mem[success]:
  gvs[] >>
  `(SND (adopt_call_outcome rq oc ee1)) with gas_obs := [] =
    SND (adopt_call_outcome rq oc ee1)` by
    (fs[extcall_returned_def] >>
     simp[evaluation_state_component_equality]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL oc.co_returnData`,`SND (adopt_call_outcome rq oc ee1)`,`OK t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def]
QED

Resume extcall_oracle_effect_summary_mem[revert]:
  gvs[] >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RevertData oc.co_returnData))`,`ee1`,
    `Abort Revert_abort t`] >>
  simp[gas_marked_exec_def, gas_marked_path_def, expr_exit_def, exit_result_def]
QED

Finalise extcall_oracle_effect_summary_mem
