(* Exceptional external-call branches on the joint judgment. *)
Theory bodyFullExtCallExit
Ancestors
  bodyFullExtCallPrecheckExit bodyFullExtCallFailurePath gasOutcomeFullCompose
  exprSimExtCallCase vyperInterpreter vyperState vyperCallOutcome vyperCallOutcomeProps
  fragGasOriginPtr fragExec exprSimDefs

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

Theorem extcall_failed_call_source_oracle:
  ext_call_precheck_ok skip ret_type target ee.accounts /\
  (~cx.txn.is_static \/ value_opt = NONE \/ value_opt = SOME 0) /\
  vopt = (if cx.txn.is_static then NONE else value_opt) /\
  take_call_outcome target calldata vopt ee = (INL (rq,outcome),ef) /\
  ~call_outcome_success outcome ==>
  !tail.
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        value_opt' <- frame_call_value cx value_opt;
        returnData <- eval_ext_call_effects cx target calldata value_opt'
          gas accounts;
        k returnData od) (ee with gas_obs := tail) =
      (INR (Error (RevertData (call_outcome_return_data outcome))),
       ef with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  `?os. ee.outcomes = SOME os` by
    metis_tac[vyperCallOutcomePropsTheory.take_call_outcome_success] >>
  `take_call_outcome target calldata vopt (ee with gas_obs := tail) =
     (INL (rq,outcome),ef with gas_obs := tail)` by
    (qpat_x_assum `take_call_outcome _ _ _ ee = _` mp_tac >>
     simp[take_call_outcome_def, take_request_outcome_def,
          call_outcome_request_def] >>
     pairarg_tac >> rw[] >> gvs[]) >>
  simp[get_accounts_def, bind_def, ignore_bind_def, return_def,
       check_def, assert_def, raise_def, frame_call_value_def,
       eval_ext_call_effects_def] >>
  Cases_on `cx.txn.is_static` >>
  gvs[bind_def, ignore_bind_def, return_def, check_def, assert_def, raise_def]
QED

Theorem extcall_failed_call_source_concrete:
  ext_call_precheck_ok skip ret_type target ee.accounts /\
  (~cx.txn.is_static \/ value_opt = NONE \/ value_opt = SOME 0) /\
  vopt = (if cx.txn.is_static then NONE else value_opt) /\
  ee.outcomes = NONE /\
  run_ext_call cx.txn.target target calldata vopt gas ee.accounts ee.tStorage
    (vyper_to_tx_params cx.txn) =
      SOME (F,rd,accounts',transient',logs',deletions) ==>
  !tail.
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        value_opt' <- frame_call_value cx value_opt;
        returnData <- eval_ext_call_effects cx target calldata value_opt'
          gas accounts;
        k returnData od) (ee with gas_obs := tail) =
      (INR (Error (RevertData rd)),ee with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  simp[get_accounts_def, bind_def, ignore_bind_def, return_def,
       check_def, assert_def, raise_def, frame_call_value_def,
       eval_ext_call_effects_def, get_transient_storage_def, lift_option_def] >>
  Cases_on `cx.txn.is_static` >>
  gvs[bind_def, ignore_bind_def, return_def, check_def, assert_def, raise_def,
      get_transient_storage_def]
QED

Theorem extcall_failed_call_exit_full:
  ext_call_precheck_ok skip ret_type target ee.accounts /\
  (~cx.txn.is_static \/ value_opt = NONE \/ value_opt = SOME 0) /\
  vopt = (if cx.txn.is_static then NONE else value_opt) /\
  take_call_outcome target calldata vopt ee = (INL (rq,outcome),ef) /\
  ~call_outcome_success outcome /\
  emit_inst JNZ [cond;Label ok;Label fl] [] sa = ((),sx) /\
  new_block fl sx = (x,sf) /\
  emit_op RETURNDATASIZE [] sf = (z,sz) /\
  compile_alloc_buffer 0 sz = (rb,sp) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] sp = (b,sc) /\
  emit_inst REVERT [rb.buf_operand;z] [] sc = (c,se) /\
  new_block ok se = (y,sk) /\ fn_has_code sa sk func /\
  ~t.vs_halted /\ ~tc.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo tc /\ lo <= tc.vs_alloca_next /\
  tc.vs_current_bb = sa.cs_current_bb /\
  tc.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand cond tc = SOME 0w /\ op_taint tnc cond = {} /\
  tc.vs_returndata = call_outcome_return_data outcome /\
  LENGTH tc.vs_returndata < dimword (:256) /\
  gas_explicit marks t.vs_gas_readings = [] /\
  (!H. valid_horizon cx st0 H ef.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (t,G,tn) marks (OK tc,Gc,tnc)) ==>
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ source` >>
  `!tail. source (ee with gas_obs := tail) =
    (INR (Error (RevertData (call_outcome_return_data outcome))),
     ef with gas_obs := tail)` by
    (unabbrev_all_tac >> metis_tac[extcall_failed_call_source_oracle]) >>
  drule_all extcall_failure_suffix_path >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gc`] strip_assume_tac) >>
  Cases_on `storage_trace_domain cx st0 ef.storage_trace`
  >- (irule gas_outcome_full_intro >>
      qexistsl_tac [`G'`,`ef`,`marks`,`Abort Revert_abort u`,
        `INR (Error (RevertData (call_outcome_return_data outcome)))`,`tn'`] >>
      simp[exit_result_def, expr_exit_def] >> rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` drule >>
      disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >>
      simp[] >> disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> disch_then irule >> simp[]) >>
  irule gas_outcome_full_bad_nil >> simp[]
QED
