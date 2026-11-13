Theory tupleAssignImmutableDeployIntRestTransport
Ancestors
  tupleAssignImmutableDeployIntGasLift gasOutcome gasExemptCert gasSummary
  bodyIntCallSeams exprSimDefs loweringPosts vyperTyping vyperInterpreter
  intCallStep compileEnv loweringStateRelDefs vyperState venomExecSemantics
  venomState fragGasPath fragExec fragGasMode fragGasFocus

Theorem rest_replay[local]:
  intcall_callee_src cx name ss es = (res,ee) /\
  (!v. res = INL v ==> value_has_type rtv v) ==>
  intcall_rest cx name mut ss prev rtv es =
    ((case res of INL v => INL (Value v) | INR e => INR e),
     ee with scopes := prev)
Proof
  strip_tac >> Cases_on `res` >> gvs[] >>
  simp[intcall_rest_def, GSYM intcall_callee_src_def, finally_def,
       pop_function_def, unlock_if_nr_def, ignore_bind_def, bind_def,
       set_scopes_def, return_def, raise_def, lift_option_type_def,
       safe_cast_well_typed]
QED

Theorem tuple_immutable_intcall_rest_transport:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_outcome F (cx_tops cx) (ctx,callee) (intcall_callee_src cx name ss)
    (es1,entered) (\res ee r. F)
    (intcall_callee_exit func ce cx rtv ret_count ret_word n t) /\
  (!v ee ir cs'.
    intcall_callee_exit func ce cx rtv ret_count ret_word n t (INL v)
      (ee with gas_obs := []) (IntRet ir cs') ==>
    value_has_type rtv v /\
    (!bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst ==>
      LENGTH inst.inst_outputs = LENGTH ir.iret_values) /\
    (!bb inst returned argv setup fuel.
      lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\
      bind_outputs inst.inst_outputs ir.iret_values
        (adopt_return_fmp ir (merge_callee_state t cs')) = SOME returned /\
      ~returned.vs_halted /\ returned.vs_current_bb = t.vs_current_bb /\
      setup_callee callee argv t = SOME setup /\
      run_blocks fuel ctx callee setup = IntRet ir cs' ==>
      ?u. gas_marked_path F ctx func
          (returned with vs_inst_idx := SUC t.vs_inst_idx) 0 (OK u) /\
        Q (INL (Value v)) (ee with <|scopes := prev; gas_obs := []|>) u)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (intcall_rest cx name mut ss prev rtv) (es1,t) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "completed"
  >> suspend "exempt"
QED
Resume tuple_immutable_intcall_rest_transport[completed]:
  gvs[exit_result_def] >>
  qpat_x_assum `intcall_callee_exit _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[intcall_callee_exit_def, expr_exit_def] >> strip_tac
  >- suspend "abort"
  >> suspend "success"
QED
Resume tuple_immutable_intcall_rest_transport[exempt]:
  rename1 `gas_exempt_cert _ _ _ _ _ _ (_,ee) (leaf,endpoint)` >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee with scopes := prev`, `leaf`, `endpoint`] >>
  simp[intcall_rest_def, GSYM intcall_callee_src_def,
       ignore_bind_def, bind_assoc] >>
  irule (cj 9 gas_exempt_cert_rules) >>
  qmatch_goalsub_abbrev_tac `finally src cleanup` >>
  `ignore_bind (finally src cleanup) (return ()) =
    finally (ignore_bind src (return ())) cleanup` by
    (rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `st` >>
     Cases_on `src st` >> Cases_on `q` >>
     simp[finally_def, ignore_bind_def, bind_def, return_def, raise_def] >>
     Cases_on `cleanup r` >> Cases_on `q` >>
     simp[bind_def, return_def, raise_def]) >>
  asm_rewrite_tac[] >>
  irule (cj 16 gas_exempt_cert_rules) >>
  qexists_tac `ee` >> conj_tac
  >- simp[Abbr `cleanup`, pop_function_def, ignore_bind_def, bind_def,
          set_scopes_def, return_def, evaluation_state_component_equality] >>
  simp[Abbr `src`] >> irule (cj 19 gas_exempt_cert_rules) >> metis_tac[]
QED
Resume tuple_immutable_intcall_rest_transport[abort]:
  Cases_on `r` >> gvs[expr_exit_def] >> rename1 `Abort a cs'` >>
  `gas_marked_path F ctx callee entered (LENGTH marks) (Abort a cs')` by
    gvs[gas_marked_exec_def] >>
  drule_all tuple_immutable_callee_counted_abort >> strip_tac >>
  `step_inst fuel ctx inst t = Abort a cs'` by
    metis_tac[step_inst_invoke_abort] >>
  `gas_marked_path F ctx func t (LENGTH marks) (Abort a cs')` by
    (simp[gas_marked_path_def] >> irule (cj 3 gas_path_rules) >>
     simp[exit_result_def, gas_path_edge_def] >>
     `~t.vs_halted` by gvs[gas_invoke_entry_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`case res of INL v => INL (Value v) | INR e => INR e`,
    `es_end with scopes := prev`, `Abort a cs'`] >>
  `!v. res <> INL v` by (Cases_on `res` >> gvs[expr_exit_def]) >>
  `expr_exit (case res of INL v => INL (Value v) | INR e => INR e) (Abort a cs')` by
    (Cases_on `res` >> gvs[expr_exit_def] >>
     Cases_on `y` >> gvs[expr_exit_def] >>
     rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  simp[exit_result_def, gas_marked_exec_def] >> gen_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[gas_invoke_entry_readings] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `tail` assume_tac) >> drule rest_replay >> simp[]
QED
Resume tuple_immutable_intcall_rest_transport[success]:
  gvs[] >>
  `intcall_callee_exit func ce cx rtv (LENGTH ir.iret_values) ret_word n t (INL v)
     (es_end with gas_obs := []) (IntRet ir s')` by
    (simp[intcall_callee_exit_def] >> metis_tac[]) >>
  first_assum (drule_then strip_assume_tac) >>
  drule_all tuple_immutable_callee_marked_invoke >> strip_tac >>
  `gas_marked_path F ctx callee entered (LENGTH marks) (IntRet ir s')` by
    gvs[gas_marked_exec_def] >>
  drule_all tuple_immutable_callee_counted_run >> strip_tac >>
  `~u.vs_halted /\ u.vs_current_bb = t.vs_current_bb` by
    (`inst' = inst` by metis_tac[optionTheory.SOME_11] >>
     `LENGTH inst'.inst_outputs = LENGTH ir.iret_values` by metis_tac[] >>
     drule_all step_inst_invoke_intret >> strip_tac >>
     `~t.vs_halted` by gvs[gas_invoke_entry_def] >>
     metis_tac[step_inst_invoke_OK_control, optionTheory.SOME_11]) >>
  `bb' = bb /\ inst' = inst` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  first_x_assum drule >> simp[] >> disch_then (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `Q _ _ final` >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL (Value v)`, `es_end with scopes := prev`, `OK final`] >>
  simp[exit_result_def] >>
  simp[gas_marked_exec_def] >> reverse conj_tac
    >- (`gas_marked_path F ctx func t (LENGTH marks + 0) (OK final)`
          suffices_by simp[] >>
        irule gas_marked_path_then >>
        qexists `u with vs_inst_idx := SUC t.vs_inst_idx` >>
        gvs[gas_marked_exec_def]) >>
    gen_tac >>
    qpat_x_assum `gas_marked_exec _ (ctx,func) _ _ _ _ _ _` mp_tac >>
    simp[gas_marked_exec_def] >> strip_tac >>
    first_x_assum (qspec_then `tail` assume_tac) >> drule rest_replay >> simp[]
QED
Finalise tuple_immutable_intcall_rest_transport
