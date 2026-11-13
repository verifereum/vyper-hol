Theory tupleAssignImmutableDeployIntRestOwned
Ancestors
  tupleAssignImmutableDeployIntGasLift tupleAssignImmutableDeployIntMemoryOwned
  tupleAssignImmutableDeployIntRestore gasOutcome gasExemptCert gasSummary
  bodyIntCallSeams exprSimDefs loweringPosts vyperTyping vyperInterpreter
  intCallStep compileEnv loweringStateRelDefs
  vyperState venomExecSemantics venomState fragGasPath fragExec fragGasMode fragGasFocus

Theorem rest_replay[local]:
  intcall_callee_src cx name ss es = (res,ee) /\
  (!v. res = INL v ==> value_has_type rtv v) ==>
  intcall_rest cx name mut ss prev rtv es =
    ((case res of INL v => INL (Value v) | INR e => INR e),
     ee with scopes := prev)
Proof
  strip_tac >>
  Cases_on `res` >> gvs[] >>
  simp[intcall_rest_def, GSYM intcall_callee_src_def, finally_def,
       pop_function_def, unlock_if_nr_def, ignore_bind_def, bind_def,
       set_scopes_def, return_def, raise_def, lift_option_type_def,
       safe_cast_well_typed]
QED

Theorem tuple_immutable_intcall_memory_rest_owned:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_outcome F (cx_tops cx) (ctx,callee) (intcall_callee_src cx name ss)
    (es1,entered) (\res ee r. F)
    (intcall_callee_exit func ce cx rtv 0 (SOME w) n t) /\
  stmt_state_rel ctx func ce cx before t /\ before.scopes = prev /\
  evaluate_type (get_tenv cx) (TupleT stys) = SOME rtv /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  origin.cs_next_id <= aid /\ aid < final.cs_next_id /\
  type_memory_bytes ce (TupleT stys) <= sz /\
  eval_operand p.ptr_operand t = SOME w /\ p.ptr_location = LocMemory /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce sa /\
  (!lname lb lsz. local_region ce prev t lname lb lsz ==>
    w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
  (!lname b lsz id off asz.
    local_region ce prev t lname b lsz /\
    FLOOKUP t.vs_allocas id = SOME (off,asz) /\ n <= id ==>
    regions_disjoint b lsz off asz) /\
  (!bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst ==>
    EVERY (not_local_ptr ce prev) inst.inst_outputs /\
    (!x. MEM x inst.inst_outputs ==> ~not_fresh_at sa x)) /\
  (!v ee ir cs'.
    intcall_callee_exit func ce cx rtv 0 (SOME w) n t (INL v) ee (IntRet ir cs') ==>
    value_has_type rtv v /\
    immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
    (!bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst ==>
      LENGTH inst.inst_outputs = LENGTH ir.iret_values)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (intcall_rest cx name mut ss prev rtv) (es1,t)
    (\res ee u. ?v.
      res = INL (Value v) /\ stmt_state_rel ctx func ce cx ee u /\
      ee.scopes = prev /\
      vv_holds ce cx (TupleT stys) (Value v)
        (LocatedValue (TupleT stys) p) ee u /\
      eval_operand p.ptr_operand u = SOME w /\ p.ptr_location = LocMemory /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      origin.cs_next_id <= aid /\ aid < final.cs_next_id /\
      type_memory_bytes ce (TupleT stys) <= sz /\
      (!lname lb lsz. local_region ce prev u lname lb lsz ==>
        w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
      ~u.vs_halted /\ u.vs_current_bb = t.vs_current_bb /\
      u.vs_inst_idx = SUC t.vs_inst_idx)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- suspend "completed"
  >> suspend "exempt"
QED
Resume tuple_immutable_intcall_memory_rest_owned[completed]:
  gvs[exit_result_def] >>
  qpat_x_assum `intcall_callee_exit _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[intcall_callee_exit_def, expr_exit_def] >> strip_tac
  >- suspend "abort"
  >> suspend "success"
QED
Resume tuple_immutable_intcall_memory_rest_owned[exempt]:
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
  simp[Abbr `src`] >> irule (cj 19 gas_exempt_cert_rules) >>
  metis_tac[]
QED
Resume tuple_immutable_intcall_memory_rest_owned[abort]:
  Cases_on `r` >> gvs[expr_exit_def] >>
  rename1 `Abort a cs'` >>
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
    `es_end with scopes := before.scopes`, `Abort a cs'`] >>
  `!v. res <> INL v` by
    (Cases_on `res` >> gvs[expr_exit_def]) >>
  `expr_exit (case res of INL v => INL (Value v) | INR e => INR e) (Abort a cs')` by
    (Cases_on `res` >> gvs[expr_exit_def] >>
     Cases_on `y` >> gvs[expr_exit_def] >>
     rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  simp[exit_result_def, gas_marked_exec_def] >> gen_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[gas_invoke_entry_readings] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `tail` assume_tac) >>
  drule rest_replay >> simp[]
QED
Resume tuple_immutable_intcall_memory_rest_owned[success]:
  gvs[] >>
  `intcall_callee_exit func ce cx rtv 0 (SOME w) n t (INL v)
     (es_end with gas_obs := []) (IntRet ir s')` by
    (simp[intcall_callee_exit_def] >> metis_tac[]) >>
  first_assum (drule_then strip_assume_tac) >>
  drule_all tuple_immutable_callee_marked_invoke >> strip_tac >>
  `gas_marked_path F ctx callee entered (LENGTH marks) (IntRet ir s')` by
    gvs[gas_marked_exec_def] >>
  drule_all tuple_immutable_callee_counted_run >> strip_tac >>
  `stmt_state_rel ctx func ce cx
    (es_end with <|gas_obs := []; scopes := before.scopes|>)
    (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (drule tuple_immutable_intcall_return_restore_next >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> simp[] >>
     impl_tac >- metis_tac[] >> simp[]) >>
  `!x. MEM x inst.inst_outputs ==> ~not_fresh_at sa x` by metis_tac[] >>
  `EVERY (not_local_ptr ce before.scopes) inst.inst_outputs` by metis_tac[] >>
  drule tuple_immutable_memory_return_owned >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  simp[] >> disch_then (qspecl_then [`before.scopes`, `sa`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `~u.vs_halted /\ u.vs_current_bb = t.vs_current_bb` by
    (`inst' = inst` by metis_tac[optionTheory.SOME_11] >>
     `LENGTH inst'.inst_outputs = LENGTH ir.iret_values` by metis_tac[] >>
     drule_all step_inst_invoke_intret >> strip_tac >>
     `~t.vs_halted` by gvs[gas_invoke_entry_def] >>
     metis_tac[step_inst_invoke_OK_control, optionTheory.SOME_11]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL (Value v)`, `es_end with scopes := before.scopes`,
    `OK (u with vs_inst_idx := SUC t.vs_inst_idx)`] >>
  reverse conj_tac
  >- (simp[expr_exit_def, exit_result_def] >>
      simp[vv_holds_def, read_result_def, return_def, is_word_type_def,
           eval_operand_def, local_region_def, lookup_var_def] >>
      conj_tac
      >- (`(es_end with <|scopes := before.scopes; gas_obs := []|>) =
            (es_end with <|gas_obs := []; scopes := before.scopes|>)` by
            simp[evaluation_state_component_equality] >> metis_tac[]) >>
      gvs[local_region_def, lookup_var_def]) >>
  simp[gas_marked_exec_def] >>
  reverse conj_tac >- gvs[gas_marked_exec_def] >> gen_tac >>
  qpat_x_assum `gas_marked_exec _ (ctx,func) _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `tail` assume_tac) >>
  drule rest_replay >> simp[]
QED
Finalise tuple_immutable_intcall_memory_rest_owned
