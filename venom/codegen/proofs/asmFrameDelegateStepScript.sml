(* Delegate calls use the frame's observed message-call outcomes. *)
Theory asmFrameDelegateStep
Ancestors
  asmFrameRel asmFrameCallStep frameObsStep asmCallOracleProps asmDataSuffixProps
  codegenRel asmSem asmWf symbolResolve extCallOracle callTrace frameOutcome
  evmCreationGuard frameCreationGuard vfmExecution vfmExecutionProp vfmRunCall vfmDomainCollection asmEncodeParse vfmOperation rich_list list regularMemorySim

(* Check the delegated request boundary without equating its zero value
   with the inherited EVM message value. *)
Theorem asm_delegate_request_fields[local]:
  s.contexts = (c,rb)::rest /\ next_opcode c = SOME DelegateCall ==>
  (request_of s).cr_kind = DelegateMessageCall /\
  (request_of s).cr_value = 0 /\
  (request_of s).cr_static = c.msgParams.static /\
  ~computed_precompile (request_of s)
Proof
  simp[request_of_def, computed_precompile_def]
QED

Theorem asm_delegate_outcome_view[local]:
  outcome_of DelegateMessageCall s n m = outcome_of MessageCall s n m
Proof
  simp[outcome_of_def]
QED

(* A delegated child runs the parent's identities and value, not the
   request's target/value pair.  This is an entry-interface diagnostic. *)
Theorem asm_delegate_enter_view[local]:
  s.contexts = (parent,prb)::rest /\
  ~fIN address precompile_addresses /\
  proceed_call DelegateCall sender address 0 ao az code stipend (Memory mr) s =
    (INL (),t) ==>
  ?child. t.contexts = (child,s.rollback)::(parent,prb)::rest /\
    child.msgParams.callee = sender /\
    child.msgParams.caller = parent.msgParams.caller /\
    child.msgParams.value = parent.msgParams.value /\
    child.msgParams.static = parent.msgParams.static /\
    child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
    t.rollback = s.rollback
Proof
  strip_tac >>
  qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, push_context_def,
       get_current_context_def, return_def] >>
  strip_tac >>
  gvs[vfmContextTheory.initial_context_def,
      vfmContextTheory.initial_msg_params_def]
QED

Theorem asm_frame_delegate_decode[local]:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" ==>
  next_opcode (FST (HD es.contexts)) = SOME DelegateCall
Proof
  strip_tac >> irule asm_frame_opcode_decode >>
  simp[wf_opname_def] >> qexistsl_tac [`a`, `data`, `prog`] >>
  gvs[is_data_inst_def, encode_inst_def, evm_opcode_byte_def,
      evm_opcode_table_def, wf_opname_def, opcode_def]
QED

Theorem asm_frame_delegate_pc_increment[local]:
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" ==>
  asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
    asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1
Proof
  strip_tac >>
  `a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  drule asm_pc_to_offset_suc >>
  simp[arithmeticTheory.ADD1, EL_APPEND1, asm_inst_size_def]
QED

Theorem asm_step_delegate[local]:
  asm_step lo otp (AsmOp "DELEGATECALL") a = asm_exec_delegatecall a
Proof
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def]
QED

Theorem asm_delegate_underflow[local]:
  LENGTH a.as_stack < 6 ==>
  asm_step lo otp (AsmOp "DELEGATECALL") a = AsmError "delegatecall: stack underflow"
Proof
  simp[asm_step_delegate] >>
  Cases_on `a.as_stack` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t'` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t'` >> simp[asm_exec_delegatecall_def] >>
  Cases_on `t` >> simp[asm_exec_delegatecall_def]
QED

Theorem asm_frame_delegate_request[local]:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  a.as_stack = gas :: addr :: ao :: sz :: ro :: rs :: stk ==>
  (asm_call_request a addr 0w (w2n ao) (w2n sz) F with
     cr_kind := DelegateMessageCall) = request_of es
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) = SOME DelegateCall` by
    (drule_all asm_frame_delegate_decode >> simp[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def] >>
  simp[request_of_def, asm_call_request_def, GSYM asm_call_input_buffer,
       expanded_slice_padded_range]
QED

Theorem asm_frame_delegate_consume[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  s.contexts = (c,rb)::rest /\
  asm_call_prepare DelegateCall s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL a.as_pc prog) a =
  asm_consume_call_outcome (request_of s) ro rs (DROP 6 a.as_stack)
    (a with as_memory := asm_call_memory ao az ro rs a.as_memory)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  drule_at (Pat `asm_call_prepare _ _ = _`) asm_message_prepare_success_view >>
  disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac (srw_ss()) [LET_THM, call_has_value_def] >> strip_tac >>
  qpat_x_assum `u = _` kall_tac >>
  `c.stack = a.as_stack` by gvs[asm_evm_rel_def] >>
  `?gas addr x y z w stk. a.as_stack = gas::addr::x::y::z::w::stk` by
    (qpat_x_assum `6 <= LENGTH _` mp_tac >>
     namedCases_on `a.as_stack` ["", "gas t1"] >> simp[] >>
     namedCases_on `t1` ["", "addr t2"] >> simp[] >>
     namedCases_on `t2` ["", "x t3"] >> simp[] >>
     namedCases_on `t3` ["", "y t4"] >> simp[] >>
     namedCases_on `t4` ["", "z t5"] >> simp[] >>
     namedCases_on `t5` ["", "w stk"] >> simp[]) >>
  drule_all asm_frame_delegate_request >> disch_tac >>
  gvs[] >> simp[asm_step_delegate, asm_exec_delegatecall_def]
QED

Theorem asm_frame_delegate_prepare_exit[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  s.contexts = (c,rb)::rest /\
  asm_call_prepare DelegateCall s = (INR e,t) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\ wf_state s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  `c.stack = a.as_stack` by gvs[asm_evm_rel_def] >>
  Cases_on `6 <= LENGTH c.stack`
  >- (`next_opcode c = SOME DelegateCall` by
        (drule_all asm_frame_delegate_decode >> simp[]) >>
      `asm_call_prepare StaticCall s = (INR e,t)` by
        fs[asm_call_prepare_delegate] >>
      `e = SOME OutOfGas` by
        (qpat_x_assum `asm_call_prepare DelegateCall _ = _` kall_tac >>
         drule_at (Pat `asm_call_prepare _ _ = _`)
           asm_call_prepare_failure_kind >>
         disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
         simp[call_has_value_def] >> metis_tac[]) >>
      `t.contexts = (c with stack := DROP 6 c.stack,rb)::rest /\
       t.txParams = s.txParams` by
        (qpat_x_assum `asm_call_prepare DelegateCall _ = _` kall_tac >>
         drule_at (Pat `asm_call_prepare _ _ = _`)
           asm_call_prepare_failure_view >>
         disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
         simp[call_has_value_def] >> metis_tac[]) >>
      `step_call DelegateCall s = (INR (SOME OutOfGas),t)` by
        simp[asm_step_call_factor, bind_def] >>
      `step s = handle_step (SOME OutOfGas) t` by
        (irule asm_message_step_terminal >> simp[] >> metis_tac[]) >>
      `rest = [] \/ (?mr. c.msgParams.outputTo = Memory mr)` by
        (fs[asm_frame_rel_def, asm_evm_rel_def] >>
         Cases_on `c.msgParams.outputTo` >> gvs[]) >>
      drule_at (Pat `step _ = _`) asm_step_oog_starved >>
      disch_then (qspecl_then [`rest`,`rb`,`6`,`c`] mp_tac) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
      `frame_resource_starved es0 r s'` by
        (fs[asm_frame_rel_def] >> drule_all frame_resource_starved_mid >> simp[]) >>
      simp[asm_frame_step_ok_def] >> metis_tac[]) >>
  `LENGTH a.as_stack < 6` by metis_tac[arithmeticTheory.NOT_LESS_EQUAL] >>
  drule asm_delegate_underflow >>
  disch_then (qspecl_then [`build_offset_to_pc prog`,
    `SND (compute_label_offsets prog)`] assume_tac) >>
  simp[asm_frame_step_ok_def]
QED

Theorem asm_frame_delegate_abort[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  s.contexts = (c,rb)::rest /\
  asm_call_prepare DelegateCall s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  ((lookup_account sender accounts).balance < value \/ 1024 < LENGTH s.contexts) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\ wf_state s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  `LENGTH c.stack <= stack_limit` by gvs[wf_state_def, wf_context_def] >>
  `next_opcode c = SOME DelegateCall` by
    (drule_all asm_frame_delegate_decode >> simp[]) >>
  drule_at (Pat `asm_call_prepare _ _ = _`) asm_message_prepare_abort_state >>
  disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac (srw_ss()) [LET_THM, call_has_value_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_call DelegateCall s = (INL (),t)` >>
  `step s = (INL (),t)` by
    (irule asm_message_step_success >> simp[] >> metis_tac[]) >>
  `LENGTH t.contexts = LENGTH s.contexts` by simp[Abbr `t`] >>
  `run_call t = run_call s` by metis_tac[run_call_same_depth_step] >>
  `wf_state t` by (drule step_preserves_wf_state >> simp[]) >>
  `6 <= LENGTH c.stack` by
    (drule_at (Pat `asm_call_prepare _ _ = _`) asm_message_prepare_success_view >>
     disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
     simp[call_has_value_def] >> metis_tac[]) >>
  `observable_call c` by simp[observable_call_def] >>
  drule frame_obs_call_same_depth >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `outcome_of (request_of s).cr_kind t (LENGTH c.logs)
     (LENGTH s.rollback.toDelete) = failed_outcome (request_of s)` by
    simp[outcome_of_def, request_of_def, failed_outcome_def, Abbr `t`] >>
  suspend "effects"
QED

Resume asm_frame_delegate_abort[effects]:
  `a.as_outcomes = failed_outcome (request_of s) :: MAP SND (call_trace t)` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `take_outcome (request_of s) a.as_outcomes =
    (failed_outcome (request_of s),MAP SND (call_trace t))` by
    simp[asm_take_outcome_failed_head] >>
  `record_request (request_of s) a.as_requests ++ call_requests t =
    call_requests es0` by
    (fs[asm_frame_rel_def, call_requests_def, record_request_def] >>
     gvs[] >> IF_CASES_TAC >> gvs[]) >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
    asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1` by
    (irule asm_frame_delegate_pc_increment >> simp[]) >>
  drule_all asm_frame_delegate_consume >> disch_tac >>
  `buffer_to_list c.memory = a.as_memory` by gvs[asm_evm_rel_def] >>
  `buffer_to_list (FST (HD t.contexts)).memory =
    asm_call_memory ao az ro rs a.as_memory` by
    (simp[Abbr `t`] >>
     qpat_x_assum `buffer_to_list c.memory = _` (fn th => rewrite_tac[GSYM th]) >>
     Cases_on `max_expansion_range (ao,az) (ro,rs)` >>
     irule asm_call_memory_buffer_extend >> simp[] >> metis_tac[]) >>
  qpat_x_assum `Abbrev (t = _)` mp_tac >>
  qmatch_goalsub_abbrev_tac `(ct,rb)::rest` >> disch_tac >>
  `t.contexts = (ct,rb)::rest /\ t.txParams = s.txParams /\
   (?d. t.msdomain = Collect d) /\
   t.rollback.accounts = s.rollback.accounts /\
   t.rollback.tStorage = s.rollback.tStorage /\
   t.rollback.toDelete = s.rollback.toDelete` by simp[Abbr `t`] >>
  `ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\
   ct.pc = SUC c.pc /\ ct.logs = c.logs /\ ct.returnData = [] /\
   ct.stack = 0w::DROP 6 c.stack` by simp[Abbr `ct`] >>
  qpat_x_assum `Abbrev (ct = _)` kall_tac >>
  qpat_x_assum `Abbrev (t = _)` kall_tac >>
  suspend "package"
QED

Resume asm_frame_delegate_abort[package]:
  `(a.as_call_ctx.cc_created_in_tx =
      account_empty (lookup_account c.msgParams.callee t.originalAccounts)) /\
    (~a.as_call_ctx.cc_created_in_tx ==> account_already_created
      (lookup_account c.msgParams.callee t.rollback.accounts))` by
    (mp_tac (Q.INST [`s` |-> `s`, `t` |-> `t`,
       `self` |-> `c.msgParams.callee`, `created` |-> `a.as_call_ctx.cc_created_in_tx`]
       step_continuing_creation_guard) >> gvs[asm_frame_rel_def] >> metis_tac[]) >>
  `(request_of s).cr_kind = DelegateMessageCall` by simp[request_of_def] >>
  `adopt_outcome (request_of s) (failed_outcome (request_of s))
      (a.as_accounts,a.as_transient,a.as_logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
   adopt_outcome_deletions (request_of s) (failed_outcome (request_of s))
      a.as_pending_deletions = t.rollback.toDelete` by
    (simp[failed_outcome_def, adopt_outcome_def, adopt_outcome_deletions_def] >>
     gvs[asm_evm_rel_def]) >>
  `buffer_to_list ct.memory =
    TAKE ro (asm_call_memory ao az ro rs a.as_memory) ++
    TAKE rs (failed_outcome (request_of s)).co_returnData ++
    DROP (ro + LENGTH (TAKE rs (failed_outcome (request_of s)).co_returnData))
      (asm_call_memory ao az ro rs a.as_memory)` by
    (gvs[failed_outcome_def, TAKE_DROP]) >>
  `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a =
   asm_consume_call_outcome (request_of s) ro rs
     (DROP (6 + (if call_has_value DelegateCall then 1 else 0)) a.as_stack)
     (a with as_memory := asm_call_memory ao az ro rs a.as_memory)` by
    simp[call_has_value_def] >>
  drule_at (Pat `asm_step _ _ _ _ = _`) asm_frame_outcome_effects_step_ok >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (drule_at (Pat `asm_frame_rel _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `s.contexts = _`)) >>
  disch_then (qspecl_then [`failed_outcome (request_of s)`,`c`,`az`,`ao`] mp_tac) >>
  simp[call_has_value_def, failed_outcome_def] >> metis_tac[]
QED
Finalise asm_frame_delegate_abort

Theorem asm_frame_delegate_terminal_exception[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  s.contexts = (c,rb)::rest /\
  asm_call_prepare DelegateCall s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish DelegateCall (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR (SOME exc),v) /\ exc <> Reverted /\ ~vfm_abort (SOME exc) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\ wf_state s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  `next_opcode c = SOME DelegateCall` by
    (drule_all asm_frame_delegate_decode >> simp[]) >>
  drule_at (Pat `asm_call_finish _ _ _ = _`)
    asm_message_prepared_terminal_exception_view >>
  disch_then (qspecl_then [`s`,`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[call_has_value_def] >> strip_tac >>
  `6 <= LENGTH c.stack` by
    (drule_at (Pat `asm_call_prepare _ _ = _`) asm_message_prepare_success_view >>
     disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
     simp[call_has_value_def] >> metis_tac[]) >>
  `LENGTH t.contexts = LENGTH s.contexts` by
    (qpat_assum `s.contexts = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `run_call t = run_call s` by metis_tac[run_call_same_depth_step] >>
  `wf_state t` by (drule step_preserves_wf_state >> simp[]) >>
  `observable_call c` by simp[observable_call_def] >>
  drule frame_obs_call_same_depth >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `outcome_of (request_of s).cr_kind t (LENGTH c.logs)
     (LENGTH s.rollback.toDelete) = failed_outcome (request_of s)` by
    simp[outcome_of_def, request_of_def, failed_outcome_def] >>
  `a.as_outcomes = failed_outcome (request_of s)::MAP SND (call_trace t)` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `record_request (request_of s) a.as_requests ++ call_requests t =
     call_requests es0` by
    (fs[asm_frame_rel_def, call_requests_def, record_request_def] >>
     gvs[] >> IF_CASES_TAC >> gvs[]) >>
  `take_outcome (request_of s) a.as_outcomes =
     (failed_outcome (request_of s),MAP SND (call_trace t))` by
    simp[asm_take_outcome_failed_head] >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
    asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1` by
    (irule asm_frame_delegate_pc_increment >> simp[]) >>
  drule_all asm_frame_delegate_consume >> disch_tac >>
  suspend "package"
QED

Resume asm_frame_delegate_terminal_exception[package]:
  `(a.as_call_ctx.cc_created_in_tx =
      account_empty (lookup_account c.msgParams.callee t.originalAccounts)) /\
    (~a.as_call_ctx.cc_created_in_tx ==> account_already_created
      (lookup_account c.msgParams.callee t.rollback.accounts))` by
    (mp_tac (Q.INST [`s` |-> `s`, `t` |-> `t`,
       `self` |-> `c.msgParams.callee`, `created` |-> `a.as_call_ctx.cc_created_in_tx`]
       step_continuing_creation_guard) >> gvs[asm_frame_rel_def] >> metis_tac[]) >>
  `(request_of s).cr_kind = DelegateMessageCall` by simp[request_of_def] >>
  `adopt_outcome (request_of s) (failed_outcome (request_of s))
      (a.as_accounts,a.as_transient,a.as_logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
   adopt_outcome_deletions (request_of s) (failed_outcome (request_of s))
      a.as_pending_deletions = t.rollback.toDelete` by
    (simp[failed_outcome_def, adopt_outcome_def, adopt_outcome_deletions_def] >>
     gvs[asm_evm_rel_def]) >>
  `buffer_to_list c.memory = a.as_memory` by gvs[asm_evm_rel_def] >>
  `buffer_to_list ct.memory =
    TAKE ro (asm_call_memory ao az ro rs a.as_memory) ++
    TAKE rs (failed_outcome (request_of s)).co_returnData ++
    DROP (ro + LENGTH (TAKE rs (failed_outcome (request_of s)).co_returnData))
      (asm_call_memory ao az ro rs a.as_memory)` by
    (gvs[failed_outcome_def, TAKE_DROP]) >>
  `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a =
   asm_consume_call_outcome (request_of s) ro rs
     (DROP (6 + (if call_has_value DelegateCall then 1 else 0)) a.as_stack)
     (a with as_memory := asm_call_memory ao az ro rs a.as_memory)` by
    simp[call_has_value_def] >>
  drule_at (Pat `asm_step _ _ _ _ = _`) asm_frame_outcome_effects_step_ok >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (drule_at (Pat `asm_frame_rel _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `s.contexts = _`)) >>
  disch_then (qspecl_then [`failed_outcome (request_of s)`,`c`,`az`,`ao`] mp_tac) >>
  simp[call_has_value_def, failed_outcome_def] >> metis_tac[]
QED
Finalise asm_frame_delegate_terminal_exception

Theorem asm_frame_delegate_terminal_none[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  s.contexts = (c,rb)::rest /\
  asm_call_prepare DelegateCall s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish DelegateCall (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR NONE,v) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\ wf_state s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  `next_opcode c = SOME DelegateCall` by
    (drule_all asm_frame_delegate_decode >> simp[]) >>
  drule_at (Pat `asm_call_finish _ _ _ = _`)
    asm_message_prepared_terminal_success_view >>
  disch_then (qspecl_then [`s`,`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[call_has_value_def] >> strip_tac >>
  `6 <= LENGTH c.stack` by
    (drule_at (Pat `asm_call_prepare _ _ = _`) asm_message_prepare_success_view >>
     disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
     simp[call_has_value_def] >> metis_tac[]) >>
  `LENGTH t.contexts = LENGTH s.contexts` by
    (qpat_assum `s.contexts = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `run_call t = run_call s` by metis_tac[run_call_same_depth_step] >>
  `wf_state t` by (drule step_preserves_wf_state >> simp[]) >>
  `observable_call c` by simp[observable_call_def] >>
  drule frame_obs_call_same_depth >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  qabbrev_tac `out = outcome_of (request_of s).cr_kind t (LENGTH c.logs)
    (LENGTH s.rollback.toDelete)` >>
  `a.as_outcomes = out::MAP SND (call_trace t)` by
    (fs[asm_frame_rel_def] >> gvs[Abbr `out`]) >>
  `record_request (request_of s) a.as_requests ++ call_requests t =
     call_requests es0` by
    (fs[asm_frame_rel_def, call_requests_def, record_request_def] >>
     gvs[] >> IF_CASES_TAC >> gvs[]) >>
  `take_outcome (request_of s) a.as_outcomes = (out,MAP SND (call_trace t))` by
    simp[take_outcome_def, computed_precompile_def, request_of_def] >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
    asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1` by
    (irule asm_frame_delegate_pc_increment >> simp[]) >>
  drule_all asm_frame_delegate_consume >> disch_tac >>
  suspend "package"
QED

Resume asm_frame_delegate_terminal_none[package]:
  `(a.as_call_ctx.cc_created_in_tx =
      account_empty (lookup_account c.msgParams.callee t.originalAccounts)) /\
    (~a.as_call_ctx.cc_created_in_tx ==> account_already_created
      (lookup_account c.msgParams.callee t.rollback.accounts))` by
    (mp_tac (Q.INST [`s` |-> `s`, `t` |-> `t`,
       `self` |-> `c.msgParams.callee`, `created` |-> `a.as_call_ctx.cc_created_in_tx`]
       step_continuing_creation_guard) >> gvs[asm_frame_rel_def] >> metis_tac[]) >>
  `out.co_success /\ out.co_returnData = ct.returnData /\
   adopt_outcome (request_of s) out (a.as_accounts,a.as_transient,a.as_logs) =
     (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
   adopt_outcome_deletions (request_of s) out a.as_pending_deletions =
     t.rollback.toDelete` by
    (simp[Abbr `out`, outcome_of_def, request_of_def,
          adopt_outcome_def, adopt_outcome_deletions_def] >>
     gvs[asm_evm_rel_def]) >>
  `buffer_to_list c.memory = a.as_memory` by gvs[asm_evm_rel_def] >>
  `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a =
   asm_consume_call_outcome (request_of s) ro rs
     (DROP (6 + (if call_has_value DelegateCall then 1 else 0)) a.as_stack)
     (a with as_memory := asm_call_memory ao az ro rs a.as_memory)` by
    simp[call_has_value_def] >>
  drule_at (Pat `asm_step _ _ _ _ = _`) asm_frame_outcome_effects_step_ok >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (drule_at (Pat `asm_frame_rel _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `s.contexts = _`)) >>
  disch_then (qspecl_then [`out`,`c`,`az`,`ao`] mp_tac) >>
  simp[call_has_value_def] >> metis_tac[]
QED
Finalise asm_frame_delegate_terminal_none

Theorem asm_frame_delegate_terminal[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  s.contexts = (c,rb)::rest /\
  asm_call_prepare DelegateCall s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish DelegateCall (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR result,v) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  Cases_on `result`
  >- (drule_all asm_frame_delegate_terminal_none >> simp[]) >>
  `~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  drule_at (Pat `asm_call_finish _ _ _ = _`) asm_message_prepared_terminal_kind >>
  disch_then (qspecl_then [`s`,`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `x <> Reverted` by gvs[] >>
  drule_all asm_frame_delegate_terminal_exception >> simp[]
QED

Theorem asm_frame_delegate_enter_step_ok[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "DELEGATECALL" /\
  s.contexts = (c,rb)::rest /\
  asm_call_prepare DelegateCall s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish DelegateCall (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (),v) /\ step s = (INL (),v) /\ observable_call c /\
  run_call v = SOME (INL (),t) /\ LENGTH t.contexts = LENGTH s.contexts ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `wf_state s /\ (?d. s.msdomain = Collect d) /\ ~c.msgParams.static /\
   asm_evm_rel (prog ++ [AsmDataItem data]) a s` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `next_opcode c = SOME DelegateCall` by
    (drule_all asm_frame_delegate_decode >> simp[]) >>
  `wf_state v /\ (?d. v.msdomain = Collect d)` by
    (conj_tac
     >- (drule_all step_preserves_wf_state >> simp[]) >>
     drule_at (Pat `step _ = _`) step_preserves_collect >> simp[]) >>
  `wf_state t /\ (?d. t.msdomain = Collect d)` by
    (conj_tac
     >- (drule_all run_call_preserves_wf_state >> simp[]) >>
     drule_at (Pat `run_call _ = _`) asm_call_run_collect >> simp[]) >>
  `t.txParams = s.txParams` by
    (drule asm_call_run_txParams >> strip_tac >>
     qspec_then `s` mp_tac vfmTxParamsTheory.step_preserves_txParams >> simp[]) >>
  (Q.SUBGOAL_THEN `?dv. v.msdomain = Collect dv` assume_tac >- simp[]) >>
  `LENGTH t.contexts = SUC (LENGTH rest)` by simp[] >>
  (Q.SUBGOAL_THEN `DelegateCall = Call \/ DelegateCall = StaticCall \/ DelegateCall = DelegateCall`
    assume_tac >- simp[]) >>
  drule_all asm_message_prepared_run_selectors >>
  disch_then (qspecl_then [`LENGTH c.logs`,`LENGTH s.rollback.toDelete`] mp_tac) >>
  simp[call_has_value_def] >> strip_tac >>
  drule_all asm_message_prepared_run_adoption >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  drule_all asm_message_prepared_enter_view >> strip_tac >>
  `LENGTH v.contexts = SUC (LENGTH s.contexts)` by simp[] >>
  drule_all asm_frame_call_enter_transport >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  suspend "consume"
QED

Resume asm_frame_delegate_enter_step_ok[consume]:
  `(a.as_call_ctx.cc_created_in_tx =
      account_empty (lookup_account c.msgParams.callee t.originalAccounts)) /\
    (~a.as_call_ctx.cc_created_in_tx ==> account_already_created
      (lookup_account c.msgParams.callee t.rollback.accounts))` by
    (mp_tac (Q.INST [`s` |-> `s`, `v` |-> `v`, `r` |-> `INL ()`, `t` |-> `t`,
       `self` |-> `c.msgParams.callee`, `created` |-> `a.as_call_ctx.cc_created_in_tx`]
       step_run_call_creation_guard) >> gvs[asm_frame_rel_def] >> metis_tac[]) >>
  `a.as_accounts = s.rollback.accounts /\ a.as_transient = s.rollback.tStorage /\
   a.as_logs = c.logs /\ a.as_pending_deletions = s.rollback.toDelete /\
   a.as_memory = buffer_to_list c.memory` by gvs[asm_evm_rel_def] >>
  `(request_of s).cr_kind = DelegateMessageCall /\
    ~computed_precompile (request_of s)` by simp[request_of_def, computed_precompile_def] >>
  qmatch_asmsub_abbrev_tac `adopt_outcome (request_of s) out _ = _` >>
  `take_outcome (request_of s) a.as_outcomes = (out,MAP SND (call_trace t))` by
    simp[Abbr `out`, take_outcome_def] >>
  `ct.stack = (if out.co_success then 1w else 0w)::DROP 6 c.stack /\
   ct.returnData = out.co_returnData` by
    simp[Abbr `out`, asm_delegate_outcome_view] >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
    asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1` by
    (irule asm_frame_delegate_pc_increment >> simp[]) >>
  drule_all asm_frame_delegate_consume >> disch_tac >>
  `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a =
   asm_consume_call_outcome (request_of s) ro rs
     (DROP (6 + (if call_has_value DelegateCall then 1 else 0)) a.as_stack)
     (a with as_memory := asm_call_memory ao az ro rs a.as_memory)` by
    simp[call_has_value_def] >>
  drule_at (Pat `asm_step _ _ _ _ = _`) asm_frame_outcome_effects_step_ok >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (drule_at (Pat `asm_frame_rel _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `s.contexts = _`)) >>
  disch_then (qspecl_then [`out`,`c`,`az`,`ao`] mp_tac) >>
  simp[call_has_value_def] >> metis_tac[]
QED
Finalise asm_frame_delegate_enter_step_ok

Theorem asm_frame_delegate_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp "DELEGATECALL" ==>
  asm_frame_step_ok prog data es0 as es
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `?c rb rest. es.contexts = (c,rb)::rest` by
    metis_tac[asm_frame_rel_def] >>
  Cases_on `asm_call_prepare DelegateCall es` >>
  rename1 `asm_call_prepare DelegateCall es = (q,u)` >> Cases_on `q`
  >- (PairCases_on `x` >>
      rename1 `asm_call_prepare DelegateCall es =
        (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u)` >>
      Cases_on `(lookup_account sender accounts).balance < value \/ 1024 < LENGTH es.contexts`
      >- (drule_all asm_frame_delegate_abort >> simp[]) >>
      `value <= (lookup_account sender accounts).balance /\ LENGTH es.contexts <= 1024`
        by (qpat_x_assum `~(_ \/ _)` mp_tac >> simp[]) >>
      Cases_on `asm_call_finish DelegateCall (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u` >>
      rename1 `asm_call_finish DelegateCall _ u = (q,v)` >> Cases_on `q`
      >- (Cases_on `x` >> suspend "entered") >>
      drule_all asm_frame_delegate_terminal >> simp[]) >>
  drule_all asm_frame_delegate_prepare_exit >> simp[]
QED

Resume asm_frame_delegate_step[entered]:
  `wf_state es /\ (?d. es.msdomain = Collect d) /\ ~c.msgParams.static /\
   asm_evm_rel (prog ++ [AsmDataItem data]) as es` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `next_opcode c = SOME DelegateCall` by
    (drule_all asm_frame_delegate_decode >> simp[]) >>
  `step_call DelegateCall es = (INL (),v)` by
    simp[asm_step_call_factor, bind_def] >>
  `step es = (INL (),v)` by
    (irule asm_message_step_success >> simp[] >> metis_tac[]) >>
  `6 <= LENGTH c.stack` by
    (drule_at (Pat `asm_call_prepare _ _ = _`) asm_message_prepare_success_view >>
     disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
     simp[call_has_value_def] >> metis_tac[]) >>
  `observable_call c` by simp[observable_call_def] >>
  (Q.SUBGOAL_THEN `DelegateCall = Call \/ DelegateCall = StaticCall \/ DelegateCall = DelegateCall`
    assume_tac >- simp[]) >>
  drule_all asm_message_prepared_enter_view >> strip_tac >>
  `wf_state v /\ (?d. v.msdomain = Collect d)` by
    (conj_tac >- (drule_all step_preserves_wf_state >> simp[]) >>
     drule_at (Pat `step _ = _`) step_preserves_collect >> simp[]) >>
  `2 <= LENGTH v.contexts` by simp[] >>
  (Q.SUBGOAL_THEN `?d. v.msdomain = Collect d` assume_tac >- simp[]) >>
  drule_all asm_call_child_run_normal >> strip_tac >>
  `LENGTH t.contexts = LENGTH es.contexts` by
    (qpat_x_assum `LENGTH t.contexts + 1 = _` mp_tac >> simp[]) >>
  drule_all asm_frame_delegate_enter_step_ok >> simp[]
QED

Finalise asm_frame_delegate_step
