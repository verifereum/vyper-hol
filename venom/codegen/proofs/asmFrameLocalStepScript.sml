(*
 * Every instruction but CALL and STATICCALL against the frame's run:
 * the single-context steps (asmEvmStepStarve, asmEvmGasStep) moved into
 * the nested frame (evmStepTransplant), with the frame's trace and
 * run_call carried across the step (frameObsStep).
 *
 * TOP-LEVEL:
 *   asm_frame_local_step
 *)

Theory asmFrameLocalStep
Ancestors
  asmFrameRel frameObsStep evmStepTransplant asmEvmStepStarve asmEvmGasStep
  evmStepSim asmDataSuffixProps codegenRel asmSem asmWf symbolResolve
  callTrace frameOutcome vfmExecution vfmExecutionProp list rich_list
  vfmOperation alist asmEncodeParse vfmState vfmSameFrame vfmRunWithinFrame
  vfmRunCall vfmContext vfmContextLength evmCreationGuard

Theorem frame_rel_singleton[local]:
  asm_evm_rel p a es /\ es.contexts = (c,rb)::rest ==>
  asm_evm_rel p a (es with contexts := [(c,rb)])
Proof
  strip_tac >> gvs[asm_evm_rel_def]
QED

Theorem frame_rel_output_to[local]:
  asm_evm_rel p a es /\ es.contexts = (c,rb)::rest ==>
  !addr. c.msgParams.outputTo <> Code addr
Proof
  strip_tac >> gvs[asm_evm_rel_def]
QED

Theorem frame_local_instruction[local]:
  asm_frame_prog_ok prog /\ i < LENGTH prog /\
  ~is_data_inst (EL i prog) /\
  EL i prog <> AsmOp "CALL" /\ EL i prog <> AsmOp "STATICCALL" /\
  EL i prog <> AsmOp "DELEGATECALL" /\ EL i prog <> AsmOp "CREATE" /\
  EL i prog <> AsmOp "CREATE2" /\ EL i prog <> AsmOp "SELFDESTRUCT" ==>
  asm_encoding_wf prog /\
  (!j. j <= i ==> ~is_data_inst (EL j prog)) /\
  (!name. EL i prog = AsmOp name ==> ~is_evm_call_name name)
Proof
  simp[asm_frame_prog_ok_def, is_evm_call_name_def] >> metis_tac[]
QED

Theorem frame_next_opcode[local]:
  asm_frame_prog_ok prog /\
  asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  es.contexts = (c,rb)::rest /\ a.as_pc < LENGTH prog /\
  ~is_data_inst (EL a.as_pc prog) ==>
  ?op. next_opcode c = SOME op /\ wf_opname op /\
    opcode op = encode_inst (SND (compute_label_offsets
      (prog ++ [AsmDataItem data]))) (EL a.as_pc prog)
Proof
  strip_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a
    (es with contexts := [(c,rb)])` by metis_tac[frame_rel_singleton] >>
  `asm_encoding_wf prog /\
   (!j. j <= a.as_pc ==> ~is_data_inst (EL j prog))` by
    metis_tac[asm_frame_prog_ok_def] >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    metis_tac[data_suffix_encoding_wf] >>
  `a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `!j. j <= a.as_pc ==>
       ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (gen_tac >> disch_tac >> `j < LENGTH prog` by decide_tac >>
     simp[EL_APPEND1]) >>
  `LENGTH (es with contexts := [(c,rb)]).contexts = 1` by simp[] >>
  `~is_data_inst (EL a.as_pc (prog ++ [AsmDataItem data]))` by
    simp[EL_APPEND1] >>
  drule_all asm_evm_step_setup >>
  simp[EL_APPEND1] >> strip_tac >> gvs[] >>
  simp[next_opcode_def] >> metis_tac[]
QED

Theorem frame_encode_system[local]:
  ~is_data_inst inst /\
  MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2; Gas] /\
  opcode op = encode_inst offsets inst ==>
  (inst = AsmOp "CALL" /\ op = Call) \/
  (inst = AsmOp "STATICCALL" /\ op = StaticCall) \/
  (inst = AsmOp "DELEGATECALL" /\ op = DelegateCall) \/
  (inst = AsmOp "CREATE" /\ op = Create) \/
  (inst = AsmOp "CREATE2" /\ op = Create2) \/
  (inst = AsmOp "GAS" /\ op = Gas)
Proof
  Cases_on `inst`
  >- (simp[encode_inst_def] >> strip_tac >>
      gvs[opcode_def, AllCaseEqs(), evm_opcode_byte_def] >>
      drule ALOOKUP_MEM >>
      qpat_x_assum `ALOOKUP _ _ = _` kall_tac >>
      simp_tac std_ss [evm_opcode_table_def, MEM, pairTheory.PAIR_EQ,
        wordsTheory.n2w_11, wordsTheory.dimword_8]) >>
  strip_tac >>
  gvs[is_data_inst_def, encode_inst_def, opcode_def,
      AllCaseEqs(), wordsTheory.dimword_8] >>
  Cases_on `l` >> gvs[encode_inst_def, wordsTheory.dimword_8]
QED

Theorem frame_local_opcode[local]:
  asm_frame_prog_ok prog /\
  asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  es.contexts = (c,rb)::rest /\ a.as_pc < LENGTH prog /\
  ~is_data_inst (EL a.as_pc prog) /\
  EL a.as_pc prog <> AsmOp "CALL" /\
  EL a.as_pc prog <> AsmOp "STATICCALL" /\
  EL a.as_pc prog <> AsmOp "DELEGATECALL" /\
  EL a.as_pc prog <> AsmOp "CREATE" /\
  EL a.as_pc prog <> AsmOp "CREATE2" /\
  EL a.as_pc prog <> AsmOp "SELFDESTRUCT" ==>
  (!op. next_opcode c = SOME op ==>
     ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  ~observable_call c /\
  (next_opcode c = SOME Gas <=> EL a.as_pc prog = AsmOp "GAS")
Proof
  strip_tac >> drule_all frame_next_opcode >> strip_tac >>
  `~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]` by
    (strip_tac >>
     `MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2; Gas]`
       by gvs[] >>
     drule_all frame_encode_system >>
     gvs[asm_frame_prog_ok_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  conj_tac >- (gvs[observable_call_def] >> metis_tac[]) >>
  simp[] >>
  eq_tac
  >- (strip_tac >>
      `MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2; Gas]`
        by simp[] >>
      drule_all frame_encode_system >> gvs[]) >>
  strip_tac >> gvs[] >>
  `opcode op = opcode Gas` by
    gvs[encode_inst_def, evm_opcode_byte_def, evm_opcode_table_def, opcode_def] >>
  `op = Gas` by (irule opcode_wf_inj >> simp[wf_opname_def]) >> simp[]
QED

Theorem frame_continue_transplant[local]:
  es.contexts = (c,rb)::rest /\ wf_state es /\
  (!op. next_opcode c = SOME op ==>
    ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c,rb)]) = (INL (),t) /\
  LENGTH t.contexts = 1 /\ asm_evm_rel p a t ==>
  ?es1. step es = (INL (),es1) /\
    LENGTH es1.contexts = LENGTH es.contexts /\
    run_call es1 = run_call es /\ asm_evm_rel p a es1
Proof
  strip_tac >> Cases_on `rest = []`
  >- (`es with contexts := [(c,rb)] = es` by
        (gvs[execution_state_component_equality]) >>
      gvs[] >>
      irule run_call_same_depth_step >> simp[]) >>
  drule_all step_transplant_continue >> strip_tac >>
  qexists_tac `t with contexts := (c',rb)::rest` >>
  conj_tac >- simp[] >>
  conj_asm1_tac >- simp[] >>
  conj_tac >- (irule run_call_same_depth_step >> simp[]) >>
  gvs[asm_evm_rel_def]
QED

Theorem frame_continue_rel[local]:
  asm_frame_rel prog data es0 a es /\
  step es = (INL (),es1) /\
  LENGTH es1.contexts = LENGTH es.contexts /\
  asm_evm_rel (prog ++ [AsmDataItem data]) a1 es1 /\
  a1.as_call_ctx = a.as_call_ctx /\
  a1.as_requests = a.as_requests /\ call_trace es1 = call_trace es /\
  a1.as_outcomes = MAP SND (call_trace es1) /\
  a1.as_gas_readings = gas_readings es1 ==>
  asm_frame_rel prog data es0 a1 es1
Proof
  strip_tac >>
  qpat_x_assum `asm_frame_rel _ _ _ _ _` mp_tac >>
  simp[asm_frame_rel_def] >> strip_tac >>
  `!addr. c.msgParams.outputTo <> Code addr` by
    metis_tac[frame_rel_output_to] >>
  `outputTo_consistent es` by gvs[outputTo_consistent_def] >>
  `same_frame_rel es es1` by (irule step_same_frame >> simp[]) >>
  `wf_state es1` by
    (drule step_preserves_wf_state >> simp[]) >>
  `account_empty (lookup_account c.msgParams.callee es1.originalAccounts) =
   account_empty (lookup_account c.msgParams.callee es.originalAccounts)` by
    (irule step_creation_original_empty >> metis_tac[]) >>
  `!addr. account_already_created (lookup_account addr es.rollback.accounts) ==>
      account_already_created (lookup_account addr es1.rollback.accounts)` by
    (mp_tac (Q.INST [`d` |-> `LENGTH es.contexts`, `B` |-> `es.rollback`,
                    `s` |-> `es`, `t` |-> `es1`, `x` |-> `()`]
       step_continuing_collision_current) >> simp[]) >>
  Cases_on `es1.contexts` >> gvs[same_frame_rel_def] >>
  PairCases_on `h` >> gvs[] >>
  `?d1. es1.msdomain = Collect d1` by
    (Cases_on `es1.msdomain` >> gvs[msdomain_compatible_def]) >>
  simp[asm_frame_rel_def] >> gvs[call_requests_def]
QED

Theorem frame_terminal_transplant[local]:
  asm_frame_rel prog data es0 a es /\ es.contexts = (c,rb)::rest /\
  (!op. next_opcode c = SOME op ==>
    ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c,rb)]) = (INR e,t) /\
  t.contexts = [(ct,rt)] /\ ~vfm_abort e ==>
  ?r es' lgs. run_call es = SOME (r,es') /\
    frame_outcome es0 r es' e ct.returnData lgs /\
    (e = NONE ==> lgs = ct.logs /\ es'.rollback = t.rollback) /\
    call_requests es = []
Proof
  strip_tac >>
  qpat_x_assum `asm_frame_rel _ _ _ _ _` mp_tac >>
  simp[asm_frame_rel_def] >> strip_tac >> gvs[] >>
  `!addr. c.msgParams.outputTo <> Code addr` by
    metis_tac[frame_rel_output_to] >>
  Cases_on `rest = []`
  >- (`es with contexts := [(c,rb)] = es` by
        gvs[execution_state_component_equality] >>
      `t.txParams = es.txParams` by
        (irule same_frame_rel_imp_txParams_rel >> irule step_same_frame >>
         gvs[outputTo_consistent_def]) >>
      `step es = (INR e,t)` by gvs[] >>
      `run_call es = SOME (INR e,t)` by
        (irule run_call_terminal_step >> simp[]) >>
      `call_trace es = []` by
        (drule frame_obs_terminal >> simp[]) >>
      qexistsl_tac [`INR e`,`t`,`ct.logs`] >>
      simp[frame_outcome_def, call_requests_def]) >>
  drule_all (SRULE [MEM] step_transplant_end) >> strip_tac >> gvs[] >>
  `LENGTH es'.contexts < LENGTH es.contexts` by
    (qpat_x_assum `frame_outcome es _ _ _ _ _` mp_tac >>
     simp[frame_outcome_def] >> Cases_on `rest` >> gvs[] >>
     Cases_on `h` >> gvs[] >> strip_tac >> gvs[] >>
     qpat_x_assum `MAP _ _ = MAP _ _`
       (mp_tac o AP_TERM ``LENGTH : context list -> num``) >> simp[]) >>
  `run_call es = SOME (INL (),es')` by
    (irule run_call_terminal_step >> simp[]) >>
  `call_trace es = []` by (drule frame_obs_terminal >> simp[]) >>
  drule_all frame_outcome_mid >> strip_tac >>
  qexistsl_tac [`INL ()`,`es'`,`c.logs ++ lgs`] >>
  simp[call_requests_def]
QED

Theorem frame_terminal_singleton_length[local]:
  wf_state es /\ es.contexts = (c,rb)::rest /\
  (!addr. c.msgParams.outputTo <> Code addr) /\
  step (es with contexts := [(c,rb)]) = (INR e,t) /\ ~vfm_abort e ==>
  LENGTH t.contexts = 1
Proof
  strip_tac >>
  `EVERY (wf_context o FST) (es with contexts := [(c,rb)]).contexts` by
    gvs[wf_state_def] >>
  `(es with contexts := [(c,rb)]).contexts <> []` by simp[] >>
  `outputTo_consistent (es with contexts := [(c,rb)])` by
    simp[outputTo_consistent_def] >>
  drule_all step_inr_not_abort_length >> simp[] >> strip_tac >>
  drule step_preserves_nonempty_contexts >> simp[] >>
  Cases_on `t.contexts` >> gvs[]
QED

Theorem frame_starved_lift[local]:
  asm_frame_rel prog data es0 a es /\ es.contexts = (c,rb)::rest /\
  (!op. next_opcode c = SOME op ==>
    ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c,rb)]) = (INR (SOME exc),t) /\
  (exc = OutOfGas \/ exc = StackOverflow) ==>
  ?r es'. run_call es = SOME (r,es') /\ frame_resource_starved es0 r es'
Proof
  strip_tac >>
  `wf_state es /\ (!addr. c.msgParams.outputTo <> Code addr)` by
    (gvs[asm_frame_rel_def] >> metis_tac[frame_rel_output_to]) >>
  `~vfm_abort (SOME exc)` by
    (gvs[vfm_abort_def]) >>
  `LENGTH t.contexts = 1` by
    (irule frame_terminal_singleton_length >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  Cases_on `t.contexts` >> gvs[] >> PairCases_on `h` >>
  drule (SRULE [MEM] frame_terminal_transplant) >>
  disch_then drule >> simp[vfm_abort_def] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[frame_resource_starved_def] >>
  metis_tac[]
QED

Theorem frame_terminal_lift[local]:
  asm_frame_rel prog data es0 a es /\ es.contexts = (c,rb)::rest /\
  (!op. next_opcode c = SOME op ==>
    ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c,rb)]) = (INR e,t) /\
  LENGTH t.contexts = 1 /\ ~vfm_abort e ==>
  ?r es' lgs. run_call es = SOME (r,es') /\
    frame_outcome es0 r es' e (FST (HD t.contexts)).returnData lgs /\
    (e = NONE ==> lgs = (FST (HD t.contexts)).logs /\
                  es'.rollback = t.rollback) /\ call_requests es = []
Proof
  strip_tac >> Cases_on `t.contexts` >> gvs[] >> PairCases_on `h` >>
  drule (SRULE [MEM] frame_terminal_transplant) >>
  disch_then drule >> simp[]
QED

Theorem frame_terminal_rel_lift[local]:
  asm_frame_rel prog data es0 a es /\ es.contexts = (c,rb)::rest /\
  (!op. next_opcode c = SOME op ==>
    ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c,rb)]) = (INR e,t) /\
  LENGTH t.contexts = 1 /\ ~vfm_abort e /\
  asm_evm_rel (prog ++ [AsmDataItem data]) a1 t ==>
  ?r es' lgs. run_call es = SOME (r,es') /\
    frame_outcome es0 r es' e a1.as_returndata lgs /\
    (e = NONE ==> lgs = a1.as_logs /\
      es'.rollback.accounts = a1.as_accounts /\
      es'.rollback.toDelete = a1.as_pending_deletions /\
      es'.rollback.tStorage = a1.as_transient) /\ call_requests es = []
Proof
  strip_tac >> drule_all frame_terminal_lift >> strip_tac >>
  Cases_on `t.contexts` >> gvs[] >> PairCases_on `h` >>
  gvs[asm_evm_rel_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem frame_asm_stack_observers[local]:
  MEM r [asm_binop f a; asm_unop g a; asm_ternop h a;
         asm_push_val w a; asm_pop a; asm_dup n a; asm_swap n a;
         asm_state_unop k a] /\
  (r = AsmOK a1 \/ r = AsmHalt a1) ==>
  a1.as_requests = a.as_requests /\ a1.as_outcomes = a.as_outcomes /\
  a1.as_gas_readings = a.as_gas_readings /\ a1.as_call_ctx = a.as_call_ctx
Proof
  simp[MEM] >> strip_tac >>
  gvs[asm_binop_def, asm_unop_def, asm_ternop_def, asm_push_val_def,
      asm_pop_def, asm_dup_def, asm_swap_def, asm_state_unop_def,
      asm_next_def, AllCaseEqs()]
QED

Theorem frame_asm_memory_observers[local]:
  MEM r [asm_mload a; asm_mstore a; asm_mstore8 a; asm_sload a;
         asm_sstore a; asm_tload a; asm_tstore a; asm_jump pc a;
         asm_jumpi pc a; asm_return_op a; asm_revert_op a;
         asm_log n a; asm_sha3 a; asm_copy_to_mem bytes a;
         asm_returndatacopy a; asm_extcodecopy a; asm_mcopy a] /\
  (r = AsmOK a1 \/ r = AsmHalt a1) ==>
  a1.as_requests = a.as_requests /\ a1.as_outcomes = a.as_outcomes /\
  a1.as_gas_readings = a.as_gas_readings /\ a1.as_call_ctx = a.as_call_ctx
Proof
  simp[MEM] >> strip_tac >>
  gvs[asm_mload_def, asm_mstore_def, asm_mstore8_def, asm_sload_def,
      asm_sstore_def, asm_tload_def, asm_tstore_def, asm_jump_def,
      asm_jumpi_def, asm_return_op_def, asm_revert_op_def, asm_log_def,
      asm_sha3_def, asm_copy_to_mem_def, asm_returndatacopy_def,
      asm_extcodecopy_def, asm_mcopy_def, asm_expand_memory_def,
      asm_next_def, AllCaseEqs()]
QED

Theorem frame_pred_cond[local]:
  P (if b then x else y) = (if b then P x else P y)
Proof
  Cases_on `b` >> simp[]
QED

Theorem frame_context_pred[local]:
  !P name a. name <> "GAS" /\ P NONE /\
  (!w. P (SOME (asm_push_val w a))) /\
  (!k. P (SOME (asm_state_unop k a))) ==>
  P (asm_step_context name a)
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[asm_step_context_def] >>
  ASM_SIMP_TAC bool_ss [frame_pred_cond]
QED

Theorem frame_asm_group_observers:
  name <> "GAS" /\ ~is_evm_call_name name /\ name <> "SELFDESTRUCT" /\
  MEM (SOME r) [asm_step_arith name a; asm_step_compare name a;
    asm_step_bitwise name a; asm_step_memory name a;
    asm_step_control pc name a; asm_step_extcall name a;
    asm_step_copy name a; asm_step_context name a] /\
  (r = AsmOK a1 \/ r = AsmHalt a1) ==>
  a1.as_requests = a.as_requests /\ a1.as_outcomes = a.as_outcomes /\
  a1.as_gas_readings = a.as_gas_readings /\ a1.as_call_ctx = a.as_call_ctx
Proof
  simp[MEM, is_evm_call_name_def] >> strip_tac >>
  all_tac
  >- suspend "arith" >- suspend "arith"
  >- suspend "compare" >- suspend "compare"
  >- suspend "bitwise" >- suspend "bitwise"
  >- suspend "memory" >- suspend "memory"
  >- suspend "control" >- suspend "control"
  >- suspend "extcall" >- suspend "extcall"
  >- suspend "copy" >- suspend "copy"
  >- suspend "context" >> suspend "context"
QED

Resume frame_asm_group_observers[arith]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[asm_step_arith_def, AllCaseEqs()] >>
  metis_tac[frame_asm_stack_observers, MEM]
QED
Resume frame_asm_group_observers[compare]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[asm_step_compare_def, AllCaseEqs()] >>
  metis_tac[frame_asm_stack_observers, MEM]
QED
Resume frame_asm_group_observers[bitwise]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[asm_step_bitwise_def, AllCaseEqs()] >>
  metis_tac[frame_asm_stack_observers, MEM]
QED
Resume frame_asm_group_observers[memory]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  gvs[asm_step_memory_def, asm_pop_def, asm_push_val_def, asm_next_def,
      AllCaseEqs()] >>
  metis_tac[frame_asm_memory_observers, MEM]
QED
Resume frame_asm_group_observers[control]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[asm_step_control_def, asm_next_def, AllCaseEqs()] >>
  metis_tac[frame_asm_memory_observers, MEM]
QED
Resume frame_asm_group_observers[extcall]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[asm_step_extcall_def]
QED
Resume frame_asm_group_observers[copy]:
  markerLib.RESUME_TAC >> rpt strip_tac >> gvs[asm_step_copy_def, AllCaseEqs()] >>
  metis_tac[frame_asm_memory_observers, MEM]
QED
Resume frame_asm_group_observers[context]:
  markerLib.RESUME_TAC >>
  qspec_then `\v. !r a1. v = SOME r /\
    (r = AsmOK a1 \/ r = AsmHalt a1) ==>
    a1.as_requests = a.as_requests /\ a1.as_outcomes = a.as_outcomes /\
    a1.as_gas_readings = a.as_gas_readings /\ a1.as_call_ctx = a.as_call_ctx` mp_tac frame_context_pred >>
  disch_then (qspecl_then [`name`,`a`] mp_tac) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >>
     conj_tac >> simp_tac std_ss [] >>
     metis_tac[frame_asm_stack_observers, MEM])) >>
  disch_then (qspecl_then [`r`,`a1`] mp_tac) >> simp[]
QED
Finalise frame_asm_group_observers[local]

Theorem frame_asm_step_observers[local]:
  (!name. inst = AsmOp name ==>
    ~is_evm_call_name name /\ name <> "GAS" /\ name <> "SELFDESTRUCT") /\
  (asm_step labels pc inst a = AsmOK a1 \/
   asm_step labels pc inst a = AsmHalt a1) ==>
  a1.as_requests = a.as_requests /\ a1.as_outcomes = a.as_outcomes /\
  a1.as_gas_readings = a.as_gas_readings /\ a1.as_call_ctx = a.as_call_ctx
Proof
  Cases_on `inst` >> simp[asm_step_def] >> strip_tac >>
  gvs[asm_next_def, AllCaseEqs()] >>
  gvs[asm_step_op_def, AllCaseEqs()] >>
  gvs[asm_dup_def, asm_swap_def, asm_log_def, asm_expand_memory_def,
      asm_next_def, AllCaseEqs()] >>
  metis_tac[frame_asm_group_observers, MEM]
QED

Theorem frame_plain_singleton_sim[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
  es.contexts = (c,rb)::rest /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  EL a.as_pc prog <> AsmOp "CALL" /\
  EL a.as_pc prog <> AsmOp "STATICCALL" /\
  EL a.as_pc prog <> AsmOp "DELEGATECALL" /\
  EL a.as_pc prog <> AsmOp "CREATE" /\
  EL a.as_pc prog <> AsmOp "CREATE2" /\
  EL a.as_pc prog <> AsmOp "SELFDESTRUCT" /\
  EL a.as_pc prog <> AsmOp "GAS" ==>
  (?t exc. step (es with contexts := [(c,rb)]) = (INR (SOME exc),t) /\
     (exc = OutOfGas \/ exc = StackOverflow)) \/
  case asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
                (EL a.as_pc prog) a of
    AsmOK a1 => ?t. step (es with contexts := [(c,rb)]) = (INL (),t) /\
      LENGTH t.contexts = 1 /\ asm_evm_rel (prog ++ [AsmDataItem data]) a1 t
  | AsmHalt a1 => ?t. step (es with contexts := [(c,rb)]) = (INR NONE,t) /\
      LENGTH t.contexts = 1 /\ asm_evm_rel (prog ++ [AsmDataItem data]) a1 t
  | AsmRevert a1 => ?t. step (es with contexts := [(c,rb)]) = (INR (SOME Reverted),t) /\
      LENGTH t.contexts = 1 /\ asm_evm_rel (prog ++ [AsmDataItem data]) a1 t
  | AsmFault a1 => ?t exc. step (es with contexts := [(c,rb)]) = (INR (SOME exc),t) /\
      exc <> Reverted /\ ~vfm_abort (SOME exc) /\ LENGTH t.contexts = 1 /\
      (FST (HD t.contexts)).returnData = []
  | AsmError _ => T
Proof
  strip_tac >> irule asm_evm_step_starve >>
  drule_all frame_local_instruction >> strip_tac >>
  gvs[asm_frame_prog_ok_def, asm_frame_rel_def] >>
  metis_tac[frame_rel_singleton]
QED

Theorem frame_plain_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  EL a.as_pc prog <> AsmOp "CALL" /\
  EL a.as_pc prog <> AsmOp "STATICCALL" /\
  EL a.as_pc prog <> AsmOp "DELEGATECALL" /\
  EL a.as_pc prog <> AsmOp "CREATE" /\
  EL a.as_pc prog <> AsmOp "CREATE2" /\
  EL a.as_pc prog <> AsmOp "SELFDESTRUCT" /\
  EL a.as_pc prog <> AsmOp "GAS" ==>
  asm_frame_step_ok prog data es0 a es
Proof
  strip_tac >>
  `?c rb rest. es.contexts = (c,rb)::rest` by gvs[asm_frame_rel_def] >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a es /\ wf_state es` by
    gvs[asm_frame_rel_def] >>
  drule_all frame_local_opcode >> strip_tac >>
  drule_all frame_plain_singleton_sim >> strip_tac
  >- (simp[asm_frame_step_ok_def] >> disj1_tac >>
      irule frame_starved_lift >> metis_tac[]) 
  >- (simp[asm_frame_step_ok_def] >> disj1_tac >>
      irule frame_starved_lift >> metis_tac[]) >>
  Cases_on `asm_step (SND (compute_label_offsets prog))
    (build_offset_to_pc prog) (EL a.as_pc prog) a` >>
  gvs[asm_frame_step_ok_def]
  >- suspend "ok"
  >- suspend "halt"
  >- suspend "revert"
  >> suspend "fault"
QED

Resume frame_plain_step[ok]:
  drule_all (SRULE [MEM] frame_continue_transplant) >> strip_tac >>
  `next_opcode (FST (HD es.contexts)) <> SOME Gas /\
   ~observable_call (FST (HD es.contexts))` by simp[] >>
  `LENGTH es1.contexts = LENGTH es.contexts` by simp[] >>
  drule_all frame_obs_plain_step >> strip_tac >>
  `!name. EL a.as_pc prog = AsmOp name ==>
    ~is_evm_call_name name /\ name <> "GAS" /\ name <> "SELFDESTRUCT"` by
    (drule_all frame_local_instruction >> strip_tac >>
     gvs[asm_frame_prog_ok_def] >> metis_tac[]) >>
  `a'.as_requests = a.as_requests /\ a'.as_outcomes = a.as_outcomes /\
   a'.as_gas_readings = a.as_gas_readings /\ a'.as_call_ctx = a.as_call_ctx` by
    (irule frame_asm_step_observers >> metis_tac[]) >>
  disj2_tac >> goal_assum (drule_at Any) >>
  irule frame_continue_rel >> simp[] >>
  conj_tac >- gvs[asm_frame_rel_def] >>
  conj_tac >- gvs[asm_frame_rel_def] >>
  qexistsl_tac [`a`,`es`] >> simp[]
QED
Resume frame_plain_step[halt]:
  drule (SRULE [MEM] frame_terminal_rel_lift) >>
  disch_then drule >> simp[vfm_abort_def] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  `!name. EL a.as_pc prog = AsmOp name ==>
    ~is_evm_call_name name /\ name <> "GAS" /\ name <> "SELFDESTRUCT"` by
    (drule_all frame_local_instruction >> strip_tac >>
     gvs[asm_frame_prog_ok_def] >> metis_tac[]) >>
  `a'.as_requests = a.as_requests` by
    metis_tac[frame_asm_step_observers] >>
  disj2_tac >> goal_assum (drule_at Any) >>
  gvs[asm_frame_rel_def]
QED
Resume frame_plain_step[revert]:
  drule (SRULE [MEM] frame_terminal_rel_lift) >>
  disch_then drule >> simp[vfm_abort_def] >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  disj2_tac >> metis_tac[]
QED
Resume frame_plain_step[fault]:
  drule_all (SRULE [MEM] frame_terminal_lift) >> strip_tac >>
  disj2_tac >> metis_tac[]
QED
Finalise frame_plain_step[local]

Theorem frame_rel_readings_update[local]:
  asm_evm_rel p a es ==>
  asm_evm_rel p (a with as_gas_readings := readings) es
Proof
  simp[asm_evm_rel_def]
QED

Theorem frame_gas_asm_step[local]:
  a.as_gas_readings = w::readings ==>
  asm_step labels pc (AsmOp "GAS") a =
    AsmOK (a with <|as_stack := w::a.as_stack; as_pc := a.as_pc + 1;
                   as_gas_readings := readings|>)
Proof
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def, asm_gas_def, asm_push_val_def, asm_next_def]
QED

Theorem frame_gas_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
  a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
  EL a.as_pc prog <> AsmOp "CALL" /\
  EL a.as_pc prog <> AsmOp "STATICCALL" /\
  EL a.as_pc prog = AsmOp "GAS" ==>
  asm_frame_step_ok prog data es0 a es
Proof
  strip_tac >>
  `EL a.as_pc prog <> AsmOp "DELEGATECALL" /\
   EL a.as_pc prog <> AsmOp "CREATE" /\
   EL a.as_pc prog <> AsmOp "CREATE2" /\
   EL a.as_pc prog <> AsmOp "SELFDESTRUCT"` by simp[] >>
  `?c rb rest. es.contexts = (c,rb)::rest` by gvs[asm_frame_rel_def] >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a es /\ wf_state es` by
    gvs[asm_frame_rel_def] >>
  drule_all frame_local_opcode >> strip_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a
    (es with contexts := [(c,rb)])` by metis_tac[frame_rel_singleton] >>
  `asm_encoding_wf prog /\ (!j. j <= a.as_pc ==>
    ~is_data_inst (EL j prog))` by metis_tac[frame_local_instruction] >>
  `LENGTH (es with contexts := [(c,rb)]).contexts = 1` by simp[] >>
  drule_all asm_evm_gas_step >> strip_tac
  >- (simp[asm_frame_step_ok_def] >> disj1_tac >>
      irule frame_starved_lift >> metis_tac[])
  >- (simp[asm_frame_step_ok_def] >> disj1_tac >>
      irule frame_starved_lift >> metis_tac[]) >>
  suspend "continue"
QED
Resume frame_gas_step[continue]:
  rename1 `step (es with contexts := [(c,rb)]) = (INL (),t)` >>
  drule_all frame_continue_transplant >> strip_tac >>
  `LENGTH es1.contexts = LENGTH es.contexts /\
   next_opcode (FST (HD es.contexts)) = SOME Gas` by simp[] >>
  drule_all frame_obs_gas_step >> strip_tac >>
  `HD (FST (HD es1.contexts)).stack = w` by
    (qpat_x_assum `asm_evm_rel _ _ es1` mp_tac >>
     simp[asm_evm_rel_def] >> Cases_on `es1.contexts` >> simp[] >>
     PairCases_on `h` >> simp[] >> strip_tac >> gvs[]) >>
  `a.as_gas_readings = w::gas_readings es1` by
    gvs[asm_frame_rel_def] >>
  drule frame_gas_asm_step >> strip_tac >>
  simp[asm_frame_step_ok_def] >> disj2_tac >>
  goal_assum (drule_at Any) >>
  irule frame_continue_rel >> simp[] >>
  conj_tac >- gvs[asm_frame_rel_def] >>
  conj_tac
  >- (drule frame_rel_readings_update >>
      disch_then (qspec_then `gas_readings es1` mp_tac) >> simp[]) >>
  qexistsl_tac [`a`,`es`] >> simp[]
QED
Finalise frame_gas_step[local]

Theorem asm_frame_noncall_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
  EL as.as_pc prog <> AsmOp "CALL" /\ EL as.as_pc prog <> AsmOp "STATICCALL" /\
  EL as.as_pc prog <> AsmOp "DELEGATECALL" /\
  EL as.as_pc prog <> AsmOp "CREATE" /\
  EL as.as_pc prog <> AsmOp "CREATE2" /\
  EL as.as_pc prog <> AsmOp "SELFDESTRUCT" ==>
  asm_frame_step_ok prog data es0 as es
Proof
  Cases_on `EL as.as_pc prog = AsmOp "GAS"`
  >- metis_tac[frame_gas_step] >>
  metis_tac[frame_plain_step]
QED
