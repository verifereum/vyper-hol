(* The EIP-6780 branch is selected by the executing account's creation flag. *)
Theory asmFrameSelfdestructStep
Ancestors
  asmFrameRel asmFrameLocalStep frameObsStep evmStepTransplant asmEvmStepStarve
  evmStepSim asmDataSuffixProps codegenRel asmSem asmWf symbolResolve
  callTrace frameOutcome vfmExecution vfmExecutionProp vfmOperation asmEncodeParse

Theorem frame_selfdestruct_singleton[local]:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "SELFDESTRUCT" /\
  (a.as_call_ctx.cc_created_in_tx =
   account_empty (lookup_account (FST (HD es.contexts)).msgParams.callee
                  es.originalAccounts)) /\
  es.contexts = (c,rb)::rest /\ a.as_stack = addr::stk /\
  asm_selfdestruct a = AsmHalt a1 ==>
  (?exc t. step (es with contexts := [(c,rb)]) = (INR (SOME exc),t) /\
           (exc = OutOfGas \/ exc = StackOverflow)) \/
  (?t. step (es with contexts := [(c,rb)]) = (INR NONE,t) /\
       LENGTH t.contexts = 1 /\
       (FST (HD t.contexts)).returnData = a1.as_returndata /\
       (FST (HD t.contexts)).logs = a1.as_logs /\
       t.rollback.accounts = a1.as_accounts /\
       t.rollback.toDelete = a1.as_pending_deletions /\
       t.rollback.tStorage = a1.as_transient)
Proof
  strip_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a es` by
    gvs[asm_frame_rel_def] >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a
      (es with contexts := [(c,rb)])` by
    metis_tac[frame_rel_singleton] >>
  `asm_encoding_wf prog /\
   (!j. j <= a.as_pc ==> ~is_data_inst (EL j prog))` by
    (gvs[asm_frame_prog_ok_def] >> metis_tac[is_data_inst_def]) >>
  `LENGTH (es with contexts := [(c,rb)]).contexts = 1` by simp[] >>
  drule_all starve_step_setup >> simp[] >> strip_tac >> gvs[] >>
  `op = SelfDestruct` by
    (irule opcode_wf_inj >>
     gvs[encode_inst_def, opcode_def, wf_opname_def,
         evm_opcode_byte_def, evm_opcode_table_def]) >>
  gvs[] >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def] >>
  asm_rewrite_tac[] >> simp[step_inst_def] >>
  simp[step_self_destruct_def, pop_stack_def, bind_def, ignore_bind_def,
       get_current_context_def, set_current_context_def, return_def,
       assert_def] >>
  simp[access_address_def, get_callee_def, set_return_data_def,
       get_accounts_def, bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def, LET_THM] >>
  `?d. es.msdomain = Collect d` by gvs[asm_frame_rel_def] >>
  simp[domain_check_def, bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def] >>
  simp[set_domain_def, bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def] >>
  qmatch_goalsub_abbrev_tac `consume_gas cost s` >>
  simp[consume_gas_def, bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def, Abbr `s`] >>
  Cases_on `cost + c.gasUsed <= c.msgParams.gasLimit`
  >- (simp[assert_def, bind_def, ignore_bind_def, return_def,
           get_current_context_def, set_current_context_def] >>
      `~c.msgParams.static` by gvs[asm_frame_rel_def] >>
      simp[assert_not_static_def, get_static_def, update_accounts_def,
           get_original_def, bind_def, ignore_bind_def, return_def,
           get_current_context_def, set_current_context_def, assert_def] >>
      Cases_on `account_empty (lookup_account c.msgParams.callee es.originalAccounts)` >>
      simp[bind_def, ignore_bind_def, return_def, update_accounts_def,
           add_to_delete_def, finish_def] >>
      simp[handle_step_def, handle_def, handle_create_def,
           get_output_to_def, get_return_data_def, bind_def, ignore_bind_def,
           get_current_context_def, return_def] >>
      Cases_on `c.msgParams.outputTo` >> gvs[] >>
      simp[reraise_def, handle_exception_def, get_num_contexts_def,
           bind_def, ignore_bind_def, return_def] >>
      gvs[asm_selfdestruct_def, asm_evm_rel_def]) >>
  simp[assert_def, bind_def, ignore_bind_def, fail_def] >>
  disj1_tac >>
  qmatch_goalsub_abbrev_tac `handle_step (SOME OutOfGas) s` >>
  `s.contexts = [(c with <|stack := stk; returnData := []|>,rb)]` by
    simp[Abbr `s`] >>
  drule starve_handle_resource >>
  disch_then (qspec_then `OutOfGas` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem asm_frame_selfdestruct_step_created:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ EL as.as_pc prog = AsmOp "SELFDESTRUCT" /\
  (as.as_call_ctx.cc_created_in_tx =
   account_empty (lookup_account (FST (HD es.contexts)).msgParams.callee
                  es.originalAccounts)) ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
