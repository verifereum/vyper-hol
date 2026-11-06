(* Creation consumes the frame's observed creation outcome, including the
   creator nonce update on failure and the created address on success. *)
Theory asmFrameCreateStep
Ancestors
  asmFrameRel asmFrameCallStep frameObsStep asmCallOracleProps asmDataSuffixProps
  codegenRel asmSem asmWf symbolResolve extCallOracle callTrace frameOutcome
  vfmExecution vfmExecutionProp

(* Actual failure is a handler exception, not a zero returned address. *)
Theorem asm_create_failed_pop_effects:
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Code address /\
  ex <> NONE /\ handle_exception ex s = (INL (),t) ==>
  t.rollback = crb /\ (FST (HD t.contexts)).logs = parent.logs
Proof
  strip_tac >> Cases_on `ex` >- gvs[] >>
  Cases_on `x = Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
      get_gas_left_def, get_current_context_def, return_def,
      consume_gas_def, set_return_data_def, set_current_context_def,
      get_num_contexts_def, get_return_data_def, get_output_to_def,
      reraise_def, assert_def, fail_def, inc_pc_def, push_stack_def,
      pop_and_incorporate_context_def, pop_context_def,
      set_rollback_def, unuse_gas_def, AllCaseEqs()]
QED

Theorem asm_create_finalization_failure_effects:
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Code address /\
  handle_create initial s = (INR ex,u) /\ ex <> NONE /\
  handle_exception ex u = (INL (),t) ==>
  t.rollback = crb /\ (FST (HD t.contexts)).logs = parent.logs
Proof
  strip_tac >>
  drule vfmHandleStepTheory.handle_create_preserves_tl_and_snd_hd >>
  simp[] >> strip_tac >>
  Cases_on `u.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  irule asm_create_failed_pop_effects >>
  goal_assum $ drule_at Any >> simp[] >> metis_tac[]
QED

Theorem asm_create_abort_effects:
  s.contexts = (c,rb)::rest /\
  (abort_unuse gas s = (INL (),t) \/
   abort_create_exists sender s = (INL (),t)) ==>
  t.rollback.toDelete = s.rollback.toDelete /\
  (FST (HD t.contexts)).logs = c.logs
Proof
  strip_tac >>
  gvs[abort_unuse_def, abort_create_exists_def, unuse_gas_def,
      push_stack_def, inc_pc_def, update_accounts_def, get_rollback_def,
      get_current_context_def, set_current_context_def,
      bind_def, ignore_bind_def, return_def, assert_def, fail_def,
      AllCaseEqs()]
QED

Theorem asm_create_saved_effects:
  s.contexts = (c,rb)::rest /\
  proceed_create sender address value code gas s = (r,t) ==>
  (SND (HD t.contexts)).toDelete = s.rollback.toDelete /\
  (FST (HD (TL t.contexts))).logs = c.logs
Proof
  strip_tac >>
  qpat_x_assum `proceed_create _ _ _ _ _ _ = _` mp_tac >>
  simp[proceed_create_def, update_accounts_def, get_rollback_def,
       get_original_def, set_original_def, push_context_def,
       ignore_bind_def, bind_def, return_def, fail_def] >>
  strip_tac >> gvs[]
QED

Theorem asm_create_failed_observed_effects:
  (FST (HD t.contexts)).logs = logs /\
  t.rollback.toDelete = pending ==>
  (outcome_of kind t (LENGTH logs) (LENGTH pending)).co_logs = [] /\
  (outcome_of kind t (LENGTH logs) (LENGTH pending)).co_toDelete = []
Proof
  simp[outcome_of_def]
QED

Theorem asm_frame_create_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CREATE" \/
   EL as.as_pc prog = AsmOp "CREATE2") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
