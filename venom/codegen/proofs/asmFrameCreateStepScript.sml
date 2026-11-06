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

Theorem asm_frame_create_decode:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CREATE" \/ EL a.as_pc prog = AsmOp "CREATE2") ==>
  next_opcode (FST (HD es.contexts)) =
    SOME (if EL a.as_pc prog = AsmOp "CREATE" then Create else Create2)
Proof
  strip_tac >> irule asm_frame_opcode_decode >>
  simp[vfmOperationTheory.wf_opname_def] >>
  qexistsl_tac [`a`, `data`, `prog`] >>
  gvs[is_data_inst_def, encode_inst_def, evm_opcode_byte_def,
      evm_opcode_table_def, vfmOperationTheory.wf_opname_def,
      vfmOperationTheory.opcode_def]
QED

Theorem asm_frame_create_observable:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\
  ((EL a.as_pc prog = AsmOp "CREATE" /\ 3 <= LENGTH a.as_stack) \/
   (EL a.as_pc prog = AsmOp "CREATE2" /\ 4 <= LENGTH a.as_stack)) ==>
  observable_call (FST (HD es.contexts))
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) =
     SOME (if EL a.as_pc prog = AsmOp "CREATE" then Create else Create2)` by
    (irule asm_frame_create_decode >> metis_tac[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def, observable_call_def]
QED

Theorem asm_create_request_observed:
  asm_evm_rel prog a es /\
  next_opcode (FST (HD es.contexts)) =
    SOME (case salt_opt of NONE => Create | SOME salt => Create2) /\
  a.as_stack = value::off::sz::
    (case salt_opt of NONE => stk | SOME salt => salt::stk) ==>
  asm_create_request a value (w2n off) (w2n sz) salt_opt = request_of es
Proof
  strip_tac >> Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def] >>
  Cases_on `salt_opt` >>
  gvs[asm_create_request_def, request_of_def, GSYM asm_call_input_buffer,
      regularMemorySimTheory.expanded_slice_padded_range]
QED

Theorem asm_create_observed_adoption:
  rq.cr_kind <> MessageCall /\ rq.cr_kind <> DelegateMessageCall /\
  ~rq.cr_static /\ t.contexts = (c,rb)::rest /\
  c.logs = logs ++ added /\ t.rollback.toDelete = deleted ++ pending ==>
  adopt_outcome rq
    (outcome_of rq.cr_kind t (LENGTH logs) (LENGTH pending))
    (accounts,ts,logs) =
    (t.rollback.accounts,t.rollback.tStorage,c.logs) /\
  adopt_outcome_deletions rq
    (outcome_of rq.cr_kind t (LENGTH logs) (LENGTH pending)) pending =
    t.rollback.toDelete
Proof
  simp[adopt_outcome_def, adopt_outcome_deletions_def, outcome_of_def,
       rich_listTheory.DROP_APPEND, rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem asm_create_observed_address:
  kind <> MessageCall /\ kind <> DelegateMessageCall /\
  HD (FST (HD t.contexts)).stack = result /\
  (result = 0w \/ result = w2w (address:address)) ==>
  (if (outcome_of kind t n m).co_success
   then w2w (outcome_of kind t n m).co_created else 0w : bytes32) = result
Proof
  strip_tac >> gvs[outcome_of_def] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem asm_consume_create_observed:
  rq.cr_kind <> MessageCall /\ rq.cr_kind <> DelegateMessageCall /\
  ~rq.cr_static /\ t.contexts = (c,rb)::rest /\
  a.as_outcomes =
    outcome_of rq.cr_kind t (LENGTH a.as_logs)
      (LENGTH a.as_pending_deletions) :: outcomes /\
  c.logs = a.as_logs ++ added /\
  t.rollback.toDelete = deleted ++ a.as_pending_deletions /\
  c.stack = result::stk /\
  (result = 0w \/ result = w2w (address:address)) ==>
  asm_consume_create_outcome rq stk a =
    AsmOK (asm_next (a with <|
      as_stack := result::stk; as_outcomes := outcomes;
      as_requests := a.as_requests ++ [rq];
      as_accounts := t.rollback.accounts; as_transient := t.rollback.tStorage;
      as_logs := c.logs; as_pending_deletions := t.rollback.toDelete;
      as_returndata := c.returnData |>))
Proof
  strip_tac >>
  `adopt_outcome rq
     (outcome_of rq.cr_kind t (LENGTH a.as_logs)
       (LENGTH a.as_pending_deletions))
     (a.as_accounts,a.as_transient,a.as_logs) =
     (t.rollback.accounts,t.rollback.tStorage,c.logs) /\
   adopt_outcome_deletions rq
     (outcome_of rq.cr_kind t (LENGTH a.as_logs)
       (LENGTH a.as_pending_deletions)) a.as_pending_deletions =
     t.rollback.toDelete` by
    (irule asm_create_observed_adoption >> metis_tac[]) >>
  `((if (outcome_of rq.cr_kind t (LENGTH a.as_logs)
      (LENGTH a.as_pending_deletions)).co_success then
      w2w (outcome_of rq.cr_kind t (LENGTH a.as_logs)
        (LENGTH a.as_pending_deletions)).co_created else 0w):bytes32) = result` by
    (irule asm_create_observed_address >> simp[] >> metis_tac[]) >>
  simp[asm_consume_create_outcome_def, take_outcome_create, outcome_of_fields]
QED

Theorem asm_create_code_pop_selectors:
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Code address /\
  handle_exception ex s = (INL (),t) ==>
  ?p. t.contexts = (p,prb)::rest /\
    p.msgParams = parent.msgParams /\ p.memory = parent.memory /\
    p.pc = SUC parent.pc /\
    p.stack = (if ex = NONE then w2w address else 0w)::parent.stack /\
    p.returnData = (if ex = SOME Reverted then child.returnData else []) /\
    p.logs = parent.logs ++ (if ex = NONE then child.logs else []) /\
    t.rollback = (if ex = NONE then s.rollback else crb)
Proof
  strip_tac >> Cases_on `ex` >> Cases_on `x = Reverted` >>
  gvs[handle_exception_def, bind_def, ignore_bind_def,
      get_gas_left_def, get_current_context_def, return_def,
      consume_gas_def, set_return_data_def, set_current_context_def,
      get_num_contexts_def, get_return_data_def, get_output_to_def,
      reraise_def, assert_def, fail_def, inc_pc_def, push_stack_def,
      pop_and_incorporate_context_def, pop_context_def,
      set_rollback_def, unuse_gas_def, push_logs_def, update_gas_refund_def,
      AllCaseEqs()]
QED

(* This view includes exceptions raised while depositing returned code. *)
Theorem asm_create_run_final_view:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  ?ex u c. u.contexts = (c,crb)::(parent,prb)::rest /\
    c.msgParams = child.msgParams /\
    handle_exception ex u = (INL (),t)
Proof
  strip_tac >>
  drule_at (Pat `run_call _ = _`) asm_call_run_last_snapshot >>
  simp[] >> strip_tac >>
  `mid.contexts <> [] /\ LENGTH t.contexts < LENGTH mid.contexts` by simp[] >>
  drule_at (Pat `step _ = _`) asm_call_step_drop_raw_view >>
  simp[] >> strip_tac >>
  `~vfm_abort ex` by
    (drule_at (Pat `step_inner _ = _`) asm_call_step_inner_noabort >> simp[]) >>
  qpat_x_assum `same_frame_rel _ _` mp_tac >>
  simp[vfmSameFrameTheory.same_frame_rel_def] >> strip_tac >>
  `u.contexts <> []` by (Cases_on `u.contexts` >> gvs[]) >>
  `?e' s'. handle_create ex u = ((INR e',s') : unit execution_result)` by metis_tac[handle_create_INR] >>
  `handle_exception e' s' = (INL (),t)` by
    (qpat_x_assum `handle_step ex u = _` mp_tac >>
     asm_rewrite_tac[handle_step_def, handle_def] >>
     simp[] >>
     qpat_x_assum `handle_create ex u = _` (fn th => simp[th])) >>
  drule vfmHandleStepTheory.handle_create_preserves_tl_and_snd_hd >>
  simp[] >> strip_tac >>
  Cases_on `u.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  Cases_on `s'.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  metis_tac[]
QED

Theorem asm_create_run_code_continuation:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Code address /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  ?ex u c p. u.contexts = (c,crb)::(parent,prb)::rest /\
    c.msgParams = child.msgParams /\ handle_exception ex u = (INL (),t) /\
    t.contexts = (p,prb)::rest /\
    p.msgParams = parent.msgParams /\ p.memory = parent.memory /\
    p.pc = SUC parent.pc /\
    p.stack = (if ex = NONE then w2w address else 0w)::parent.stack /\
    p.returnData = (if ex = SOME Reverted then c.returnData else []) /\
    p.logs = parent.logs ++ (if ex = NONE then c.logs else []) /\
    (ex <> NONE ==> t.rollback = crb)
Proof
  strip_tac >>
  drule_at (Pat `run_call _ = _`) asm_create_run_final_view >>
  simp[] >> strip_tac >>
  `c.msgParams.outputTo = Code address` by simp[] >>
  drule_at (Pat `handle_exception _ _ = _`) asm_create_code_pop_selectors >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ex`,`u`,`c`,`p`] >> simp[]
QED

(* The frame relation excludes creation-initcode as the observed frame. *)
Theorem asm_create_frame_output_boundary:
  asm_frame_rel prog data es0 a es ==>
  ?c rb rest. es0.contexts = (c,rb)::rest /\
    (!address. c.msgParams.outputTo <> Code address)
Proof
  rw[asm_frame_rel_def, asm_evm_rel_def] >> gvs[] >> metis_tac[]
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
