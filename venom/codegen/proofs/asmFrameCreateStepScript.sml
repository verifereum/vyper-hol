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

Theorem asm_create_ready_finish_no_failure[local]:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  LENGTH c.stack < stack_limit /\ n <= c.gasUsed /\
  (if abort then abort_unuse n else do
     access_address address; ensure_storage_in_domain address;
     if b3 then abort_create_exists sender
     else proceed_create sender address value code n
   od) s = (INR e,t) ==> F
Proof
  strip_tac >> Cases_on `abort`
  >- (drule_all asm_abort_unuse_state >> gvs[]) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[access_address_def, ensure_storage_in_domain_def,
       domain_check_def, set_domain_def, bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `(if b3 then _ else _) v` >>
  `v.contexts = (c,rb)::rest` by simp[Abbr `v`] >>
  Cases_on `b3` >> simp[]
  >- fs[vfmConstantsTheory.stack_limit_def,
          abort_create_exists_def, update_accounts_def, get_rollback_def,
          push_stack_def, inc_pc_def, get_current_context_def,
          set_current_context_def, bind_def, ignore_bind_def,
          return_def, assert_def] >>
  strip_tac >>
  `v.contexts <> []` by simp[] >>
  drule_all vfmStepLengthTheory.proceed_create_returns_inl >> simp[]
QED

Theorem asm_create_charged_failure[local]:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ LENGTH c.stack < stack_limit /\
  (do consume_gas n; assert_not_static; set_return_data [];
      depth <- get_num_contexts;
      if b1 \/ b2 \/ depth > 1024 then abort_unuse n else do
        access_address address; ensure_storage_in_domain address;
        if b3 then abort_create_exists sender
        else proceed_create sender address value code n
      od
   od) s = (INR e,t) ==> e = SOME OutOfGas
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 4 disch_tac >>
  Cases_on `c.gasUsed + n <= c.msgParams.gasLimit` >>
  simp[consume_gas_def, assert_not_static_def, get_static_def,
       set_return_data_def, get_num_contexts_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `(if _ then _ else _) v` >>
  strip_tac >>
  `v.contexts = (c with <|gasUsed := c.gasUsed + n; returnData := []|>,rb)::rest /\
   v.msdomain = Collect d` by simp[Abbr `v`] >>
  `F` suffices_by simp[] >>
  irule (PURE_REWRITE_RULE[ignore_bind_def] asm_create_ready_finish_no_failure) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> fs[vfmConstantsTheory.stack_limit_def]
QED

Theorem asm_create_raw_failure:
  s.contexts = (c,rb)::rest /\ wf_state s /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (if two then 4 else 3) <= LENGTH c.stack /\
  step_create two s = (INR e,t) ==> e = SOME OutOfGas
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 5 disch_tac >>
  `LENGTH c.stack <= stack_limit` by gvs[wf_state_def, wf_context_def] >>
  simp[step_create_def, pop_stack_def, memory_expansion_info_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `consume_gas charge _` >>
  qmatch_goalsub_abbrev_tac `expand_memory expansion _` >>
  simp[Once consume_gas_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def,
       assert_def, return_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `if paid then _ else _` >>
  Cases_on `paid` >> simp[] >>
  simp[expand_memory_def, read_memory_def, get_callee_def, get_accounts_def,
       get_gas_left_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `if size_ok then _ else _` >>
  Cases_on `size_ok` >> simp[] >>
  qmatch_goalsub_abbrev_tac `consume_gas gas prepared` >>
  strip_tac >>
  drule_at (Pat `_ = (INR _,_)`)
    (SRULE[ignore_bind_def, bind_def] asm_create_charged_failure) >>
  simp[Abbr `prepared`] >>
  Cases_on `two` >> fs[vfmConstantsTheory.stack_limit_def]
QED

Theorem asm_create_success_prefix[local]:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (if two then 4 else 3) <= LENGTH c.stack /\
  step_create two s = (INL (),t) ==>
  ?u p gas abort collision sender address value code.
    u.contexts = (p,rb)::rest /\ u.msdomain = Collect d /\
    p.msgParams = c.msgParams /\ p.jumpDest = c.jumpDest /\ p.pc = c.pc /\
    p.stack = DROP (if two then 4 else 3) c.stack /\
    p.returnData = [] /\ p.logs = c.logs /\
    buffer_to_list p.memory = asm_call_memory (w2n (EL 1 c.stack))
      (w2n (EL 2 c.stack)) 0 0 (buffer_to_list c.memory) /\
    u.rollback.tStorage = s.rollback.tStorage /\
    u.rollback.toDelete = s.rollback.toDelete /\
    (if abort then abort_unuse gas else do
       access_address address; ensure_storage_in_domain address;
       if collision then abort_create_exists sender
       else proceed_create sender address value code gas
     od) u = (INL (),t)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 4 disch_tac >>
  simp[step_create_def, pop_stack_def, memory_expansion_info_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `consume_gas charge _` >>
  qmatch_goalsub_abbrev_tac `expand_memory expansion _` >>
  simp[Once consume_gas_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def,
       assert_def, return_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `if paid then _ else _` >>
  Cases_on `paid` >> simp[] >>
  simp[expand_memory_def, read_memory_def, get_callee_def, get_accounts_def,
       get_gas_left_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `if size_ok then _ else _` >>
  Cases_on `size_ok` >> simp[] >>
  qmatch_goalsub_abbrev_tac `consume_gas gas _` >>
  simp[consume_gas_def, assert_not_static_def, get_static_def,
       set_return_data_def, get_num_contexts_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `if paid2 then _ else _` >>
  Cases_on `paid2` >> simp[] >>
  strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `two` >> gvs[Abbr `expansion`, listTheory.EL_TAKE] >>
  irule asm_call_memory_buffer_extend >>
  simp[max_expansion_range_def] >>
  Cases_on `w2n (EL 2 c.stack) = 0` >> simp[]
QED

Theorem asm_create_finish_view[local]:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  (if abort then abort_unuse gas else do
     access_address address; ensure_storage_in_domain address;
     if collision then abort_create_exists sender
     else proceed_create sender address value code gas
   od) s = (INL (),t) ==>
  (?p. t.contexts = (p,rb)::rest /\ p.msgParams = c.msgParams /\
    p.jumpDest = c.jumpDest /\ p.pc = SUC c.pc /\
    p.stack = 0w::c.stack /\ p.returnData = c.returnData /\
    p.logs = c.logs /\ p.memory = c.memory /\
    t.rollback.tStorage = s.rollback.tStorage /\
    t.rollback.toDelete = s.rollback.toDelete) \/
  (?child crb. t.contexts = (child,crb)::(c,rb)::rest /\
    child.msgParams.outputTo = Code address /\ child.logs = [] /\
    crb.toDelete = s.rollback.toDelete /\
    crb.tStorage = s.rollback.tStorage /\
    t.rollback.toDelete = s.rollback.toDelete)
Proof
  strip_tac >> Cases_on `abort`
  >- (gvs[abort_unuse_def, unuse_gas_def, push_stack_def, inc_pc_def,
          get_current_context_def, set_current_context_def, bind_def,
          ignore_bind_def, return_def, assert_def, fail_def, AllCaseEqs()] >>
      simp[]) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[access_address_def, ensure_storage_in_domain_def,
       domain_check_def, set_domain_def, bind_def, ignore_bind_def, return_def] >>
  Cases_on `collision` >>
  simp[abort_create_exists_def, proceed_create_def, update_accounts_def,
       get_rollback_def, get_original_def, set_original_def, push_context_def,
       push_stack_def, inc_pc_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def, return_def,
       assert_def, fail_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> simp[vfmContextTheory.initial_context_def, vfmContextTheory.initial_msg_params_def]
QED

Theorem asm_create_raw_same_depth:
  s.contexts = (c,rb)::rest /\ wf_state s /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (if two then 4 else 3) <= LENGTH c.stack /\
  step_create two s = (INL (),t) /\
  LENGTH t.contexts = LENGTH s.contexts ==>
  ?p. t.contexts = (p,rb)::rest /\ p.msgParams = c.msgParams /\
    p.jumpDest = c.jumpDest /\ p.pc = SUC c.pc /\
    p.stack = 0w :: DROP (if two then 4 else 3) c.stack /\
    p.returnData = [] /\ p.logs = c.logs /\
    buffer_to_list p.memory = asm_call_memory (w2n (EL 1 c.stack))
      (w2n (EL 2 c.stack)) 0 0 (buffer_to_list c.memory) /\
    t.rollback.tStorage = s.rollback.tStorage /\
    t.rollback.toDelete = s.rollback.toDelete
Proof
  strip_tac >> drule_all asm_create_success_prefix >> strip_tac >>
  drule_at (Pat `_ = (INL (),t)`) asm_create_finish_view >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem asm_create_raw_child_entry:
  s.contexts = (c,rb)::rest /\ wf_state s /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (if two then 4 else 3) <= LENGTH c.stack /\
  step_create two s = (INL (),t) /\
  LENGTH t.contexts = SUC (LENGTH s.contexts) ==>
  ?child crb parent address.
    t.contexts = (child,crb)::(parent,rb)::rest /\
    parent.msgParams = c.msgParams /\ parent.jumpDest = c.jumpDest /\
    parent.pc = c.pc /\ parent.stack = DROP (if two then 4 else 3) c.stack /\
    parent.returnData = [] /\ parent.logs = c.logs /\
    buffer_to_list parent.memory = asm_call_memory (w2n (EL 1 c.stack))
      (w2n (EL 2 c.stack)) 0 0 (buffer_to_list c.memory) /\
    child.msgParams.outputTo = Code address /\ child.logs = [] /\
    crb.toDelete = s.rollback.toDelete /\
    crb.tStorage = s.rollback.tStorage /\
    t.rollback.toDelete = s.rollback.toDelete
Proof
  strip_tac >> drule_all asm_create_success_prefix >> strip_tac >>
  drule_at (Pat `_ = (INL (),t)`) asm_create_finish_view >>
  simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED
Theorem asm_create_code_pop_jumpDest:
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Code address /\
  handle_exception ex s = (INL (),t) ==>
  (FST (HD t.contexts)).jumpDest = parent.jumpDest
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

Theorem asm_create_run_code_jumpDest:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Code address /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  (FST (HD t.contexts)).jumpDest = parent.jumpDest
Proof
  strip_tac >>
  drule_at (Pat `run_call _ = _`) asm_create_run_final_view >>
  simp[] >> strip_tac >>
  irule asm_create_code_pop_jumpDest >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
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
