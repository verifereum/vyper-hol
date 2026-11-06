(* Creation consumes the frame's observed creation outcome, including the
   creator nonce update on failure and the created address on success. *)
Theory asmFrameCreateStep
Ancestors
  asmFrameRel asmFrameCallStep frameObsStep asmCallOracleProps asmDataSuffixProps
  codegenRel asmSem asmWf symbolResolve extCallOracle callTrace frameOutcome
  vfmExecution vfmExecutionProp frameCreationGuard

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
    p.msgParams = parent.msgParams /\ p.jumpDest = parent.jumpDest /\
    p.memory = parent.memory /\
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
    p.msgParams = parent.msgParams /\ p.jumpDest = parent.jumpDest /\
    p.memory = parent.memory /\
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

Theorem asm_create_initcode_length[local]:
  LENGTH (buffer_take off sz
    (buffer_extend (MAX (buffer_length mem)
      (if 0 < sz then 32 * word_size (off + sz) else 0) -
      buffer_length mem) mem)) = sz
Proof
  `buffer_take off sz
    (buffer_extend (MAX (buffer_length mem)
      (if 0 < sz then 32 * word_size (off + sz) else 0) -
      buffer_length mem) mem) = buffer_read off sz mem` by
    (irule asm_call_expanded_input >>
     qexistsl_tac [`off`,`0`,`0`,`sz`] >>
     simp[max_expansion_range_def] >>
     Cases_on `sz = 0` >> simp[]) >>
  simp[vfmBufferTheory.buffer_read_to_list]
QED

Theorem asm_create_success_prefix[local]:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (if two then 4 else 3) <= LENGTH c.stack /\
  step_create two s = (INL (),t) ==>
  ?u p gas abort collision sender address value code.
    w2n (EL 2 c.stack) <= 2 * max_code_size /\
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
  `w2n (EL 2 c.stack) <= 2 * max_code_size` by
    (Cases_on `two` >>
     fs[Abbr `expansion`, listTheory.EL_TAKE, asm_create_initcode_length]) >>
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
Theorem asm_frame_create_consume[local]:
  asm_evm_rel (prog ++ [AsmDataItem data]) a s /\
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME (case salt_opt of NONE => Create | SOME salt => Create2) /\
  a.as_stack = value::off::sz::
    (case salt_opt of NONE => stk | SOME salt => salt::stk) /\
  EL a.as_pc prog = AsmOp (case salt_opt of NONE => "CREATE" | SOME salt => "CREATE2") /\
  w2n sz <= 2 * max_code_size ==>
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL a.as_pc prog) a =
  asm_consume_create_outcome (request_of s) stk
    (a with as_memory := asm_call_memory (w2n off) (w2n sz) 0 0 a.as_memory)
Proof
  strip_tac >>
  `asm_create_request a value (w2n off) (w2n sz) salt_opt = request_of s` by
    (irule asm_create_request_observed >> simp[] >> metis_tac[]) >>
  Cases_on `salt_opt` >>
  gvs[asm_step_def, asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
      asm_step_bitwise_def, asm_step_memory_def, asm_step_control_def,
      asm_step_extcall_def, asm_exec_create_def, asm_exec_create2_def]
QED

Theorem asm_frame_create_effects_step_ok:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  EL a.as_pc prog = AsmOp (case salt_opt of NONE => "CREATE" | SOME salt => "CREATE2") /\
  a.as_stack = value::off::sz::
    (case salt_opt of NONE => stk | SOME salt => salt::stk) /\
  w2n sz <= 2 * max_code_size /\
  s.contexts = (c,rb)::rest /\ t.contexts = (ct,rb)::rest /\
  (a.as_call_ctx.cc_created_in_tx =
    account_empty (lookup_account c.msgParams.callee t.originalAccounts)) /\
  (~a.as_call_ctx.cc_created_in_tx ==> account_already_created
    (lookup_account c.msgParams.callee t.rollback.accounts)) /\
  run_call t = run_call s /\ wf_state t /\ t.txParams = s.txParams /\
  (?d. t.msdomain = Collect d) /\
  ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\ ct.pc = SUC c.pc /\
  ct.stack = result::stk /\ (result = 0w \/ result = w2w (address:address)) /\
  buffer_to_list ct.memory = asm_call_memory (w2n off) (w2n sz) 0 0 a.as_memory /\
  ct.logs = a.as_logs ++ added /\
  t.rollback.toDelete = deleted ++ a.as_pending_deletions /\
  a.as_outcomes = outcome_of (request_of s).cr_kind t (LENGTH a.as_logs)
    (LENGTH a.as_pending_deletions) :: MAP SND (call_trace t) /\
  gas_readings t = gas_readings s /\
  call_requests s = request_of s :: call_requests t ==>
  asm_frame_step_ok prog data es0 a s
Proof
  strip_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s` by fs[asm_frame_rel_def] >>
  `EL a.as_pc prog = AsmOp "CREATE" \/ EL a.as_pc prog = AsmOp "CREATE2"` by
    (Cases_on `salt_opt` >> gvs[]) >>
  `next_opcode c = SOME (case salt_opt of NONE => Create | SOME salt => Create2)` by
    (drule_at (Pat `asm_evm_rel _ _ _`) asm_frame_create_decode >> simp[] >>
     Cases_on `salt_opt` >> gvs[]) >>
  drule_all asm_frame_create_consume >> disch_tac >>
  `(request_of s).cr_kind <> MessageCall /\
   (request_of s).cr_kind <> DelegateMessageCall /\ ~(request_of s).cr_static` by
    (Cases_on `salt_opt` >> gvs[request_of_def]) >>
  qmatch_asmsub_abbrev_tac `asm_consume_create_outcome _ _ prepared` >>
  `asm_consume_create_outcome (request_of s) stk prepared =
   AsmOK (asm_next (prepared with <|
     as_stack := result::stk; as_outcomes := MAP SND (call_trace t);
     as_requests := prepared.as_requests ++ [request_of s];
     as_accounts := t.rollback.accounts; as_transient := t.rollback.tStorage;
     as_logs := ct.logs; as_pending_deletions := t.rollback.toDelete;
     as_returndata := ct.returnData |>))` by
    (irule asm_consume_create_observed >> simp[Abbr `prepared`] >> metis_tac[]) >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
   asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1` by
    (`a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
     drule asmEncodeParseTheory.asm_pc_to_offset_suc >>
     Cases_on `salt_opt` >>
     simp[arithmeticTheory.ADD1, rich_listTheory.EL_APPEND1, asm_inst_size_def]) >>
  pure_rewrite_tac[asm_frame_step_ok_def] >> disj2_tac >>
  asm_rewrite_tac[] >> simp[] >> qexists_tac `t` >> simp[] >>
  qpat_x_assum `asm_frame_rel _ _ _ _ _` mp_tac >>
  rewrite_tac[asm_frame_rel_def] >> strip_tac >> gvs[] >>
  simp[asm_frame_rel_def, Abbr `prepared`, asm_next_def] >>
  gvs[asm_evm_rel_def, asm_next_def]
QED

Theorem asm_create_step_success:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME (if two then Create2 else Create) /\
  step_create two s = (INL (),v) ==>
  step s = (INL (),v)
Proof
  strip_tac >>
  `FLOOKUP c.msgParams.parsed c.pc = SOME (if two then Create2 else Create)` by
    (qpat_x_assum `next_opcode c = _` mp_tac >>
     Cases_on `two` >> simp[next_opcode_def] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  simp_tac (srw_ss()) [step_def, get_current_context_def, handle_def,
    bind_def, ignore_bind_def, return_def] >>
  qpat_assum `s.contexts = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `FLOOKUP _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `two` >>
  gvs[step_inst_def, inc_pc_or_jump_def, is_call_def, bind_def,
      ignore_bind_def, return_def]
QED


Theorem asm_create_raw_size:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (if two then 4 else 3) <= LENGTH c.stack /\
  step_create two s = (INL (),t) ==>
  w2n (EL 2 c.stack) <= 2 * max_code_size
Proof
  strip_tac >> drule_all asm_create_success_prefix >> strip_tac >> simp[]
QED

Theorem asm_frame_create_same_depth_step_ok:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  EL a.as_pc prog = AsmOp (case salt_opt of NONE => "CREATE" | SOME salt => "CREATE2") /\
  a.as_stack = value::off::sz::
    (case salt_opt of NONE => stk | SOME salt => salt::stk) /\
  s.contexts = (c,rb)::rest /\
  step_create (IS_SOME salt_opt) s = (INL (),t) /\
  LENGTH t.contexts = LENGTH s.contexts ==>
  asm_frame_step_ok prog data es0 a s
Proof
  strip_tac >>
  `wf_state s /\ (?d. s.msdomain = Collect d) /\ ~c.msgParams.static /\
   asm_evm_rel (prog ++ [AsmDataItem data]) a s` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `c.stack = a.as_stack /\ buffer_to_list c.memory = a.as_memory /\
   c.logs = a.as_logs /\ s.rollback.toDelete = a.as_pending_deletions` by
    gvs[asm_evm_rel_def] >>
  `(if IS_SOME salt_opt then 4 else 3) <= LENGTH c.stack` by
    (Cases_on `salt_opt` >> gvs[]) >>
  `next_opcode c = SOME (if IS_SOME salt_opt then Create2 else Create)` by
    (drule_at (Pat `asm_evm_rel _ _ _`) asm_frame_create_decode >>
     Cases_on `salt_opt` >> gvs[]) >>
  `step s = (INL (),t)` by (irule asm_create_step_success >> metis_tac[]) >>
  `wf_state t /\ (?dt. t.msdomain = Collect dt) /\ t.txParams = s.txParams` by
    (rpt conj_tac
     >- (drule_all vfmRunCallTheory.step_preserves_wf_state >> simp[])
     >- (drule_at (Pat `step _ = _`) vfmDomainCollectionTheory.step_preserves_collect >> simp[]) >>
     qspec_then `s` mp_tac vfmTxParamsTheory.step_preserves_txParams >> simp[]) >>
  `observable_call c` by (Cases_on `salt_opt` >> gvs[observable_call_def]) >>
  drule_all asm_create_raw_same_depth >> strip_tac >>
  drule_all asm_create_raw_size >> disch_tac >>
  drule_at (Pat `step _ = _`) frame_obs_call_same_depth >> simp[] >> strip_tac >>
  `run_call t = run_call s` by (drule_all run_call_same_depth_step >> simp[]) >>
  `call_requests s = request_of s :: call_requests t` by
    (Cases_on `salt_opt` >>
     gvs[call_requests_def, computed_precompile_def, request_of_def]) >>
  `a.as_outcomes = MAP SND (call_trace s)` by fs[asm_frame_rel_def] >>
  `(a.as_call_ctx.cc_created_in_tx =
      account_empty (lookup_account c.msgParams.callee s.originalAccounts)) /\
    (~a.as_call_ctx.cc_created_in_tx ==> account_already_created
      (lookup_account c.msgParams.callee s.rollback.accounts))` by
    gvs[asm_frame_rel_def] >>
  `account_empty (lookup_account c.msgParams.callee t.originalAccounts) =
    account_empty (lookup_account c.msgParams.callee s.originalAccounts)` by
    (irule evmCreationGuardTheory.step_creation_original_empty >> metis_tac[]) >>
  `!addr. account_already_created (lookup_account addr s.rollback.accounts) ==>
      account_already_created (lookup_account addr t.rollback.accounts)` by
    (mp_tac (Q.INST [`d` |-> `LENGTH s.contexts`, `B` |-> `s.rollback`,
                    `s` |-> `s`, `t` |-> `t`, `x` |-> `()`]
       vfmRunCallTheory.step_continuing_collision_current) >> simp[]) >>
  drule_at_then (Pat `t.contexts = _`) irule asm_frame_create_effects_step_ok >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `salt_opt` >>
  Cases_on `salt_opt` >> gvs[]
QED

Theorem asm_frame_create_child_step_ok:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  EL a.as_pc prog = AsmOp (case salt_opt of NONE => "CREATE" | SOME salt => "CREATE2") /\
  a.as_stack = value::off::sz::
    (case salt_opt of NONE => stk | SOME salt => salt::stk) /\
  s.contexts = (c,rb)::rest /\
  step_create (IS_SOME salt_opt) s = (INL (),v) /\
  LENGTH v.contexts = SUC (LENGTH s.contexts) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  strip_tac >>
  `wf_state s /\ (?d. s.msdomain = Collect d) /\ ~c.msgParams.static /\
   asm_evm_rel (prog ++ [AsmDataItem data]) a s` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `c.stack = a.as_stack /\ buffer_to_list c.memory = a.as_memory /\
   c.logs = a.as_logs /\ s.rollback.toDelete = a.as_pending_deletions` by
    gvs[asm_evm_rel_def] >>
  `(if IS_SOME salt_opt then 4 else 3) <= LENGTH c.stack` by
    (Cases_on `salt_opt` >> gvs[]) >>
  `next_opcode c = SOME (if IS_SOME salt_opt then Create2 else Create)` by
    (drule_at (Pat `asm_evm_rel _ _ _`) asm_frame_create_decode >>
     Cases_on `salt_opt` >> gvs[]) >>
  `step s = (INL (),v)` by (irule asm_create_step_success >> metis_tac[]) >>
  `wf_state v /\ (?dv. v.msdomain = Collect dv) /\ v.txParams = s.txParams` by
    (rpt conj_tac
     >- (drule_all vfmRunCallTheory.step_preserves_wf_state >> simp[])
     >- (drule_at (Pat `step _ = _`) vfmDomainCollectionTheory.step_preserves_collect >> simp[]) >>
     qspec_then `s` mp_tac vfmTxParamsTheory.step_preserves_txParams >> simp[]) >>
  `observable_call c` by (Cases_on `salt_opt` >> gvs[observable_call_def]) >>
  drule_all asm_create_raw_child_entry >> strip_tac >>
  drule_all asm_create_raw_size >> disch_tac >>
  `2 <= LENGTH v.contexts` by simp[] >>
  drule_at (Pat `wf_state v`) asm_call_child_run_normal >> simp[] >> strip_tac >>
  `LENGTH t.contexts = SUC (LENGTH rest)` by gvs[] >>
  `t.txParams = s.txParams` by
    (drule asm_call_run_txParams >> simp[]) >>
  drule_at (Pat `run_call _ = _`) asm_create_run_code_continuation >>
  simp[] >> strip_tac >>
  `?deleted. t.rollback.toDelete = deleted ++ a.as_pending_deletions` by
    (drule_at (Pat `run_call v = _`) asm_call_run_pending_suffix_any_output >>
     simp[] >> metis_tac[]) >>
  drule_at (Pat `step _ = _`) frame_obs_call_enter >> simp[] >> strip_tac >>
  `run_call t = run_call s` by
    (drule_at (Pat `step _ = _`) run_call_enter_return >> simp[] >> metis_tac[]) >>
  `call_requests s = request_of s :: call_requests t` by
    (Cases_on `salt_opt` >>
     gvs[call_requests_def, computed_precompile_def, request_of_def]) >>
  `a.as_outcomes = MAP SND (call_trace s)` by fs[asm_frame_rel_def] >>
  `(a.as_call_ctx.cc_created_in_tx =
      account_empty (lookup_account c.msgParams.callee t.originalAccounts)) /\
    (~a.as_call_ctx.cc_created_in_tx ==> account_already_created
      (lookup_account c.msgParams.callee t.rollback.accounts))` by
    (mp_tac (Q.INST [`s` |-> `s`, `v` |-> `v`, `r` |-> `INL ()`,
       `t` |-> `t`, `self` |-> `c.msgParams.callee`,
       `created` |-> `a.as_call_ctx.cc_created_in_tx`]
       step_run_call_creation_guard) >> gvs[asm_frame_rel_def] >> metis_tac[]) >>
  drule_at_then (Pat `t.contexts = _`) irule asm_frame_create_effects_step_ok >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`address`, `salt_opt`] >>
  Cases_on `salt_opt` >> Cases_on `ex = NONE` >> gvs[]
QED

Theorem asm_frame_create_normal_step_ok:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  EL a.as_pc prog = AsmOp (case salt_opt of NONE => "CREATE" | SOME salt => "CREATE2") /\
  a.as_stack = value::off::sz::
    (case salt_opt of NONE => stk | SOME salt => salt::stk) /\
  s.contexts = (c,rb)::rest /\
  step_create (IS_SOME salt_opt) s = (INL (),v) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  strip_tac >>
  `wf_state s /\ (?d. s.msdomain = Collect d) /\ ~c.msgParams.static /\
   asm_evm_rel (prog ++ [AsmDataItem data]) a s` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `(if IS_SOME salt_opt then 4 else 3) <= LENGTH c.stack` by
    (gvs[asm_evm_rel_def] >> Cases_on `salt_opt` >> gvs[]) >>
  `LENGTH v.contexts = LENGTH s.contexts \/
   LENGTH v.contexts = SUC (LENGTH s.contexts)` by
    (drule_all asm_create_success_prefix >> strip_tac >>
     drule_at (Pat `_ = (INL (),v)`) asm_create_finish_view >>
     simp[] >> strip_tac >> gvs[])
  >- (drule_at_then (Pat `step_create _ _ = _`) irule asm_frame_create_same_depth_step_ok >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_at_then (Pat `step_create _ _ = _`) irule asm_frame_create_child_step_ok >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem asm_create_step_terminal:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME (if two then Create2 else Create) /\
  step_create two s = (INR e,u) ==>
  step s = handle_step e u
Proof
  strip_tac >>
  `FLOOKUP c.msgParams.parsed c.pc = SOME (if two then Create2 else Create)` by
    (qpat_x_assum `next_opcode c = _` mp_tac >>
     Cases_on `two` >> simp[next_opcode_def] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  simp_tac (srw_ss()) [step_def, get_current_context_def, handle_def,
    bind_def, ignore_bind_def, return_def] >>
  qpat_assum `s.contexts = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `FLOOKUP _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `two` >>
  gvs[step_inst_def, bind_def, ignore_bind_def]
QED

Theorem asm_frame_create_failure_starved:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  EL a.as_pc prog = AsmOp (case salt_opt of NONE => "CREATE" | SOME salt => "CREATE2") /\
  a.as_stack = value::off::sz::
    (case salt_opt of NONE => stk | SOME salt => salt::stk) /\
  s.contexts = (c,rb)::rest /\
  step_create (IS_SOME salt_opt) s = (INR e,u) ==>
  ?r t. run_call s = SOME (r,t) /\ frame_resource_starved es0 r t
Proof
  strip_tac >>
  `wf_state s /\ (?d. s.msdomain = Collect d) /\ ~c.msgParams.static /\
   asm_evm_rel (prog ++ [AsmDataItem data]) a s` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `(if IS_SOME salt_opt then 4 else 3) <= LENGTH c.stack` by
    (gvs[asm_evm_rel_def] >> Cases_on `salt_opt` >> gvs[]) >>
  `next_opcode c = SOME (if IS_SOME salt_opt then Create2 else Create)` by
    (drule_at (Pat `asm_evm_rel _ _ _`) asm_frame_create_decode >>
     Cases_on `salt_opt` >> gvs[]) >>
  drule_all asm_create_raw_failure >> strip_tac >> gvs[] >>
  `s.contexts <> []` by simp[] >>
  `LENGTH u.contexts = LENGTH s.contexts` by
    (drule_all vfmStepLengthTheory.step_create_inr_no_grow >> simp[]) >>
  `same_frame_rel s u` by
    (irule (INST_TYPE [alpha |-> ``:unit``]
       vfmStepLengthTheory.same_frame_or_grow_eq_length) >> simp[] >>
     qexistsl_tac [`step_create (IS_SOME salt_opt)`, `INR (SOME OutOfGas)`] >> simp[]) >>
  `EVERY (wf_context o FST) u.contexts` by
    (`EVERY (wf_context o FST) s.contexts` by fs[wf_state_def] >>
     mp_tac (Q.INST [`two` |-> `IS_SOME (salt_opt:bytes32 option)`]
       vfmDecreasesGasTheory.decreases_gas_cred_step_create) >>
     rewrite_tac[vfmDecreasesGasTheory.decreases_gas_cred_def] >>
     metis_tac[pairTheory.SND]) >>
  `?p. u.contexts = (p,rb)::rest /\ p.msgParams = c.msgParams /\
       u.txParams = s.txParams /\ p.gasUsed <= p.msgParams.gasLimit` by
    (gvs[vfmSameFrameTheory.same_frame_rel_def] >>
     Cases_on `u.contexts` >> gvs[] >> PairCases_on `h` >>
     gvs[wf_context_def]) >>
  `step s = handle_step (SOME OutOfGas) u` by
    (irule asm_create_step_terminal >> metis_tac[]) >>
  `!address. c.msgParams.outputTo <> Code address` by
    gvs[asm_evm_rel_def] >>
  `?r t. run_call s = SOME (r,t) /\ frame_resource_starved s r t` by
    (Cases_on `rest`
     >- (drule_all asm_handle_step_oog_singleton >> disch_tac >>
         `step s = (INR (SOME OutOfGas), u with contexts :=
           [(p with <|gasUsed := p.msgParams.gasLimit; returnData := []|>,rb)])` by
           metis_tac[] >>
         drule asm_run_call_stops_after_step >> simp[] >> strip_tac >>
         simp[frame_resource_starved_def, frame_outcome_def] >>
         qexistsl_tac [`OutOfGas`, `[]`, `[]`] >> simp[]) >>
     PairCases_on `h` >> rename1 `s.contexts = (c,rb)::(h0,h1)::saved` >>
     `?mr. c.msgParams.outputTo = Memory mr` by
       (Cases_on `c.msgParams.outputTo` >> gvs[] >>
        fs[wf_state_def, outputTo_consistent_stack_def]) >>
     `p.msgParams.outputTo = Memory mr` by simp[] >>
     `LENGTH h0.stack < stack_limit` by
       (gvs[wf_state_def, stack_room_ok_def]) >>
     drule_all asm_handle_step_memory >> disch_tac >>
     `OutOfGas <> Reverted` by simp[] >>
     drule_all asm_handle_exception_memory_exception >> disch_tac >>
     `step s = (INL (), u with <| contexts :=
       (h0 with <|pc := SUC h0.pc; stack := 0w::h0.stack; returnData := [];
         memory := buffer_write mr.offset [] h0.memory|>,h1)::saved; rollback := rb|>)` by
       simp[vfmExecutionTheory.vfm_abort_def] >>
     drule asm_run_call_stops_after_step >> simp[] >> strip_tac >>
     simp[frame_resource_starved_def, frame_outcome_def] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `asm_frame_rel _ _ _ _ _` mp_tac >>
  simp[asm_frame_rel_def] >> strip_tac >>
  drule_all frame_resource_starved_mid >> simp[]
QED

Theorem asm_frame_create_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CREATE" \/
   EL as.as_pc prog = AsmOp "CREATE2") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 4 disch_tac >>
  `?c rb rest. es.contexts = (c,rb)::rest` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  `!salt_opt value off sz stk.
     EL as.as_pc prog = AsmOp (case salt_opt of NONE => "CREATE" | SOME salt => "CREATE2") /\
     as.as_stack = value::off::sz::
       (case salt_opt of NONE => stk | SOME salt => salt::stk) ==>
     asm_frame_step_ok prog data es0 as es` by
    (rpt gen_tac >> strip_tac >>
     Cases_on `step_create (IS_SOME salt_opt) es` >>
     rename1 `step_create _ es = (res,mid)` >> Cases_on `res`
     >- (Cases_on `x` >>
         drule_at_then (Pat `step_create _ _ = _`) irule asm_frame_create_normal_step_ok >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     drule_at (Pat `step_create _ _ = _`) asm_frame_create_failure_starved >>
     simp[] >> strip_tac >>
     simp[asm_frame_step_ok_def] >> metis_tac[]) >>
  Cases_on `as.as_stack`
  >- gvs[asm_frame_step_ok_def, asm_step_def, asm_step_op_def,
      asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
      asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
      asm_exec_create_def, asm_exec_create2_def] >>
  Cases_on `t`
  >- gvs[asm_frame_step_ok_def, asm_step_def, asm_step_op_def,
      asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
      asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
      asm_exec_create_def, asm_exec_create2_def] >>
  Cases_on `t'`
  >- gvs[asm_frame_step_ok_def, asm_step_def, asm_step_op_def,
      asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
      asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
      asm_exec_create_def, asm_exec_create2_def] >>
  Cases_on `EL as.as_pc prog = AsmOp "CREATE"`
  >- (first_x_assum (qspec_then `NONE` irule) >> simp[] >> metis_tac[]) >>
  Cases_on `t`
  >- gvs[asm_frame_step_ok_def, asm_step_def, asm_step_op_def,
      asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
      asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
      asm_exec_create_def, asm_exec_create2_def] >>
  rename1 `as.as_stack = value::off::sz::salt::stk` >>
  first_x_assum (qspec_then `SOME salt` irule) >> simp[] >> metis_tac[]
QED
