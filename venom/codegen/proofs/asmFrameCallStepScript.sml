(*
 * CALL and STATICCALL against the frame's run.  The EVM either takes the
 * call at the frame's depth (precompiles, calls that fail before a
 * child starts) or runs a child frame back to this one; either way the
 * frame's call trace records one request and its outcome, which is the
 * outcome the assembly takes from as_outcomes.
 *
 * TOP-LEVEL:
 *   asm_frame_call_step
 *)

Theory asmFrameCallStep
Ancestors
  asmFrameRel frameObsStep evmStepSim asmCallOracleProps asmDataSuffixProps
  codegenRel asmSem asmWf symbolResolve extCallOracle callTrace frameOutcome
  vfmExecution vfmExecutionProp vfmRunCall vfmRunWithinFrame vfmContextLength vfmDecreasesGas
  vfmPreserves vfmAccountDeletion vfmStaticCalls vfmAccountFrame vfmStepLength vfmDomainCollection asmEncodeParse rich_list vfmOperation regularMemorySim vfmBuffer vfmTypes list spillSim
Libs
  wordsLib

Theorem asm_precompile_sha256_success:
  s.contexts = (c,rb)::rest /\
  precompile_sha2_256 s = (INR NONE,t) ==>
  precompile_result 2w (buffer_to_list c.msgParams.data) =
    SOME (SOME (FST (HD t.contexts)).returnData) /\
  t.rollback = s.rollback /\
  (FST (HD t.contexts)).logs = c.logs
Proof
  strip_tac >>
  qhdtm_x_assum `precompile_sha2_256` mp_tac >>
  simp[precompile_sha2_256_def, get_call_data_def, consume_gas_def,
       set_return_data_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def,
       finish_def] >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
QED

Theorem asm_precompile_ecrecover_success:
  s.contexts = (c,rb)::rest /\
  c.returnData = [] /\ precompile_ecrecover s = (INR NONE,t) ==>
  precompile_result 1w (buffer_to_list c.msgParams.data) =
    SOME (SOME (FST (HD t.contexts)).returnData) /\
  t.rollback = s.rollback /\
  (FST (HD t.contexts)).logs = c.logs
Proof
  strip_tac >>
  qhdtm_x_assum `precompile_ecrecover` mp_tac >>
  simp[precompile_ecrecover_def, get_call_data_def, consume_gas_def,
       set_return_data_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def,
       finish_def, precompile_result_def] >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  BasicProvers.FULL_CASE_TAC >>
  gvs[bind_def, ignore_bind_def, return_def, finish_def, fail_def,
      get_current_context_def, set_current_context_def, AllCaseEqs()]
QED

Theorem asm_precompile_ecadd_success:
  s.contexts = (c,rb)::rest /\
  precompile_ecadd s = (INR NONE,t) ==>
  precompile_result 6w (buffer_to_list c.msgParams.data) =
    SOME (SOME (FST (HD t.contexts)).returnData) /\
  t.rollback = s.rollback /\
  (FST (HD t.contexts)).logs = c.logs
Proof
  strip_tac >>
  qhdtm_x_assum `precompile_ecadd` mp_tac >>
  simp[precompile_ecadd_def, get_call_data_def, consume_gas_def,
       set_return_data_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def,
       finish_def, precompile_result_ecadd] >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  BasicProvers.FULL_CASE_TAC >>
  gvs[bind_def, ignore_bind_def, return_def, finish_def, fail_def] >>
  PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, return_def, finish_def,
      get_current_context_def, set_current_context_def]
QED

Theorem asm_precompile_ecmul_success:
  s.contexts = (c,rb)::rest /\
  precompile_ecmul s = (INR NONE,t) ==>
  precompile_result 7w (buffer_to_list c.msgParams.data) =
    SOME (SOME (FST (HD t.contexts)).returnData) /\
  t.rollback = s.rollback /\
  (FST (HD t.contexts)).logs = c.logs
Proof
  strip_tac >>
  qhdtm_x_assum `precompile_ecmul` mp_tac >>
  simp[precompile_ecmul_def, get_call_data_def, consume_gas_def,
       set_return_data_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def,
       finish_def, precompile_result_ecmul] >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  BasicProvers.FULL_CASE_TAC >>
  gvs[bind_def, ignore_bind_def, return_def, finish_def, fail_def] >>
  PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, return_def, finish_def,
      get_current_context_def, set_current_context_def]
QED

Theorem asm_computed_precompile_success:
  s.contexts = (c,rb)::rest /\ c.returnData = [] /\
  (address = 1w \/ address = 2w \/ address = 6w \/ address = 7w) /\
  dispatch_precompiles address s = (INR NONE,t) ==>
  precompile_result address (buffer_to_list c.msgParams.data) =
    SOME (SOME (FST (HD t.contexts)).returnData) /\
  t.rollback = s.rollback /\
  (FST (HD t.contexts)).logs = c.logs
Proof
    `dimindex (:160) = 160` by simp[] >>
  strip_tac >> gvs[dispatch_precompiles_def, wordsTheory.dimword_def]
  >- (drule_all asm_precompile_ecrecover_success >> simp[])
  >- (drule_all asm_precompile_sha256_success >> simp[])
  >- (drule_all asm_precompile_ecadd_success >> simp[])
  >> drule_all asm_precompile_ecmul_success >> simp[]
QED

Theorem asm_call_nested_handler_inl:
  wf_state s /\ 2 <= LENGTH s.contexts /\
  step_inner s = (INR e,t) /\ ~vfm_abort e /\
  handle_step e t = (q,u) ==> ISL q
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  `EVERY (wf_context o FST) t.contexts` by
    (mp_tac decreases_gas_cred_step_inner >>
     rewrite_tac[decreases_gas_cred_def] >>
     disch_then (qspec_then `s` mp_tac) >> simp[] >>
     gvs[wf_state_def]) >>
  `stack_room_ok t /\ gas_stack_ok t` by
    (irule step_inner_preserves_stack_room_gas_ok >>
     goal_assum $ drule_at Any >> simp[]) >>
  `LENGTH t.contexts >= LENGTH s.contexts` by
    (mp_tac vfmStepLengthTheory.same_frame_or_grow_step_inner_named >>
     metis_tac[vfmStepLengthTheory.same_frame_or_grow_length]) >>
  irule handle_step_not_abort_returns_inl >>
  qexistsl_tac [`e`, `t`, `u`] >> simp[]
QED

Theorem asm_call_child_parent_msgParams:
  step_call op s = (q,e) /\ s.contexts <> [] /\
  LENGTH s.contexts < LENGTH e.contexts /\
  wf_state e /\ run_call e = SOME (INL (),t) ==>
  (FST (HD t.contexts)).msgParams =
  (FST (HD s.contexts)).msgParams
Proof
  strip_tac >> drule step_call_push_structure >> simp[] >> strip_tac >>
  `2 <= LENGTH e.contexts` by
    (Cases_on `s.contexts` >> gvs[] >> decide_tac) >>
  drule_all run_call_parent_msgParams >> strip_tac >>
  Cases_on `e.contexts` >> gvs[] >>
  rename1 `e.contexts = child :: parents` >>
  Cases_on `parents` >> gvs[]
QED

Theorem asm_call_child_run_classify:
  wf_state child /\ 2 <= LENGTH child.contexts ==>
  ?r t. run_call child = SOME (r,t) /\ wf_state t /\
    ((r = INL () /\ LENGTH t.contexts + 1 = LENGTH child.contexts) \/
     (?e. r = INR e /\ vfm_abort e))
Proof
  strip_tac >>
  Cases_on `run_call_tr (LENGTH child.contexts) (step child)` >>
  rename1 `run_call_tr _ _ = (result,finished)` >>
  `run_call child = SOME (result,finished)` by simp[run_call_eq_tr] >>
  qexistsl_tac [`result`, `finished`] >> simp[] >>
  conj_tac >- metis_tac[run_call_preserves_wf_state] >>
  Cases_on `result`
  >- (Cases_on `x` >> simp[] >> metis_tac[run_call_inl_length]) >>
  simp[] >> irule run_call_inr_requires_abort_ge2 >>
  qexistsl_tac [`child`, `finished`] >> simp[]
QED

Theorem asm_handle_exception_nested_normal:
  wf_state s /\ 2 <= LENGTH s.contexts /\
  handle_exception exc s = (r,t) ==> r = INL ()
Proof
  strip_tac >>
  `ISL r` by
    (irule vfmHandleStepTheory.handle_exception_ge_2_inl >>
     qexistsl_tac [`exc`, `s`, `t`] >> gvs[wf_state_def]) >>
  Cases_on `r` >> gvs[] >> Cases_on `x` >> simp[]
QED

Theorem asm_handle_exception_memory_no_abort:
  wf_state s /\ s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\ ~vfm_abort exc /\
  handle_exception exc s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e)
Proof
  strip_tac >>
  `2 <= LENGTH s.contexts` by simp[] >>
  drule_all asm_handle_exception_nested_normal >> simp[]
QED

Theorem asm_frame_call_decode:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") ==>
  next_opcode (FST (HD es.contexts)) =
    SOME (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall)
Proof
  strip_tac >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    gvs[asm_frame_prog_ok_def, data_suffix_encoding_wf] >>
  `a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `!j. j <= a.as_pc ==> ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (rpt strip_tac >> `j < LENGTH prog` by decide_tac >>
     gvs[EL_APPEND1, asm_frame_prog_ok_def] >>
     metis_tac[is_data_inst_def]) >>
  drule_all assemble_parse_exact >> strip_tac >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc <
     LENGTH (assemble (prog ++ [AsmDataItem data]))` by
    (irule offset_in_bounds >> simp[]) >>
  gvs[EL_APPEND1, encode_inst_def, evm_opcode_byte_def, evm_opcode_table_def] >>
  `op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall)` by
    (irule opcode_wf_inj >> simp[wf_opname_def, opcode_def]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def, next_opcode_def]
QED

Theorem asm_frame_call_observable:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\
  ((EL a.as_pc prog = AsmOp "CALL" /\ 7 <= LENGTH a.as_stack) \/
   (EL a.as_pc prog = AsmOp "STATICCALL" /\ 6 <= LENGTH a.as_stack)) ==>
  observable_call (FST (HD es.contexts))
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) =
     SOME (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall)` by
    (irule asm_frame_call_decode >> metis_tac[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def, observable_call_def]
QED

Theorem asm_call_input_buffer:
  TAKE sz (DROP off (asm_expand_memory (off + sz) (buffer_to_list mem))) =
  buffer_read off sz mem
Proof
  simp[expanded_slice_padded_range, buffer_read_to_list,
       take_pad_0_def, PAD_RIGHT, GSYM REPLICATE_GENLIST] >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ] >>
  rpt strip_tac >>
  simp[EL_GENLIST, read_byte_def, EL_APPEND_EQN, EL_TAKE, EL_DROP,
       EL_REPLICATE] >>
  IF_CASES_TAC >> gvs[LENGTH_TAKE_EQ, EL_DROP, EL_REPLICATE] >>
  rpt (IF_CASES_TAC >> gvs[EL_REPLICATE])
QED

Theorem asm_frame_call_request:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "CALL" /\
  a.as_stack = gas :: addr :: value :: ao :: sz :: ro :: rs :: stk ==>
  asm_call_request a addr value (w2n ao) (w2n sz) F = request_of es
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) = SOME Call` by
    (drule asm_frame_call_decode >>
     disch_then (qspecl_then [`es`, `data`, `a`] mp_tac) >> simp[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def] >>
  simp[request_of_def, asm_call_request_def, GSYM asm_call_input_buffer,
       expanded_slice_padded_range]
QED

Theorem asm_frame_staticcall_request:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp "STATICCALL" /\
  a.as_stack = gas :: addr :: ao :: sz :: ro :: rs :: stk ==>
  asm_call_request a addr 0w (w2n ao) (w2n sz) T = request_of es
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) = SOME StaticCall` by
    (drule asm_frame_call_decode >>
     disch_then (qspecl_then [`es`, `data`, `a`] mp_tac) >> simp[]) >>
  Cases_on `es.contexts` >> gvs[asm_evm_rel_def] >>
  PairCases_on `h` >> gvs[asm_evm_rel_def] >>
  simp[request_of_def, asm_call_request_def, GSYM asm_call_input_buffer,
       expanded_slice_padded_range]
QED

Theorem asm_call_underflow:
  LENGTH a.as_stack < 7 ==>
  asm_step lo otp (AsmOp "CALL") a = AsmError "call: stack underflow"
Proof
  simp[asm_step_call_staticcall_gas] >>
  Cases_on `a.as_stack` >> simp[asm_exec_call_def] >>
  Cases_on `t` >> simp[asm_exec_call_def] >>
  Cases_on `t'` >> simp[asm_exec_call_def] >>
  Cases_on `t` >> simp[asm_exec_call_def] >>
  Cases_on `t'` >> simp[asm_exec_call_def] >>
  Cases_on `t` >> simp[asm_exec_call_def] >>
  Cases_on `t'` >> simp[asm_exec_call_def]
QED

Theorem asm_staticcall_underflow:
  LENGTH a.as_stack < 6 ==>
  asm_step lo otp (AsmOp "STATICCALL") a = AsmError "staticcall: stack underflow"
Proof
  simp[asm_step_call_staticcall_gas] >>
  Cases_on `a.as_stack` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t'` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t'` >> simp[asm_exec_staticcall_def] >>
  Cases_on `t` >> simp[asm_exec_staticcall_def]
QED

Theorem asm_abort_call_value_state:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack < stack_limit /\
  stipend <= c.gasUsed ==>
  abort_call_value stipend s =
    (INL (), s with contexts :=
      (c with <| stack := 0w :: c.stack; returnData := [];
                 gasUsed := c.gasUsed - stipend; pc updated_by SUC |>, rb)::rest)
Proof
  simp[abort_call_value_def, push_stack_def, set_return_data_def,
       unuse_gas_def, inc_pc_def, bind_def, ignore_bind_def,
       get_current_context_def, set_current_context_def,
       assert_def, return_def, b2w_def]
QED

Theorem asm_abort_unuse_state:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack < stack_limit /\
  stipend <= c.gasUsed ==>
  abort_unuse stipend s =
    (INL (), s with contexts :=
      (c with <| stack := 0w :: c.stack;
                 gasUsed := c.gasUsed - stipend; pc updated_by SUC |>, rb)::rest)
Proof
  simp[abort_unuse_def, push_stack_def, unuse_gas_def, inc_pc_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, assert_def, return_def, b2w_def]
QED

Definition asm_call_prepare_def:
  asm_call_prepare op = do
    valueOffset <<- if call_has_value op then 1 else 0;
    args <- pop_stack (6 + valueOffset);
    gas <<- w2n $ EL 0 args;
    address <<- w2w $ EL 1 args;
    value <<- if 0 < valueOffset then w2n $ EL 2 args else 0;
    argsOffset <<- w2n $ EL (2 + valueOffset) args;
    argsSize <<- w2n $ EL (3 + valueOffset) args;
    retOffset <<- w2n $ EL (4 + valueOffset) args;
    retSize <<- w2n $ EL (5 + valueOffset) args;
    (offset, size) <<- max_expansion_range
      (argsOffset, argsSize) (retOffset, retSize);
    mx <- memory_expansion_info offset size;
    accessCost <- access_address address;
    positiveValueCost <<- if 0 < value then call_value_cost else 0;
    accounts <- get_accounts;
    toAccount <<- lookup_account address accounts;
    (code, delegateCost) <- case get_delegate toAccount.code of
               NONE => return (toAccount.code, 0)
             | SOME delegate => do
                 cost <- access_address delegate;
                 return ((lookup_account delegate accounts).code, cost)
               od;
    createCost <<- if op = Call /\ 0 < value /\ account_empty toAccount
                   then new_account_cost else 0;
    gasLeft <- get_gas_left;
    (dynamicGas, stipend) <<- call_gas value gas gasLeft mx.cost $
                                accessCost + positiveValueCost + createCost + delegateCost;
    consume_gas $ static_gas op + dynamicGas + mx.cost;
    if op = Call /\ 0 < value then assert_not_static else return ();
    expand_memory mx.expand_by;
    sender <- get_callee;
    return (sender,address,value,argsOffset,argsSize,code,stipend,retOffset,retSize,accounts)
  od
End

(* Preparation depends only on the operand layout and charge, not on
   whether the child inherits the message identities. *)
Theorem asm_call_prepare_delegate:
  asm_call_prepare DelegateCall = asm_call_prepare StaticCall
Proof
  simp[asm_call_prepare_def, call_has_value_def, static_gas_def]
QED

Definition asm_call_finish_def:
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) =
    if (lookup_account sender accounts).balance < value
    then abort_call_value stipend
    else do
      set_return_data [];
      sucDepth <- get_num_contexts;
      if sucDepth > 1024
      then abort_unuse stipend
      else proceed_call op sender address value ao az code stipend
             (Memory <| offset := ro; size := rs |>)
    od
End

Theorem asm_uncurry_projection[local]:
  !f. UNCURRY f = (\p. f (FST p) (SND p))
Proof
  gen_tac >> simp[FUN_EQ_THM] >> gen_tac >> Cases_on `p` >> simp[]
QED

Theorem asm_step_call_factor:
  step_call op s = vfmExecution$bind (asm_call_prepare op) (asm_call_finish op) s
Proof
  rewrite_tac[asm_call_prepare_def, asm_call_finish_def, step_call_def,
              asm_uncurry_projection, LET_THM] >>
  simp[bind_assoc, ignore_bind_def, asm_call_finish_def]
QED

Theorem asm_call_finish_balance:
  u.contexts = (c,rb)::rest /\ LENGTH c.stack < stack_limit /\
  stipend <= c.gasUsed /\ (lookup_account sender accounts).balance < value ==>
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (), u with contexts :=
      (c with <| stack := 0w :: c.stack; returnData := [];
                 gasUsed := c.gasUsed - stipend; pc updated_by SUC |>,rb)::rest)
Proof
  strip_tac >> drule_all asm_abort_call_value_state >>
  simp[asm_call_finish_def]
QED

Theorem asm_call_finish_depth:
  u.contexts = (c,rb)::rest /\ LENGTH c.stack < stack_limit /\
  stipend <= c.gasUsed /\ value <= (lookup_account sender accounts).balance /\
  1024 < LENGTH u.contexts ==>
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (), u with contexts :=
      (c with <| stack := 0w :: c.stack; returnData := [];
                 gasUsed := c.gasUsed - stipend; pc updated_by SUC |>,rb)::rest)
Proof
  strip_tac >> `LENGTH u.contexts = SUC (LENGTH rest)` by simp[] >>
  simp[asm_call_finish_def, set_return_data_def, get_num_contexts_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def] >>
  qmatch_goalsub_abbrev_tac `abort_unuse stipend v` >>
  `v.contexts = (c with returnData := [],rb)::rest` by simp[Abbr `v`] >>
  drule asm_abort_unuse_state >>
  disch_then (qspec_then `stipend` mp_tac) >>
  gvs[Abbr `v`, vfmConstantsTheory.stack_limit_def]
QED

Theorem asm_call_finish_proceed:
  u.contexts = (c,rb)::rest /\
  value <= (lookup_account sender accounts).balance /\
  LENGTH u.contexts <= 1024 ==>
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    proceed_call op sender address value ao az code stipend
      (Memory <| offset := ro; size := rs |>)
      (u with contexts := (c with returnData := [],rb)::rest)
Proof
  strip_tac >> `LENGTH u.contexts = SUC (LENGTH rest)` by simp[] >>
  simp[asm_call_finish_def, set_return_data_def, get_num_contexts_def,
       bind_def, ignore_bind_def, get_current_context_def,
       set_current_context_def, return_def]
QED

Theorem asm_pop_stack_state:
  s.contexts = (c,rb)::rest /\ n <= LENGTH c.stack ==>
  pop_stack n s =
    (INL (TAKE n c.stack), s with contexts :=
      (c with stack := DROP n c.stack,rb)::rest)
Proof
  simp[pop_stack_def, bind_def, ignore_bind_def, LET_THM,
       get_current_context_def, set_current_context_def, assert_def, return_def]
QED

Theorem asm_pop_stack_underflow:
  s.contexts = (c,rb)::rest /\ LENGTH c.stack < n ==>
  pop_stack n s = (INR (SOME StackUnderflow),s)
Proof
  simp[pop_stack_def, bind_def, ignore_bind_def, LET_THM,
       get_current_context_def, assert_def, return_def]
QED

Theorem asm_access_address_collect:
  s.msdomain = Collect d ==>
  access_address a s =
    (INL (if fIN a s.rollback.accesses.addresses
          then warm_access_cost else cold_access_cost),
     s with <| rollback := s.rollback with accesses :=
                 s.rollback.accesses with addresses := fINSERT a s.rollback.accesses.addresses;
               msdomain := Collect (d with addresses updated_by fINSERT a) |> )
Proof
  simp[access_address_def, domain_check_def, set_domain_def, return_def,
       bind_def, ignore_bind_def]
QED

Theorem asm_access_addresses_collect:
  s.msdomain = Collect d ==>
  (do ca <- access_address a; cb <- access_address b; return (ca,cb) od) s =
    (INL ((if fIN a s.rollback.accesses.addresses
           then warm_access_cost else cold_access_cost),
          (if fIN b (fINSERT a s.rollback.accesses.addresses)
           then warm_access_cost else cold_access_cost)),
     s with <| rollback := s.rollback with accesses :=
                 s.rollback.accesses with addresses :=
                   fINSERT b (fINSERT a s.rollback.accesses.addresses);
               msdomain := Collect (d with addresses updated_by (fINSERT b o fINSERT a)) |> )
Proof
  strip_tac >> drule asm_access_address_collect >>
  disch_then (qspec_then `a` assume_tac) >>
  simp[Once bind_def] >>
  simp[Once bind_def] >>
  qmatch_goalsub_abbrev_tac `access_address b t` >>
  `t.msdomain = Collect (d with addresses updated_by fINSERT a)` by
    simp[Abbr `t`] >>
  drule asm_access_address_collect >>
  disch_then (qspec_then `b` assume_tac) >>
  simp[bind_def, return_def, Abbr `t`]
QED

Theorem asm_memory_expansion_info_state:
  s.contexts = (c,rb)::rest ==>
  memory_expansion_info offset sz s =
    (INL <| cost := memory_expansion_cost (buffer_length c.memory)
                    (if 0 < sz then word_size (offset + sz) * 32 else 0);
            expand_by := MAX (buffer_length c.memory)
                    (if 0 < sz then word_size (offset + sz) * 32 else 0)
                    - buffer_length c.memory |>,s)
Proof
  simp[memory_expansion_info_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_consume_gas_state:
  s.contexts = (c,rb)::rest /\ c.gasUsed + k <= c.msgParams.gasLimit ==>
  consume_gas k s = (INL (),s with contexts :=
    (c with gasUsed := c.gasUsed + k,rb)::rest)
Proof
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def]
QED

Theorem asm_consume_gas_out_of_gas:
  s.contexts = (c,rb)::rest /\ c.msgParams.gasLimit < c.gasUsed + k ==>
  consume_gas k s = (INR (SOME OutOfGas),s)
Proof
  simp[consume_gas_def, get_current_context_def, bind_def,
       ignore_bind_def, assert_def, return_def]
QED

Theorem asm_expand_memory_state:
  s.contexts = (c,rb)::rest ==>
  expand_memory n s = (INL (),s with contexts :=
    (c with memory := buffer_extend n c.memory,rb)::rest)
Proof
  simp[expand_memory_def, get_current_context_def, set_current_context_def,
       bind_def, return_def]
QED

Theorem asm_call_prepare_collect_eq:
  !s c rb rest d op vo args gas address value ao az ro rs range newSize mxCost
   expansion ac t accounts target code dc u vc cc cg charge.
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack /\
  vo = (if call_has_value op then 1 else 0) /\
  args = TAKE (6 + vo) c.stack /\ gas = w2n (EL 0 args) /\
  address = w2w (EL 1 args) /\
  value = (if 0 < vo then w2n (EL 2 args) else 0) /\
  ao = w2n (EL (2 + vo) args) /\ az = w2n (EL (3 + vo) args) /\
  ro = w2n (EL (4 + vo) args) /\ rs = w2n (EL (5 + vo) args) /\
  range = max_expansion_range (ao,az) (ro,rs) /\
  newSize = (if 0 < SND range then word_size (FST range + SND range) * 32 else 0) /\
  mxCost = memory_expansion_cost (buffer_length c.memory) newSize /\
  expansion = MAX (buffer_length c.memory) newSize - buffer_length c.memory /\
  ac = (if fIN address s.rollback.accesses.addresses
        then warm_access_cost else cold_access_cost) /\
  t = s with <| contexts := (c with stack := DROP (6 + vo) c.stack,rb)::rest;
       rollback := s.rollback with accesses := s.rollback.accesses with
         addresses := fINSERT address s.rollback.accesses.addresses;
       msdomain := Collect (d with addresses updated_by fINSERT address) |> /\
  accounts = s.rollback.accounts /\ target = lookup_account address accounts /\
  (code,dc,u) = (case get_delegate target.code of
     NONE => (target.code,0,t)
   | SOME delegate =>
       ((lookup_account delegate accounts).code,
        (if fIN delegate t.rollback.accesses.addresses
         then warm_access_cost else cold_access_cost),
        t with <| rollback := t.rollback with accesses := t.rollback.accesses with
                    addresses := fINSERT delegate t.rollback.accesses.addresses;
                  msdomain := Collect (d with addresses updated_by
                    (fINSERT delegate o fINSERT address)) |>)) /\
  vc = (if 0 < value then call_value_cost else 0) /\
  cc = (if op = Call /\ 0 < value /\ account_empty target then new_account_cost else 0) /\
  cg = call_gas value gas (c.msgParams.gasLimit - c.gasUsed) mxCost (ac+vc+cc+dc) /\
  charge = static_gas op + FST cg + mxCost ==>
  asm_call_prepare op s =
    if c.msgParams.gasLimit < c.gasUsed + charge
    then (INR (SOME OutOfGas),u)
    else (INL (c.msgParams.callee,address,value,ao,az,code,SND cg,ro,rs,accounts),
          u with contexts :=
            (c with <| stack := DROP (6 + vo) c.stack;
                       gasUsed := c.gasUsed + charge;
                       memory := buffer_extend expansion c.memory |>,rb)::rest)
Proof
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `pop_stack (6+vo) s =
     (INL args,s with contexts := (c with stack := DROP (6+vo) c.stack,rb)::rest)` by
    (drule_all asm_pop_stack_state >> fs[]) >>
  pure_rewrite_tac[asm_call_prepare_def, LET_THM, asm_uncurry_projection] >>
  BETA_TAC >>
  qpat_assum `vo = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  pure_once_rewrite_tac[bind_def] >>
  qpat_assum `pop_stack _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `gas = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `address = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `value = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `ao = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `az = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `ro = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `rs = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `gas = _` (fn th => rewrite_tac[GSYM (SRULE [] th)]) >>
  rename1 `range' = max_expansion_range (ao,az) (ro,rs)` >>
  qpat_assum `range' = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qabbrev_tac `popped = s with contexts := (c with stack := DROP (6+vo) c.stack,rb)::rest` >>
  `popped.contexts = (c with stack := DROP (6+vo) c.stack,rb)::rest` by simp[Abbr `popped`] >>
  `memory_expansion_info (FST range') (SND range') popped =
     (INL <|cost := mxCost; expand_by := expansion|>,popped)` by
    (drule asm_memory_expansion_info_state >>
     disch_then (qspecl_then [`SND range'`,`FST range'`] mp_tac) >>
     fs[]) >>
  pure_once_rewrite_tac[bind_def] >>
  qpat_assum `memory_expansion_info _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  suspend "warmed"
QED

Resume asm_call_prepare_collect_eq[warmed]:
  `popped.msdomain = Collect d` by simp[Abbr `popped`] >>
  `access_address address popped = (INL ac,t)` by
    (drule asm_access_address_collect >>
     disch_then (qspec_then `address` mp_tac) >>
     simp[Abbr `popped`]) >>
  pure_once_rewrite_tac[bind_def] >>
  qpat_assum `access_address _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  `t.rollback.accounts = accounts` by simp[] >>
  pure_once_rewrite_tac[bind_def] >>
  simp_tac (srw_ss()) [get_accounts_def, return_def] >>
  qpat_assum `t.rollback.accounts = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `target = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `vc = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `cc = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  `t.msdomain = Collect (d with addresses updated_by fINSERT address)` by simp[] >>
  `(case get_delegate target.code of
      NONE => return (target.code,0)
    | SOME delegate => do cost <- access_address delegate;
                          return ((lookup_account delegate accounts).code,cost) od) t =
     (INL (code,dc),u)` by
    (Cases_on `get_delegate target.code`
     >- (qpat_x_assum `(code,dc,u) = _` mp_tac >>
         simp_tac (srw_ss()) [return_def] >> strip_tac >> simp[]) >>
     drule asm_access_address_collect >>
     disch_then (qspec_then `x` assume_tac) >>
     qpat_x_assum `(code,dc,u) = _` mp_tac >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     simp[bind_def, return_def]) >>
  pure_once_rewrite_tac[bind_def] >>
  qpat_assum `_ t = (INL (code,dc),u)` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  `u.contexts = (c with stack := DROP (6+vo) c.stack,rb)::rest` by
    (Cases_on `get_delegate target.code` >>
     qpat_x_assum `(code,dc,u) = _` mp_tac >>
     simp_tac (srw_ss()) [] >> strip_tac >> simp[]) >>
  suspend "gas"
QED

Resume asm_call_prepare_collect_eq[gas]:
  `get_gas_left u = (INL (c.msgParams.gasLimit - c.gasUsed),u)` by
    simp[get_gas_left_def, get_current_context_def, bind_def, return_def] >>
  pure_once_rewrite_tac[bind_def] >>
  qpat_assum `get_gas_left u = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `cg = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `charge = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  Cases_on `c.msgParams.gasLimit < c.gasUsed + charge`
  >- (`consume_gas charge u = (INR (SOME OutOfGas),u)` by
        (drule asm_consume_gas_out_of_gas >>
         disch_then (qspec_then `charge` mp_tac) >>
         qpat_assum `c.msgParams.gasLimit < _`
           (fn th => simp_tac (srw_ss()) [th])) >>
      pure_once_rewrite_tac[ignore_bind_def] >>
      pure_once_rewrite_tac[bind_def] >>
      qpat_assum `consume_gas charge u = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `c.msgParams.gasLimit < _`
        (fn th => simp_tac (srw_ss()) [th])) >>
  `consume_gas charge u =
     (INL (),u with contexts :=
        (c with <|stack := DROP (6+vo) c.stack; gasUsed := c.gasUsed+charge|>,rb)::rest)` by
    (drule asm_consume_gas_state >>
     disch_then (qspec_then `charge` mp_tac) >>
     qpat_assum `~(c.msgParams.gasLimit < _)`
       (fn th => simp_tac (srw_ss() ++ numSimps.ARITH_ss) [th])) >>
  pure_once_rewrite_tac[ignore_bind_def] >>
      pure_once_rewrite_tac[bind_def] >>
  qpat_assum `consume_gas charge u = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qabbrev_tac `paid = u with contexts :=
    (c with <|stack := DROP (6+vo) c.stack; gasUsed := c.gasUsed+charge|>,rb)::rest` >>
  `paid.contexts =
    (c with <|stack := DROP (6+vo) c.stack; gasUsed := c.gasUsed+charge|>,rb)::rest` by
    simp[Abbr `paid`] >>
  drule asm_expand_memory_state >>
  disch_then (qspec_then `expansion` assume_tac) >>
  qunabbrev_tac `paid` >>
  qpat_assum `~c.msgParams.static` (fn ns =>
    qpat_assum `~(c.msgParams.gasLimit < _)` (fn ng =>
      qpat_assum `expand_memory expansion _ = _` (fn ex =>
        simp_tac (srw_ss())
          [ns,ng,SRULE [] ex,COND_RATOR,assert_not_static_def,get_static_def,
           get_current_context_def,assert_def,bind_def,ignore_bind_def,
           return_def,get_callee_def])))
QED

Finalise asm_call_prepare_collect_eq
Theorem asm_call_stipend_le_charge:
  vc = (if 0 < value then call_value_cost else 0) /\
  cg = call_gas value gas gasLeft mxCost (ac + vc + cc + dc) /\
  charge = static_gas op + FST cg + mxCost ==>
  SND cg <= charge
Proof
  strip_tac >>
  `(if 0 < value then call_stipend else 0) <= (ac + vc + cc + dc) + mxCost` by
    (Cases_on `0 < value` >>
     fs[vfmConstantsTheory.call_stipend_def, vfmConstantsTheory.call_value_cost_def]) >>
  PairCases_on `cg` >>
  qpat_x_assum `(_,_) = call_gas _ _ _ _ _` (assume_tac o SYM) >>
  drule_all vfmRunCallTheory.call_gas_stipend_le_consumed >> simp[]
QED

Theorem asm_call_unused_gas_le_paid:
  (stipend:num) <= charge /\ childLimit <= stipend ==>
  childLimit - childUsed <= oldUsed + charge
Proof
  decide_tac
QED


Theorem asm_call_prepare_success_stack:
  s.contexts = (c,rb)::rest /\
  asm_call_prepare op s = (INL result,u) ==>
  6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack
Proof
  strip_tac >> spose_not_then assume_tac >>
  `pop_stack (6 + (if call_has_value op then 1 else 0)) s =
     (INR (SOME StackUnderflow),s)` by
    (qpat_x_assum `asm_call_prepare _ _ = _` kall_tac >>
     Cases_on `call_has_value op` >>
     gvs[pop_stack_def, get_current_context_def, assert_def, bind_def,
         ignore_bind_def, fail_def, return_def]) >>
  qpat_x_assum `asm_call_prepare _ _ = _` mp_tac >>
  pure_rewrite_tac[asm_call_prepare_def, LET_THM] >>
  Cases_on `call_has_value op` >> gvs[] >> simp[bind_def]
QED

Theorem asm_call_prepare_success_view:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  let vo = if call_has_value op then 1 else 0 in
  let args = TAKE (6 + vo) c.stack in
  6 + vo <= LENGTH c.stack /\
  sender = c.msgParams.callee /\ accounts = s.rollback.accounts /\
  address = w2w (EL 1 args) /\
  value = (if 0 < vo then w2n (EL 2 args) else 0) /\
  ao = w2n (EL (2 + vo) args) /\ az = w2n (EL (3 + vo) args) /\
  ro = w2n (EL (4 + vo) args) /\ rs = w2n (EL (5 + vo) args) /\
  ?charge acc d'.
    stipend <= charge /\ c.gasUsed + charge <= c.msgParams.gasLimit /\
    u = s with <| contexts :=
      (c with <| stack := DROP (6 + vo) c.stack;
                  gasUsed := c.gasUsed + charge;
                  memory := buffer_extend
                    (MAX (buffer_length c.memory)
                      (let range = max_expansion_range (ao,az) (ro,rs) in
                       if 0 < SND range then word_size (FST range + SND range) * 32 else 0)
                     - buffer_length c.memory) c.memory |>,rb)::rest;
      rollback := s.rollback with accesses := acc;
      msdomain := Collect d' |>
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_success_stack >> disch_tac >>
  qabbrev_tac `vo:num = if call_has_value op then 1 else 0` >>
  qabbrev_tac `args = TAKE (6 + vo) c.stack` >>
  qabbrev_tac `gas = w2n (EL 0 args)` >>
  qabbrev_tac `address' = w2w (EL 1 args) : address` >>
  qabbrev_tac `value' = if 0 < vo then w2n (EL 2 args) else 0` >>
  qabbrev_tac `ao' = w2n (EL (2 + vo) args)` >>
  qabbrev_tac `az' = w2n (EL (3 + vo) args)` >>
  qabbrev_tac `ro' = w2n (EL (4 + vo) args)` >>
  qabbrev_tac `rs' = w2n (EL (5 + vo) args)` >>
  qabbrev_tac `range' = max_expansion_range (ao',az') (ro',rs')` >>
  qabbrev_tac `newSize = if 0 < SND range' then word_size (FST range' + SND range') * 32 else 0` >>
  qabbrev_tac `mxCost = memory_expansion_cost (buffer_length c.memory) newSize` >>
  qabbrev_tac `expansion = MAX (buffer_length c.memory) newSize - buffer_length c.memory` >>
  qabbrev_tac `ac = if fIN address' s.rollback.accesses.addresses then warm_access_cost else cold_access_cost` >>
  qabbrev_tac `t = s with <| contexts := (c with stack := DROP (6 + vo) c.stack,rb)::rest;
    rollback := s.rollback with accesses := s.rollback.accesses with
      addresses := fINSERT address' s.rollback.accesses.addresses;
    msdomain := Collect (d with addresses updated_by fINSERT address') |>` >>
  qabbrev_tac `accounts' = s.rollback.accounts` >>
  qabbrev_tac `target = lookup_account address' accounts'` >>
  qabbrev_tac `resolved = case get_delegate target.code of
    NONE => (target.code,0,t)
  | SOME delegate => ((lookup_account delegate accounts').code,
      (if fIN delegate t.rollback.accesses.addresses then warm_access_cost else cold_access_cost),
      t with <| rollback := t.rollback with accesses := t.rollback.accesses with
        addresses := fINSERT delegate t.rollback.accesses.addresses;
        msdomain := Collect (d with addresses updated_by (fINSERT delegate o fINSERT address')) |>)` >>
  PairCases_on `resolved` >>
  suspend "named"
QED

Resume asm_call_prepare_success_view[named]:
  qabbrev_tac `vc = if 0 < value' then call_value_cost else 0` >>
  qabbrev_tac `cc = if op = Call /\ 0 < value' /\ account_empty target then new_account_cost else 0` >>
  qabbrev_tac `cg = call_gas value' gas (c.msgParams.gasLimit - c.gasUsed) mxCost (ac+vc+cc+resolved1)` >>
  qabbrev_tac `charge = static_gas op + FST cg + mxCost` >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack` by metis_tac[] >>
  drule_all asm_call_prepare_collect_eq >>
  qpat_x_assum `asm_call_prepare _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `c.msgParams.gasLimit < c.gasUsed + charge`
  >- (qpat_assum `c.msgParams.gasLimit < _` (fn th => simp_tac (srw_ss()) [th])) >>
  qpat_assum `~(c.msgParams.gasLimit < _)` (fn th => simp_tac (srw_ss()) [th]) >>
  strip_tac >>
  drule_all asm_call_stipend_le_charge >> disch_tac >>
  suspend "project"
QED

Resume asm_call_prepare_success_view[project]:
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[GSYM th]))
    [`args = _`, `address' = _`, `value' = _`, `ao' = _`, `az' = _`,
     `ro' = _`, `rs' = _`, `range' = _`, `newSize = _`, `expansion = _`] >>
  qpat_assum `6 + vo <= _` (fn th => simp_tac (srw_ss()) [th]) >>
  qexists_tac `charge` >>
  `c.gasUsed + charge <= c.msgParams.gasLimit` by decide_tac >>
  qpat_assum `SND cg <= charge` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `c.gasUsed + charge <= _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  Cases_on `get_delegate target.code` >>
  qpat_x_assum `(resolved0,resolved1,resolved2) = _` mp_tac >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_x_assum `resolved2 = _` SUBST_ALL_TAC >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `Collect domain0` >>
  qmatch_goalsub_abbrev_tac `s.rollback with accesses := access0` >>
  qexistsl_tac [`access0`,`domain0`] >> simp_tac (srw_ss()) []
QED

Finalise asm_call_prepare_success_view

Theorem asm_message_prepare_success_view:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall \/ op = DelegateCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  let vo = if call_has_value op then 1 else 0 in
  let args = TAKE (6 + vo) c.stack in
  6 + vo <= LENGTH c.stack /\
  sender = c.msgParams.callee /\ accounts = s.rollback.accounts /\
  address = w2w (EL 1 args) /\
  value = (if 0 < vo then w2n (EL 2 args) else 0) /\
  ao = w2n (EL (2 + vo) args) /\ az = w2n (EL (3 + vo) args) /\
  ro = w2n (EL (4 + vo) args) /\ rs = w2n (EL (5 + vo) args) /\
  ?charge acc d'.
    stipend <= charge /\ c.gasUsed + charge <= c.msgParams.gasLimit /\
    u = s with <| contexts :=
      (c with <| stack := DROP (6 + vo) c.stack;
                  gasUsed := c.gasUsed + charge;
                  memory := buffer_extend
                    (MAX (buffer_length c.memory)
                      (let range = max_expansion_range (ao,az) (ro,rs) in
                       if 0 < SND range then word_size (FST range + SND range) * 32 else 0)
                     - buffer_length c.memory) c.memory |>,rb)::rest;
      rollback := s.rollback with accesses := acc;
      msdomain := Collect d' |>
Proof
  strip_tac
  >- (irule asm_call_prepare_success_view >> simp[] >> metis_tac[])
  >- (irule asm_call_prepare_success_view >> simp[] >> metis_tac[]) >>
  gvs[asm_call_prepare_delegate] >>
  drule_at (Pat `asm_call_prepare _ _ = _`) asm_call_prepare_success_view >>
  disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
  asm_simp_tac (srw_ss()) [call_has_value_def, LET_THM] >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`charge`,`acc`,`d'`] >> simp[]
QED

Theorem asm_call_prepare_contexts_wf:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  EVERY (wf_context o FST) s.contexts /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  EVERY (wf_context o FST) u.contexts
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_success_view >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  gvs[wf_context_def, LENGTH_DROP] >> decide_tac
QED

Theorem asm_call_prepare_stack_room:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  EVERY (wf_context o FST) s.contexts /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  LENGTH (FST (HD u.contexts)).stack < stack_limit
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_success_view >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  gvs[wf_context_def, LENGTH_DROP] >> decide_tac
QED

Theorem asm_call_prepare_stipend_paid:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  EVERY (wf_context o FST) s.contexts /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  stipend <= (FST (HD u.contexts)).gasUsed
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_success_view >>
  simp_tac (srw_ss()) [LET_THM] >> strip_tac >> gvs[]
QED

Theorem asm_pop_and_incorporate_context_state:
  s.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
  child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed ==>
  pop_and_incorporate_context success s =
    let g = child.msgParams.gasLimit - child.gasUsed in
    let p = if success then parent with <|
                gasUsed := parent.gasUsed - g;
                logs := parent.logs ++ child.logs;
                addRefund := parent.addRefund + child.addRefund;
                subRefund := parent.subRefund + child.subRefund |>
            else parent with gasUsed := parent.gasUsed - g in
    (INL (), s with <| contexts := (p,parent_rb)::rest;
                       rollback := if success then s.rollback else child_rb |>)
Proof
  strip_tac >> Cases_on `success` >>
  simp[pop_and_incorporate_context_def, get_gas_left_def,
       get_current_context_def, pop_context_def, unuse_gas_def,
       set_current_context_def, set_rollback_def, push_logs_def,
       update_gas_refund_def, bind_def, ignore_bind_def, return_def,
       assert_def] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[vfmContextTheory.context_component_equality]
QED

Theorem asm_handle_exception_memory_success:
  s.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
  child.msgParams.outputTo = Memory r /\
  LENGTH parent.stack < stack_limit /\
  child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed ==>
  handle_exception NONE s = (INL (), s with contexts :=
    (parent with <|
      gasUsed := parent.gasUsed - (child.msgParams.gasLimit-child.gasUsed);
      pc := SUC parent.pc; stack := b2w T :: parent.stack;
      returnData := child.returnData;
      memory := buffer_write r.offset (TAKE r.size child.returnData) parent.memory;
      logs := parent.logs ++ child.logs;
      addRefund := parent.addRefund + child.addRefund;
      subRefund := parent.subRefund + child.subRefund |>,parent_rb)::rest)
Proof
  strip_tac >>
  drule_all asm_pop_and_incorporate_context_state >>
  disch_then (qspec_then `T` assume_tac) >>
  fs[vfmConstantsTheory.stack_limit_def] >>
  simp[handle_exception_def, get_num_contexts_def, get_return_data_def,
       get_output_to_def, get_current_context_def, bind_def,
       ignore_bind_def, return_def, asm_pop_and_incorporate_context_state,
       inc_pc_def, set_return_data_def, push_stack_def, write_memory_def,
       set_current_context_def, assert_def, vfmConstantsTheory.stack_limit_def] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[vfmContextTheory.context_component_equality]
QED

Theorem asm_handle_exception_memory_reverted:
  s.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
  child.msgParams.outputTo = Memory r /\
  LENGTH parent.stack < stack_limit /\
  child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed ==>
  handle_exception (SOME Reverted) s = (INL (), s with <|
    contexts := (parent with <|
      gasUsed := parent.gasUsed - (child.msgParams.gasLimit-child.gasUsed);
      pc := SUC parent.pc; stack := b2w F :: parent.stack;
      returnData := child.returnData;
      memory := buffer_write r.offset (TAKE r.size child.returnData) parent.memory
    |>,parent_rb)::rest; rollback := child_rb |>)
Proof
  strip_tac >>
  drule_all asm_pop_and_incorporate_context_state >>
  disch_then (qspec_then `F` assume_tac) >>
  fs[vfmConstantsTheory.stack_limit_def] >>
  simp[handle_exception_def, get_num_contexts_def, get_return_data_def,
       get_output_to_def, get_current_context_def, bind_def,
       ignore_bind_def, return_def, inc_pc_def, set_return_data_def,
       push_stack_def, write_memory_def, set_current_context_def, assert_def] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[vfmContextTheory.context_component_equality]
QED

Theorem asm_handle_exception_memory_exception:
  s.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
  child.msgParams.outputTo = Memory r /\
  child.gasUsed <= child.msgParams.gasLimit /\
  LENGTH parent.stack < stack_limit /\ exc <> Reverted ==>
  handle_exception (SOME exc) s = (INL (), s with <|
    contexts := (parent with <| pc := SUC parent.pc;
      stack := 0w :: parent.stack; returnData := [];
      memory := buffer_write r.offset [] parent.memory |>,parent_rb)::rest;
    rollback := child_rb |>)
Proof
  strip_tac >>
  simp[handle_exception_def, get_gas_left_def, get_current_context_def,
       consume_gas_def, set_current_context_def, set_return_data_def,
       get_num_contexts_def, get_return_data_def, get_output_to_def,
       bind_def, ignore_bind_def, return_def, assert_def] >>
  qmatch_goalsub_abbrev_tac `pop_and_incorporate_context F t` >>
  `t.contexts = (child with <|returnData := [];
       gasUsed := child.msgParams.gasLimit|>,child_rb)::(parent,parent_rb)::rest`
    by simp[Abbr `t`] >>
  qpat_x_assum `s.contexts = _` kall_tac >>
  drule asm_pop_and_incorporate_context_state >>
  simp[] >> disch_then (qspec_then `F` assume_tac) >>
  fs[vfmConstantsTheory.stack_limit_def] >>
  simp[inc_pc_def, set_return_data_def, push_stack_def, write_memory_def,
       get_current_context_def, set_current_context_def, bind_def,
       ignore_bind_def, return_def, assert_def, Abbr `t`] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[vfmContextTheory.context_component_equality]
QED

Theorem asm_message_step_terminal:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall \/ op = DelegateCall) /\
  step_call op s = (INR e,t) ==>
  step s = handle_step e t
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `FLOOKUP c.msgParams.parsed c.pc = SOME op` by
    (qpat_x_assum `next_opcode c = _` mp_tac >>
     simp[next_opcode_def] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  simp_tac (srw_ss()) [step_def, get_current_context_def, handle_def,
    bind_def, ignore_bind_def, return_def] >>
  qpat_assum `s.contexts = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `FLOOKUP _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `op = Call \/ op = StaticCall \/ op = DelegateCall` strip_assume_tac >>
  gvs[step_inst_def, bind_def, ignore_bind_def]
QED

Theorem asm_call_step_terminal:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall) /\
  step_call op s = (INR e,t) ==>
  step s = handle_step e t
Proof
  strip_tac >> irule asm_message_step_terminal >> simp[] >> metis_tac[]
QED

Theorem asm_handle_step_memory:
  t.contexts = (child,child_rb)::tail /\
  child.msgParams.outputTo = Memory mr ==>
  handle_step e t =
    (if vfm_abort e then (INR e,t) else handle_exception e t)
Proof
  strip_tac >>
  simp[handle_step_def, handle_create_def, get_return_data_def,
       get_output_to_def, get_current_context_def, handle_def,
       bind_def, ignore_bind_def, return_def, reraise_def] >>
  Cases_on `e` >> Cases_on `vfm_abort (SOME x)` >>
  simp[handle_def, bind_def, ignore_bind_def, get_current_context_def,
       return_def, reraise_def]
QED

Theorem asm_proceed_call_contexts_wf:
  s.contexts <> [] /\ EVERY (wf_context o FST) s.contexts /\
  proceed_call op sender address value ao az code stipend outputTo s = (res,t) ==>
  t.contexts <> [] /\ EVERY (wf_context o FST) t.contexts
Proof
  strip_tac >>
  `stipend < SUC stipend` by simp[] >>
  drule decreases_gas_cred_proceed_call >>
  rewrite_tac[decreases_gas_cred_def] >>
  disch_tac >> metis_tac[pairTheory.SND]
QED

Theorem asm_proceed_call_child_gas:
  s.contexts <> [] /\ EVERY (wf_context o FST) s.contexts /\
  proceed_call op sender address value ao az code stipend outputTo s = (res,t) ==>
  (FST (HD t.contexts)).gasUsed <= (FST (HD t.contexts)).msgParams.gasLimit
Proof
  strip_tac >> drule_all asm_proceed_call_contexts_wf >>
  Cases_on `t.contexts` >> simp[wf_context_def]
QED

Theorem asm_call_prepare_proceed_child_gas:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  EVERY (wf_context o FST) s.contexts /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  proceed_call op sender address value ao az code stipend (Memory mr) u = (res,t) ==>
  (FST (HD t.contexts)).gasUsed <= (FST (HD t.contexts)).msgParams.gasLimit
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `EVERY (wf_context o FST) u.contexts` by
    (drule_all asm_call_prepare_contexts_wf >> simp[]) >>
  `u.contexts <> []` by
    (drule_all asm_call_prepare_success_view >>
     simp_tac (srw_ss()) [LET_THM] >> strip_tac >> gvs[]) >>
  drule_all asm_proceed_call_child_gas >> simp[]
QED

Theorem asm_proceed_call_memory_boundary:
  s.contexts = (parent,parent_rb)::rest /\
  proceed_call op sender address value ao az code stipend (Memory mr) s = (res,t) /\
  stipend <= parent.gasUsed ==>
  ?child child_rb.
    t.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
    child.msgParams.outputTo = Memory mr /\
    child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed
Proof
  strip_tac >>
  `s.contexts <> []` by simp[] >>
  drule_all vfmRunCallTheory.proceed_call_push_structure >> strip_tac >>
  drule vfmRunCallTheory.proceed_call_parent_gas_ok >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `t.contexts` >- fs[] >>
  PairCases_on `h` >> gvs[]
QED

Theorem asm_proceed_call_memory_success:
  s.contexts = (parent,parent_rb)::rest /\
  proceed_call op sender address value ao az code stipend (Memory mr) s = (res,t) /\
  stipend <= parent.gasUsed /\ LENGTH parent.stack < stack_limit ==>
  ?child child_rb.
    t.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
    handle_exception NONE t = (INL (), t with contexts :=
      (parent with <|
        gasUsed := parent.gasUsed - (child.msgParams.gasLimit-child.gasUsed);
        pc := SUC parent.pc; stack := b2w T :: parent.stack;
        returnData := child.returnData;
        memory := buffer_write mr.offset (TAKE mr.size child.returnData) parent.memory;
        logs := parent.logs ++ child.logs;
        addRefund := parent.addRefund + child.addRefund;
        subRefund := parent.subRefund + child.subRefund |>,parent_rb)::rest)
Proof
  strip_tac >> drule_all asm_proceed_call_memory_boundary >> strip_tac >>
  qexistsl [`child`, `child_rb`] >> conj_tac >- simp[] >>
  drule_all asm_handle_exception_memory_success >> simp[]
QED

Theorem asm_proceed_call_memory_reverted:
  s.contexts = (parent,parent_rb)::rest /\
  proceed_call op sender address value ao az code stipend (Memory mr) s = (res,t) /\
  stipend <= parent.gasUsed /\ LENGTH parent.stack < stack_limit ==>
  ?child child_rb.
    t.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
    handle_exception (SOME Reverted) t = (INL (), t with <|
      contexts := (parent with <|
        gasUsed := parent.gasUsed - (child.msgParams.gasLimit-child.gasUsed);
        pc := SUC parent.pc; stack := b2w F :: parent.stack;
        returnData := child.returnData;
        memory := buffer_write mr.offset (TAKE mr.size child.returnData) parent.memory
      |>,parent_rb)::rest; rollback := child_rb |>)
Proof
  strip_tac >> drule_all asm_proceed_call_memory_boundary >> strip_tac >>
  qexistsl [`child`, `child_rb`] >> conj_tac >- simp[] >>
  drule_all asm_handle_exception_memory_reverted >> simp[]
QED

Theorem asm_proceed_call_memory_exception:
  s.contexts = (parent,parent_rb)::rest /\
  proceed_call op sender address value ao az code stipend (Memory mr) s = (res,t) /\
  stipend <= parent.gasUsed /\ LENGTH parent.stack < stack_limit /\
  exc <> Reverted /\
  (FST (HD t.contexts)).gasUsed <= (FST (HD t.contexts)).msgParams.gasLimit ==>
  ?child child_rb.
    t.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
    handle_exception (SOME exc) t = (INL (), t with <|
      contexts := (parent with <| pc := SUC parent.pc;
        stack := 0w :: parent.stack; returnData := [];
        memory := buffer_write mr.offset [] parent.memory |>,parent_rb)::rest;
      rollback := child_rb |>)
Proof
  strip_tac >> drule_all asm_proceed_call_memory_boundary >> strip_tac >>
  qexistsl [`child`, `child_rb`] >> conj_tac >- simp[] >>
  `child.gasUsed <= child.msgParams.gasLimit` by gvs[] >>
  drule_all asm_handle_exception_memory_exception >> simp[]
QED

Theorem asm_call_step_memory_success:
  s.contexts = (c,rb)::outer /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall) /\
  step_call op s = (INR NONE,t) /\
  u.contexts = (parent,parent_rb)::rest /\
  proceed_call op sender address value ao az code stipend (Memory mr) u = (res,t) /\
  stipend <= parent.gasUsed /\ LENGTH parent.stack < stack_limit ==>
  ?child child_rb.
    t.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
    step s = (INL (), t with contexts :=
      (parent with <|
        gasUsed := parent.gasUsed - (child.msgParams.gasLimit-child.gasUsed);
        pc := SUC parent.pc; stack := b2w T :: parent.stack;
        returnData := child.returnData;
        memory := buffer_write mr.offset (TAKE mr.size child.returnData) parent.memory;
        logs := parent.logs ++ child.logs;
        addRefund := parent.addRefund + child.addRefund;
        subRefund := parent.subRefund + child.subRefund |>,parent_rb)::rest)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_step_terminal >> disch_tac >>
  drule_all asm_proceed_call_memory_boundary >> strip_tac >>
  drule_all asm_handle_step_memory >> disch_tac >>
  drule_all asm_proceed_call_memory_success >> strip_tac >>
  gvs[vfm_abort_def] >> metis_tac[]
QED

Theorem asm_call_step_memory_reverted:
  s.contexts = (c,rb)::outer /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall) /\
  step_call op s = (INR (SOME Reverted),t) /\
  u.contexts = (parent,parent_rb)::rest /\
  proceed_call op sender address value ao az code stipend (Memory mr) u = (res,t) /\
  stipend <= parent.gasUsed /\ LENGTH parent.stack < stack_limit ==>
  ?child child_rb.
    t.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
    step s = (INL (), t with <|
      contexts := (parent with <|
        gasUsed := parent.gasUsed - (child.msgParams.gasLimit-child.gasUsed);
        pc := SUC parent.pc; stack := b2w F :: parent.stack;
        returnData := child.returnData;
        memory := buffer_write mr.offset (TAKE mr.size child.returnData) parent.memory
      |>,parent_rb)::rest; rollback := child_rb |>)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_step_terminal >> disch_tac >>
  drule_all asm_proceed_call_memory_boundary >> strip_tac >>
  drule_all asm_handle_step_memory >> disch_tac >>
  drule_all asm_proceed_call_memory_reverted >> strip_tac >>
  gvs[vfm_abort_def] >> metis_tac[]
QED

Theorem asm_call_step_memory_exception:
  s.contexts = (c,rb)::outer /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall) /\
  step_call op s = (INR (SOME exc),t) /\
  u.contexts = (parent,parent_rb)::rest /\
  proceed_call op sender address value ao az code stipend (Memory mr) u = (res,t) /\
  stipend <= parent.gasUsed /\ LENGTH parent.stack < stack_limit /\
  exc <> Reverted /\ ~vfm_abort (SOME exc) /\
  (FST (HD t.contexts)).gasUsed <= (FST (HD t.contexts)).msgParams.gasLimit ==>
  ?child child_rb.
    t.contexts = (child,child_rb)::(parent,parent_rb)::rest /\
    step s = (INL (), t with <|
      contexts := (parent with <| pc := SUC parent.pc;
        stack := 0w :: parent.stack; returnData := [];
        memory := buffer_write mr.offset [] parent.memory |>,parent_rb)::rest;
      rollback := child_rb |>)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_step_terminal >> disch_tac >>
  drule_all asm_proceed_call_memory_boundary >> strip_tac >>
  drule_all asm_handle_step_memory >> disch_tac >>
  drule_all asm_proceed_call_memory_exception >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem asm_call_step_terminal_abort:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall) /\
  step_call op s = (INR e,t) /\ vfm_abort e ==>
  step s = (INR e,t)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_step_terminal >>
  simp[handle_step_def, reraise_def]
QED

Theorem asm_call_prepare_failure_kind:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack /\
  asm_call_prepare op s = (INR e,t) ==>
  e = SOME OutOfGas
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  qabbrev_tac `vo:num = if call_has_value op then 1 else 0` >>
  qabbrev_tac `args = TAKE (6 + vo) c.stack` >>
  qabbrev_tac `gas = w2n (EL 0 args)` >>
  qabbrev_tac `address' = w2w (EL 1 args) : address` >>
  qabbrev_tac `value' = if 0 < vo then w2n (EL 2 args) else 0` >>
  qabbrev_tac `ao' = w2n (EL (2 + vo) args)` >>
  qabbrev_tac `az' = w2n (EL (3 + vo) args)` >>
  qabbrev_tac `ro' = w2n (EL (4 + vo) args)` >>
  qabbrev_tac `rs' = w2n (EL (5 + vo) args)` >>
  qabbrev_tac `range' = max_expansion_range (ao',az') (ro',rs')` >>
  qabbrev_tac `newSize = if 0 < SND range' then word_size (FST range' + SND range') * 32 else 0` >>
  qabbrev_tac `mxCost = memory_expansion_cost (buffer_length c.memory) newSize` >>
  qabbrev_tac `expansion = MAX (buffer_length c.memory) newSize - buffer_length c.memory` >>
  qabbrev_tac `ac = if fIN address' s.rollback.accesses.addresses then warm_access_cost else cold_access_cost` >>
  qabbrev_tac `warmed = s with <| contexts := (c with stack := DROP (6 + vo) c.stack,rb)::rest;
    rollback := s.rollback with accesses := s.rollback.accesses with
      addresses := fINSERT address' s.rollback.accesses.addresses;
    msdomain := Collect (d with addresses updated_by fINSERT address') |>` >>
  qabbrev_tac `accounts' = s.rollback.accounts` >>
  qabbrev_tac `target = lookup_account address' accounts'` >>
  qabbrev_tac `resolved = case get_delegate target.code of
    NONE => (target.code,0,warmed)
  | SOME delegate => ((lookup_account delegate accounts').code,
      (if fIN delegate warmed.rollback.accesses.addresses then warm_access_cost else cold_access_cost),
      warmed with <| rollback := warmed.rollback with accesses := warmed.rollback.accesses with
        addresses := fINSERT delegate warmed.rollback.accesses.addresses;
        msdomain := Collect (d with addresses updated_by (fINSERT delegate o fINSERT address')) |>)` >>
  PairCases_on `resolved` >>
  qabbrev_tac `vc = if 0 < value' then call_value_cost else 0` >>
  qabbrev_tac `cc = if op = Call /\ 0 < value' /\ account_empty target then new_account_cost else 0` >>
  qabbrev_tac `cg = call_gas value' gas (c.msgParams.gasLimit - c.gasUsed) mxCost (ac+vc+cc+resolved1)` >>
  qabbrev_tac `charge = static_gas op + FST cg + mxCost` >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack` by metis_tac[] >>
  drule_all asm_call_prepare_collect_eq >>
  qpat_x_assum `asm_call_prepare _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `c.msgParams.gasLimit < c.gasUsed + charge` >> simp[]
QED

Theorem asm_call_prepare_failure_step:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ next_opcode c = SOME op /\
  (op = Call \/ op = StaticCall) /\
  6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack /\
  asm_call_prepare op s = (INR e,t) ==>
  step s = handle_step (SOME OutOfGas) t
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_failure_kind >> disch_then SUBST_ALL_TAC >>
  `step_call op s = (INR (SOME OutOfGas),t)` by
    simp[asm_step_call_factor, bind_def] >>
  drule_all asm_call_step_terminal >> simp[]
QED

Theorem asm_call_prepare_failure_view:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack /\
  asm_call_prepare op s = (INR e,t) ==>
  t.contexts = (c with stack := DROP (6 + (if call_has_value op then 1 else 0)) c.stack,rb)::rest /\
  t.txParams = s.txParams
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  qabbrev_tac `vo:num = if call_has_value op then 1 else 0` >>
  qabbrev_tac `args = TAKE (6 + vo) c.stack` >>
  qabbrev_tac `gas = w2n (EL 0 args)` >>
  qabbrev_tac `address' = w2w (EL 1 args) : address` >>
  qabbrev_tac `value' = if 0 < vo then w2n (EL 2 args) else 0` >>
  qabbrev_tac `ao' = w2n (EL (2 + vo) args)` >>
  qabbrev_tac `az' = w2n (EL (3 + vo) args)` >>
  qabbrev_tac `ro' = w2n (EL (4 + vo) args)` >>
  qabbrev_tac `rs' = w2n (EL (5 + vo) args)` >>
  qabbrev_tac `range' = max_expansion_range (ao',az') (ro',rs')` >>
  qabbrev_tac `newSize = if 0 < SND range' then word_size (FST range' + SND range') * 32 else 0` >>
  qabbrev_tac `mxCost = memory_expansion_cost (buffer_length c.memory) newSize` >>
  qabbrev_tac `expansion = MAX (buffer_length c.memory) newSize - buffer_length c.memory` >>
  qabbrev_tac `ac = if fIN address' s.rollback.accesses.addresses then warm_access_cost else cold_access_cost` >>
  qabbrev_tac `warmed = s with <| contexts := (c with stack := DROP (6 + vo) c.stack,rb)::rest;
    rollback := s.rollback with accesses := s.rollback.accesses with
      addresses := fINSERT address' s.rollback.accesses.addresses;
    msdomain := Collect (d with addresses updated_by fINSERT address') |>` >>
  qabbrev_tac `accounts' = s.rollback.accounts` >>
  qabbrev_tac `target = lookup_account address' accounts'` >>
  qabbrev_tac `resolved = case get_delegate target.code of
    NONE => (target.code,0,warmed)
  | SOME delegate => ((lookup_account delegate accounts').code,
      (if fIN delegate warmed.rollback.accesses.addresses then warm_access_cost else cold_access_cost),
      warmed with <| rollback := warmed.rollback with accesses := warmed.rollback.accesses with
        addresses := fINSERT delegate warmed.rollback.accesses.addresses;
        msdomain := Collect (d with addresses updated_by (fINSERT delegate o fINSERT address')) |>)` >>
  PairCases_on `resolved` >>
  qabbrev_tac `vc = if 0 < value' then call_value_cost else 0` >>
  qabbrev_tac `cc = if op = Call /\ 0 < value' /\ account_empty target then new_account_cost else 0` >>
  qabbrev_tac `cg = call_gas value' gas (c.msgParams.gasLimit - c.gasUsed) mxCost (ac+vc+cc+resolved1)` >>
  qabbrev_tac `charge = static_gas op + FST cg + mxCost` >>
  rule_assum_tac (REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack` by metis_tac[] >>
  drule_all asm_call_prepare_collect_eq >>
  qpat_x_assum `asm_call_prepare _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `c.msgParams.gasLimit < c.gasUsed + charge` >> simp[] >>
  strip_tac >>
  Cases_on `get_delegate target.code` >>
  qpat_x_assum `(resolved0,resolved1,resolved2) = _` mp_tac >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem asm_run_call_stops_after_step:
  step s = (r,t) /\ (~ISL r \/ LENGTH t.contexts < LENGTH s.contexts) ==>
  run_call s = SOME (r,t)
Proof
  strip_tac >> drule vfmAccountFrameTheory.run_call_step_equation >>
  simp[Once WhileTheory.OWHILE_THM] >>
  Cases_on `ISL r` >> gvs[]
QED

Theorem asm_handle_step_oog_singleton:
  t.contexts = [(c,rb)] /\ c.gasUsed <= c.msgParams.gasLimit ==>
  handle_step (SOME OutOfGas) t =
    (INR (SOME OutOfGas), t with contexts :=
      [(c with <| gasUsed := c.msgParams.gasLimit; returnData := [] |>,rb)])
Proof
  strip_tac >>
  simp[handle_step_def, handle_create_def, get_return_data_def,
       get_output_to_def, get_current_context_def, bind_def,
       ignore_bind_def, return_def, handle_def, reraise_def] >>
  Cases_on `c.msgParams.outputTo` >>
  simp[handle_def, bind_def, ignore_bind_def, return_def, reraise_def,
       handle_exception_def, get_gas_left_def, get_current_context_def,
       consume_gas_def, set_current_context_def, set_return_data_def,
       get_num_contexts_def, assert_def]
QED

Theorem asm_step_oog_starved:
  s.contexts = (c,rb)::rest /\ wf_state s /\
  (rest = [] \/ (?mr. c.msgParams.outputTo = Memory mr)) /\
  step s = handle_step (SOME OutOfGas) t /\
  t.contexts = (c with stack := DROP n c.stack,rb)::rest /\
  t.txParams = s.txParams ==>
  ?r s'. run_call s = SOME (r,s') /\ frame_resource_starved s r s'
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `c.gasUsed <= c.msgParams.gasLimit` by
    (qpat_x_assum `wf_state s` mp_tac >> simp[wf_state_def, wf_context_def]) >>
  qmatch_asmsub_abbrev_tac `t.contexts = (popped,rb)::rest` >>
  `popped.gasUsed <= popped.msgParams.gasLimit` by simp[Abbr `popped`] >>
  Cases_on `rest`
  >- suspend "single" >>
  PairCases_on `h` >>
  `?mr. c.msgParams.outputTo = Memory mr` by metis_tac[NOT_CONS_NIL] >>
  pop_assum strip_assume_tac >>
  `popped.msgParams.outputTo = Memory mr` by simp[Abbr `popped`] >>
  `LENGTH h0.stack < stack_limit` by
    (qpat_x_assum `wf_state s` mp_tac >> simp[wf_state_def, stack_room_ok_def]) >>
  drule_all asm_handle_step_memory >> disch_tac >>
  `OutOfGas <> Reverted` by simp[] >>
  drule_all asm_handle_exception_memory_exception >> disch_tac >>
  suspend "nested"
QED

Resume asm_step_oog_starved[single]:
  drule_all asm_handle_step_oog_singleton >> disch_tac >>
  `step s = (INR (SOME OutOfGas), t with contexts :=
    [(popped with <|gasUsed := popped.msgParams.gasLimit; returnData := []|>,rb)])`
    by metis_tac[] >>
  drule asm_run_call_stops_after_step >> simp[] >> strip_tac >>
  simp[frame_resource_starved_def, frame_outcome_def] >>
  qexistsl_tac [`OutOfGas`, `[]`, `[]`] >> simp[]
QED

Resume asm_step_oog_starved[nested]:
  `step s = (INL (), t with <| contexts :=
      (h0 with <|pc := SUC h0.pc; stack := 0w::h0.stack; returnData := [];
        memory := buffer_write mr.offset [] h0.memory|>,h1)::t'; rollback := rb|>)`
    by simp[] >>
  drule asm_run_call_stops_after_step >> simp[] >> strip_tac >>
  simp[frame_resource_starved_def, frame_outcome_def] >>
  metis_tac[]
QED
Finalise asm_step_oog_starved

Theorem asm_call_prepare_failure_starved:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\ wf_state s /\
  ~c.msgParams.static /\ next_opcode c = SOME op /\
  (op = Call \/ op = StaticCall) /\
  6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack /\
  (rest = [] \/ (?mr. c.msgParams.outputTo = Memory mr)) /\
  asm_call_prepare op s = (INR e,t) ==>
  ?r s'. run_call s = SOME (r,s') /\ frame_resource_starved s r s'
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_failure_step >> disch_tac >>
  drule_all asm_call_prepare_failure_view >> strip_tac >>
  drule_all asm_step_oog_starved >> simp[]
QED
Theorem asm_frame_call_prepare_failure_starved:
  asm_frame_rel prog data es0 as s /\
  s.contexts = (c,rb)::rest /\ next_opcode c = SOME op /\
  (op = Call \/ op = StaticCall) /\
  6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack /\
  (rest = [] \/ (?mr. c.msgParams.outputTo = Memory mr)) /\
  asm_call_prepare op s = (INR e,t) ==>
  ?r s'. run_call s = SOME (r,s') /\ frame_resource_starved es0 r s'
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  qpat_x_assum `asm_frame_rel _ _ _ _ _` mp_tac >>
  simp[asm_frame_rel_def] >> rpt strip_tac >>
  `~c.msgParams.static` by metis_tac[CONS_11, pairTheory.PAIR_EQ] >>
  drule_all asm_call_prepare_failure_starved >> strip_tac >>
  drule_all frame_resource_starved_mid >> metis_tac[]
QED



Theorem asm_frame_call_prepare_failure_step_ok:
  asm_frame_rel prog data es0 a s /\
  s.contexts = (c,rb)::rest /\ next_opcode c = SOME op /\
  (op = Call \/ op = StaticCall) /\
  6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack /\
  asm_call_prepare op s = (INR e,t) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `?mr. c.msgParams.outputTo = Memory mr` by
    (fs[asm_frame_rel_def, asm_evm_rel_def] >>
     Cases_on `c.msgParams.outputTo` >> gvs[]) >>
  (Q.SUBGOAL_THEN `rest = [] \/ (?mr. c.msgParams.outputTo = Memory mr)`
     assume_tac >- metis_tac[]) >>
  drule_all asm_frame_call_prepare_failure_starved >>
  strip_tac >> simp[asm_frame_step_ok_def] >> metis_tac[]
QED

Theorem asm_frame_call_prepare_exit:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s = (INR e,t) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `c.stack = a.as_stack` by fs[asm_frame_rel_def, asm_evm_rel_def] >>
  Cases_on `6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack`
  >- (`asm_evm_rel (prog ++ [AsmDataItem data]) a s` by
        fs[asm_frame_rel_def] >>
      `next_opcode c = SOME op` by
        (drule_all asm_frame_call_decode >> simp[]) >>
      (Q.SUBGOAL_THEN `op = Call \/ op = StaticCall` assume_tac
        >- (Cases_on `EL a.as_pc prog = AsmOp "CALL"` >> gvs[])) >>
      drule_all asm_frame_call_prepare_failure_step_ok >> simp[]) >>
  Cases_on `EL a.as_pc prog = AsmOp "CALL"` >>
  gvs[call_has_value_def]
  >- (`LENGTH a.as_stack < 7` by simp[] >>
      drule asm_call_underflow >>
      disch_then (qspecl_then [`build_offset_to_pc prog`,
        `SND (compute_label_offsets prog)`] assume_tac) >>
      simp[asm_frame_step_ok_def]) >>
  `LENGTH a.as_stack < 6` by simp[] >>
  drule asm_staticcall_underflow >>
  disch_then (qspecl_then [`build_offset_to_pc prog`,
    `SND (compute_label_offsets prog)`] assume_tac) >>
  simp[asm_frame_step_ok_def]
QED

Theorem asm_expand_memory_nested[local]:
  asm_expand_memory n (asm_expand_memory m mem) =
    if m <= n then asm_expand_memory n mem else asm_expand_memory m mem
Proof
  `!a b. a <= b ==> (a + 31) DIV 32 * 32 <= (b + 31) DIV 32 * 32`
    by (rpt strip_tac >> simp[] >>
        irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >>
  Cases_on `m <= n`
  >- (first_x_assum drule >> strip_tac >>
      simp[asm_expand_eq_evm, APPEND_ASSOC] >>
      rw[arithmeticTheory.MAX_DEF] >>
      simp[REPLICATE_APPEND] >> gvs[] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  `n <= m` by simp[] >> first_x_assum drule >> strip_tac >>
  simp[asm_expand_eq_evm, APPEND_ASSOC] >>
  rw[arithmeticTheory.MAX_DEF] >> simp[REPLICATE_APPEND] >> gvs[] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

Theorem asm_call_memory_buffer_extend:
  max_expansion_range (ao,az) (ro,rs) = (off,sz) /\
  e = MAX (buffer_length mem)
        (if 0 < sz then word_size (off+sz) * 32 else 0) - buffer_length mem ==>
  buffer_to_list (buffer_extend e mem) =
    asm_call_memory ao az ro rs (buffer_to_list mem)
Proof
  Cases_on `az = 0` >> Cases_on `rs = 0` >>
  simp[max_expansion_range_def, asm_call_memory_def] >>
  rw[] >> gvs[buffer_to_list_extend, vfmConstantsTheory.word_size_def,
    asm_expand_memory_nested, asm_expand_eq_evm] >>
  IF_CASES_TAC >> gvs[] >>
  `ao + az = ro + rs` by decide_tac >>
  `ao + (az + 31) = ro + (rs + 31)` by decide_tac >> simp[]
QED

Theorem asm_call_memory_buffer_write:
  max_expansion_range (ao,az) (ro,rs) = (off,sz) /\
  e = MAX (buffer_length mem)
        (if 0 < sz then word_size (off+sz) * 32 else 0) - buffer_length mem ==>
  buffer_to_list (buffer_write ro (TAKE rs bytes) (buffer_extend e mem)) =
    TAKE ro (asm_call_memory ao az ro rs (buffer_to_list mem)) ++
    TAKE rs bytes ++
    DROP (ro + LENGTH (TAKE rs bytes))
      (asm_call_memory ao az ro rs (buffer_to_list mem))
Proof
  strip_tac >> drule_all asm_call_memory_buffer_extend >> strip_tac >>
  dep_rewrite.DEP_REWRITE_TAC[buffer_to_list_write_le] >> simp[] >>
  strip_tac >>
  `rs <> 0` by (Cases_on `rs` >> gvs[]) >>
  `ro <= LENGTH (asm_call_memory ao az ro rs (buffer_to_list mem))`
    by (simp[asm_call_memory_def] >>
        mp_tac (Q.SPECL [`ro + rs`,
          `if az = 0 then buffer_to_list mem
           else asm_expand_memory (ao + az) (buffer_to_list mem)`]
          spillSimTheory.asm_expand_memory_length) >> decide_tac) >>
  qpat_x_assum `buffer_to_list _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
  simp[] >> decide_tac
QED

Theorem asm_take_outcome_failed_head:
  take_outcome rq (failed_outcome rq :: os) = (failed_outcome rq,os)
Proof
  simp[take_outcome_def] >> Cases_on `computed_precompile rq` >> simp[] >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >> simp[] >>
  Cases_on `x` >> simp[]
QED

Theorem asm_message_prepare_abort_state:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall \/ op = DelegateCall) /\
  LENGTH c.stack <= stack_limit /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  ((lookup_account sender accounts).balance < value \/ 1024 < LENGTH s.contexts) ==>
  let vo = if call_has_value op then 1 else 0 in
  ?charge acc d'.
    stipend <= charge /\ c.gasUsed + charge <= c.msgParams.gasLimit /\
    step_call op s = (INL (), s with <| contexts :=
      (c with <| stack := 0w :: DROP (6 + vo) c.stack;
                  gasUsed := c.gasUsed + charge - stipend;
                  returnData := []; pc updated_by SUC;
                  memory := buffer_extend
                    (MAX (buffer_length c.memory)
                      (let range = max_expansion_range (ao,az) (ro,rs) in
                       if 0 < SND range then word_size (FST range + SND range) * 32 else 0)
                     - buffer_length c.memory) c.memory |>,rb)::rest;
      rollback := s.rollback with accesses := acc;
      msdomain := Collect d' |>)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_message_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `buffer_extend expansion c.memory` >>
  qexistsl_tac [`charge`,`acc`,`d'`] >>
  qpat_assum `stipend <= charge` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `c.gasUsed + charge <= _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qabbrev_tac `prepared = c with <|
    stack := DROP (6 + (if call_has_value op then 1 else 0)) c.stack;
    gasUsed := c.gasUsed + charge; memory := buffer_extend expansion c.memory |>` >>
  `u.contexts = (prepared,rb)::rest` by simp[Abbr `prepared`] >>
  `LENGTH prepared.stack < stack_limit` by
    (fs[Abbr `prepared`, vfmConstantsTheory.stack_limit_def] >> decide_tac) >>
  `stipend <= prepared.gasUsed` by (simp[Abbr `prepared`] >> decide_tac) >>
  `asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (), u with contexts :=
      (prepared with <| stack := 0w :: prepared.stack; returnData := [];
        gasUsed := prepared.gasUsed - stipend; pc updated_by SUC |>,rb)::rest)` by
    (`LENGTH u.contexts = LENGTH s.contexts` by simp[] >>
     Cases_on `(lookup_account sender accounts).balance < value`
     >- (drule_all asm_call_finish_balance >>
         disch_then (fn th => simp_tac (srw_ss()) [th])) >>
     `value <= (lookup_account sender accounts).balance` by decide_tac >>
     `1024 < LENGTH u.contexts` by metis_tac[] >>
     drule_all asm_call_finish_depth >>
     disch_then (fn th => simp_tac (srw_ss()) [th])) >>
  rewrite_tac[asm_step_call_factor, Once bind_def] >>
  qpat_assum `asm_call_prepare _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `asm_call_finish _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `u = _` (fn th => pure_rewrite_tac[th]) >>
  simp[Abbr `prepared`]
QED

Theorem asm_call_prepare_abort_state:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  LENGTH c.stack <= stack_limit /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  ((lookup_account sender accounts).balance < value \/ 1024 < LENGTH s.contexts) ==>
  let vo = if call_has_value op then 1 else 0 in
  ?charge acc d'.
    stipend <= charge /\ c.gasUsed + charge <= c.msgParams.gasLimit /\
    step_call op s = (INL (), s with <| contexts :=
      (c with <| stack := 0w :: DROP (6 + vo) c.stack;
                  gasUsed := c.gasUsed + charge - stipend;
                  returnData := []; pc updated_by SUC;
                  memory := buffer_extend
                    (MAX (buffer_length c.memory)
                      (let range = max_expansion_range (ao,az) (ro,rs) in
                       if 0 < SND range then word_size (FST range + SND range) * 32 else 0)
                     - buffer_length c.memory) c.memory |>,rb)::rest;
      rollback := s.rollback with accesses := acc;
      msdomain := Collect d' |>)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  irule asm_message_prepare_abort_state >> fs[] >> metis_tac[]
QED

Theorem asm_message_step_success:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall \/ op = DelegateCall) /\
  step_call op s = (INL (),v) ==>
  step s = (INL (),v)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `FLOOKUP c.msgParams.parsed c.pc = SOME op` by
    (qpat_x_assum `next_opcode c = _` mp_tac >>
     simp[next_opcode_def] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  simp_tac (srw_ss()) [step_def, get_current_context_def, handle_def,
    bind_def, ignore_bind_def, return_def] >>
  qpat_assum `s.contexts = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  qpat_assum `FLOOKUP _ _ = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `op = Call \/ op = StaticCall \/ op = DelegateCall` strip_assume_tac >>
  gvs[step_inst_def, inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, return_def]
QED

Theorem asm_call_step_success:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall) /\
  step_call op s = (INL (),v) ==>
  step s = (INL (),v)
Proof
  strip_tac >> irule asm_message_step_success >> simp[] >> metis_tac[]
QED

Theorem asm_call_abort_outcome:
  s.contexts = (c,rb)::rest /\ t.contexts = (c',rb)::rest /\
  c'.stack = 0w::stk /\ c'.returnData = [] /\ c'.logs = c.logs /\
  t.rollback.accounts = s.rollback.accounts /\
  t.rollback.tStorage = s.rollback.tStorage /\
  t.rollback.toDelete = s.rollback.toDelete /\
  (next_opcode c = SOME Call \/ next_opcode c = SOME StaticCall) ==>
  outcome_of (request_of s).cr_kind t (LENGTH c.logs) (LENGTH s.rollback.toDelete) =
    failed_outcome (request_of s)
Proof
  strip_tac >>
  simp[outcome_of_def, request_of_def, failed_outcome_def]
QED

Theorem asm_consume_call_failed:
  a.as_outcomes = failed_outcome rq :: os /\ rq.cr_kind = MessageCall ==>
  asm_consume_call_outcome rq ro rs stk a =
    AsmOK (asm_next (a with <|
      as_stack := 0w::stk; as_outcomes := os;
      as_requests := record_request rq a.as_requests;
      as_returndata := [] |>))
Proof
  strip_tac >>
  simp[asm_consume_call_outcome_eq, asm_take_outcome_failed_head] >>
  simp[failed_outcome_def, adopt_outcome_def, adopt_outcome_deletions_def,
       TAKE_DROP] >>
  AP_TERM_TAC >> simp[asm_state_component_equality]
QED

Theorem asm_frame_call_abort_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  ((lookup_account sender accounts).balance < value \/ 1024 < LENGTH s.contexts) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\ wf_state s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  `LENGTH c.stack <= stack_limit` by
    (gvs[wf_state_def, wf_context_def]) >>
  (Q.SUBGOAL_THEN `op = Call \/ op = StaticCall` assume_tac >- metis_tac[]) >>
  `next_opcode c = SOME op` by
    (drule_all asm_frame_call_decode >> simp[] >> metis_tac[]) >>
  drule_at (Pat `asm_call_prepare _ _ = _`) asm_call_prepare_abort_state >>
  disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[])) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_call op s = (INL (),t)` >>
  `step s = (INL (),t)` by (irule asm_call_step_success >> metis_tac[]) >>
  `LENGTH t.contexts = LENGTH s.contexts` by simp[Abbr `t`] >>
  `run_call t = run_call s` by metis_tac[run_call_same_depth_step] >>
  `wf_state t` by
    (drule step_preserves_wf_state >> simp[]) >>
  `6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack` by
    (drule_all asm_call_prepare_success_stack >> simp[]) >>
  `observable_call c` by
    (simp[observable_call_def] >>
     Cases_on `op = Call` >> gvs[call_has_value_def]) >>
  drule frame_obs_call_same_depth >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `outcome_of (request_of s).cr_kind t (LENGTH c.logs)
     (LENGTH s.rollback.toDelete) = failed_outcome (request_of s)` by
    (irule asm_call_abort_outcome >>
     simp[Abbr `t`] >> metis_tac[]) >>
  suspend "restore"
QED

Resume asm_frame_call_abort_step[restore]:
  rpt strip_tac >>
  drule_at (Pat `asm_call_prepare _ _ = _`) asm_call_prepare_success_view >>
  disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `u = _` kall_tac >>
  `c.stack = a.as_stack /\ ~a.as_call_ctx.cc_static` by gvs[asm_evm_rel_def] >>
  `a.as_outcomes = failed_outcome (request_of s) :: MAP SND (call_trace t)` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `(request_of s).cr_kind = MessageCall` by
    (Cases_on `EL a.as_pc prog = AsmOp "CALL"` >> gvs[request_of_def]) >>
  `6 <= LENGTH a.as_stack` by
    (qpat_x_assum `6 + _ <= LENGTH _` mp_tac >> simp[] >> decide_tac) >>
  `?gas addr x y z w stk. a.as_stack = gas::addr::x::y::z::w::stk` by
    (qpat_x_assum `6 <= LENGTH a.as_stack` mp_tac >>
     namedCases_on `a.as_stack` ["", "gas t1"] >> simp[] >>
     namedCases_on `t1` ["", "addr t2"] >> simp[] >>
     namedCases_on `t2` ["", "x t3"] >> simp[] >>
     namedCases_on `t3` ["", "y t4"] >> simp[] >>
     namedCases_on `t4` ["", "z t5"] >> simp[] >>
     namedCases_on `t5` ["", "w stk"] >> simp[]) >>
  qpat_x_assum `asm_call_prepare _ _ = _` kall_tac >>
  qpat_x_assum `(lookup_account _ _).balance < _ \/ _` kall_tac >>
  qpat_x_assum `step_call _ _ = _` kall_tac >>
  qpat_x_assum `sender = _` kall_tac >>
  qpat_x_assum `accounts = _` kall_tac >>
  qpat_x_assum `address = _` kall_tac >>
  qpat_x_assum `value = _` kall_tac >>
  suspend "assembly"
QED

Resume asm_frame_call_abort_step[assembly]:
  `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     (EL a.as_pc prog) a =
   AsmOK (asm_next (a with <|
     as_memory := asm_call_memory ao az ro rs a.as_memory;
     as_stack := 0w::DROP (6 + (if call_has_value op then 1 else 0)) a.as_stack;
     as_outcomes := MAP SND (call_trace t);
     as_requests := record_request (request_of s) a.as_requests;
     as_returndata := [] |>))` by
    (Cases_on `EL a.as_pc prog = AsmOp "CALL"`
     >- (qpat_x_assum `Abbrev (t = _)` kall_tac >>
         gvs[call_has_value_def] >>
         namedCases_on `stk` ["", "rsw tail"] >> gvs[] >>
         drule_all asm_frame_call_request >> disch_tac >>
         simp[asm_step_call_staticcall_gas, asm_exec_call_def] >>
         qmatch_goalsub_abbrev_tac `asm_consume_call_outcome _ _ _ _ b` >>
         `b.as_outcomes = failed_outcome (request_of s) :: MAP SND (call_trace t)`
           by simp[Abbr `b`] >>
         drule_all asm_consume_call_failed >>
         disch_then (fn th => rewrite_tac[th]) >> simp[Abbr `b`]) >>
     qpat_x_assum `Abbrev (t = _)` kall_tac >>
     gvs[call_has_value_def] >>
     drule_all asm_frame_staticcall_request >> disch_tac >>
     simp[asm_step_call_staticcall_gas, asm_exec_staticcall_def] >>
     qmatch_goalsub_abbrev_tac `asm_consume_call_outcome _ _ _ _ b` >>
     `b.as_outcomes = failed_outcome (request_of s) :: MAP SND (call_trace t)`
       by simp[Abbr `b`] >>
     drule_all asm_consume_call_failed >>
     disch_then (fn th => rewrite_tac[th]) >> simp[Abbr `b`]) >>
  suspend "relation"
QED

Resume asm_frame_call_abort_step[relation]:
  map_every (fn q => qpat_x_assum q kall_tac)
    [`ao = _`, `az = _`, `ro = _`, `rs = _`,
     `a.as_stack = _`, `op = (if _ then _ else _)`] >>
  `buffer_to_list c.memory = a.as_memory` by gvs[asm_evm_rel_def] >>
  `buffer_to_list (FST (HD t.contexts)).memory =
     asm_call_memory ao az ro rs a.as_memory` by
    (qpat_x_assum `Abbrev (t = _)`
       (fn th => pure_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     simp_tac (srw_ss()) [] >>
     qpat_x_assum `buffer_to_list c.memory = _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     Cases_on `max_expansion_range (ao,az) (ro,rs)` >>
     rename1 `max_expansion_range (ao,az) (ro,rs) = (off,sz)` >>
     simp_tac (srw_ss()) [] >>
     irule asm_call_memory_buffer_extend >>
     qexistsl_tac [`off`,`sz`] >> simp_tac (srw_ss()) [] >>
     first_assum ACCEPT_TAC) >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
   asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1` by
    (`a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
     drule asm_pc_to_offset_suc >>
     simp[arithmeticTheory.ADD1, EL_APPEND1] >>
     Cases_on `EL a.as_pc prog = AsmOp "CALL"` >>
     gvs[asm_inst_size_def]) >>
  `record_request (request_of s) a.as_requests ++ call_requests t =
     call_requests es0` by
    (fs[asm_frame_rel_def, call_requests_def, record_request_def] >>
     gvs[] >> IF_CASES_TAC >> gvs[]) >>
  qpat_x_assum `Abbrev (t = _)` mp_tac >>
  qmatch_goalsub_abbrev_tac `(ct,rb)::rest` >> disch_tac >>
  `t.contexts = (ct,rb)::rest /\ t.txParams = s.txParams /\
   t.msdomain = Collect d' /\
   t.rollback.accounts = s.rollback.accounts /\
   t.rollback.tStorage = s.rollback.tStorage /\
   t.rollback.toDelete = s.rollback.toDelete` by simp[Abbr `t`] >>
  qpat_x_assum `Abbrev (t = _)` kall_tac >>
  `ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\
   ct.pc = SUC c.pc /\ ct.logs = c.logs /\ ct.returnData = [] /\
   ct.stack = 0w::DROP (6 + (if call_has_value op then 1 else 0)) c.stack` by
    simp[Abbr `ct`] >>
  qpat_x_assum `Abbrev (ct = _)` kall_tac >>
  simp[asm_frame_step_ok_def] >> disj2_tac >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `asm_frame_rel prog data es0 a s` mp_tac >>
  rewrite_tac[asm_frame_rel_def] >> strip_tac >>
  gvs[] >> simp[asm_next_def] >>
  gvs[asm_evm_rel_def, asm_next_def]
QED

Finalise asm_frame_call_abort_step

Theorem asm_frame_call_consume:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL a.as_pc prog) a =
  asm_consume_call_outcome (request_of s) ro rs
    (DROP (6 + (if call_has_value op then 1 else 0)) a.as_stack)
    (a with as_memory := asm_call_memory ao az ro rs a.as_memory)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  (Q.SUBGOAL_THEN `op = Call \/ op = StaticCall` assume_tac
    >- (Cases_on `EL a.as_pc prog = AsmOp "CALL"` >> gvs[])) >>
  drule_at (Pat `asm_call_prepare _ _ = _`) asm_call_prepare_success_view >>
  disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `u = _` kall_tac >>
  `c.stack = a.as_stack /\ ~a.as_call_ctx.cc_static` by gvs[asm_evm_rel_def] >>
  `6 <= LENGTH a.as_stack` by
    (qpat_x_assum `6 + _ <= LENGTH _` mp_tac >> simp[] >> decide_tac) >>
  `?gas addr x y z w stk. a.as_stack = gas::addr::x::y::z::w::stk` by
    (qpat_x_assum `6 <= LENGTH a.as_stack` mp_tac >>
     namedCases_on `a.as_stack` ["", "gas t1"] >> simp[] >>
     namedCases_on `t1` ["", "addr t2"] >> simp[] >>
     namedCases_on `t2` ["", "x t3"] >> simp[] >>
     namedCases_on `t3` ["", "y t4"] >> simp[] >>
     namedCases_on `t4` ["", "z t5"] >> simp[] >>
     namedCases_on `t5` ["", "w stk"] >> simp[]) >>
  Cases_on `EL a.as_pc prog = AsmOp "CALL"`
  >- (gvs[call_has_value_def] >>
      namedCases_on `stk` ["", "rsw tail"] >> gvs[] >>
      drule_all asm_frame_call_request >> disch_tac >>
      simp[asm_step_call_staticcall_gas, asm_exec_call_def]) >>
  gvs[call_has_value_def] >>
  drule_all asm_frame_staticcall_request >> disch_tac >>
  simp[asm_step_call_staticcall_gas, asm_exec_staticcall_def]
QED

Theorem asm_frame_outcome_effects_restore:
  asm_frame_rel prog data es0 a s /\ a.as_pc < LENGTH prog /\
  asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
    asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1 /\
  s.contexts = (c,rb)::rest /\ t.contexts = (ct,rb)::rest /\
  wf_state t /\ t.txParams = s.txParams /\ (?d. t.msdomain = Collect d) /\
  ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\
  ct.pc = SUC c.pc /\
  take_outcome (request_of s) a.as_outcomes = (out,MAP SND (call_trace t)) /\
  gas_readings t = gas_readings s /\
  record_request (request_of s) a.as_requests ++ call_requests t = call_requests es0 /\
  mem = asm_call_memory ao az ro rs a.as_memory /\
  ct.stack = (if out.co_success then 1w else 0w)::
    DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
  ct.returnData = out.co_returnData /\
  buffer_to_list ct.memory = TAKE ro mem ++ TAKE rs out.co_returnData ++
    DROP (ro + LENGTH (TAKE rs out.co_returnData)) mem /\
  adopt_outcome (request_of s) out (a.as_accounts,a.as_transient,a.as_logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
  adopt_outcome_deletions (request_of s) out a.as_pending_deletions =
    t.rollback.toDelete /\
  asm_consume_call_outcome (request_of s) ro rs
    (DROP (6 + (if call_has_value op then 1 else 0)) a.as_stack)
    (a with as_memory := mem) = AsmOK a1 ==>
  asm_frame_rel prog data es0 a1 t
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  qpat_x_assum `asm_consume_call_outcome _ _ _ _ _ = _` mp_tac >>
  simp[asm_consume_call_outcome_eq] >> strip_tac >>
  qpat_x_assum `asm_frame_rel prog data es0 a s` mp_tac >>
  rewrite_tac[asm_frame_rel_def] >> strip_tac >>
  gvs[] >> simp[asm_frame_rel_def, asm_next_def] >>
  gvs[asm_evm_rel_def, asm_next_def]
QED

Theorem asm_frame_call_effects_restore:
  asm_frame_rel prog data es0 a s /\ a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\ t.contexts = (ct,rb)::rest /\
  wf_state t /\ t.txParams = s.txParams /\ (?d. t.msdomain = Collect d) /\
  ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\
  ct.pc = SUC c.pc /\
  take_outcome (request_of s) a.as_outcomes = (out,MAP SND (call_trace t)) /\
  gas_readings t = gas_readings s /\
  record_request (request_of s) a.as_requests ++ call_requests t = call_requests es0 /\
  mem = asm_call_memory ao az ro rs a.as_memory /\
  ct.stack = (if out.co_success then 1w else 0w)::
    DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
  ct.returnData = out.co_returnData /\
  buffer_to_list ct.memory = TAKE ro mem ++ TAKE rs out.co_returnData ++
    DROP (ro + LENGTH (TAKE rs out.co_returnData)) mem /\
  adopt_outcome (request_of s) out (a.as_accounts,a.as_transient,a.as_logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
  adopt_outcome_deletions (request_of s) out a.as_pending_deletions =
    t.rollback.toDelete /\
  asm_consume_call_outcome (request_of s) ro rs
    (DROP (6 + (if call_has_value op then 1 else 0)) a.as_stack)
    (a with as_memory := mem) = AsmOK a1 ==>
  asm_frame_rel prog data es0 a1 t
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
   asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1` by
    (`a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
     drule asm_pc_to_offset_suc >>
     simp[arithmeticTheory.ADD1, EL_APPEND1] >>
     Cases_on `EL a.as_pc prog = AsmOp "CALL"` >>
     gvs[asm_inst_size_def]) >>
  drule_all asm_frame_outcome_effects_restore >> simp[]
QED

Theorem asm_frame_outcome_effects_step_ok:
  asm_frame_rel prog data es0 a s /\ a.as_pc < LENGTH prog /\
  asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
    asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1 /\
  s.contexts = (c,rb)::rest /\ t.contexts = (ct,rb)::rest /\
  run_call t = run_call s /\
  wf_state t /\ t.txParams = s.txParams /\ (?d. t.msdomain = Collect d) /\
  ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\
  ct.pc = SUC c.pc /\
  take_outcome (request_of s) a.as_outcomes = (out,MAP SND (call_trace t)) /\
  gas_readings t = gas_readings s /\
  record_request (request_of s) a.as_requests ++ call_requests t = call_requests es0 /\
  mem = asm_call_memory ao az ro rs a.as_memory /\
  ct.stack = (if out.co_success then 1w else 0w)::
    DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
  ct.returnData = out.co_returnData /\
  buffer_to_list ct.memory = TAKE ro mem ++ TAKE rs out.co_returnData ++
    DROP (ro + LENGTH (TAKE rs out.co_returnData)) mem /\
  adopt_outcome (request_of s) out (a.as_accounts,a.as_transient,a.as_logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
  adopt_outcome_deletions (request_of s) out a.as_pending_deletions =
    t.rollback.toDelete /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (EL a.as_pc prog) a =
    asm_consume_call_outcome (request_of s) ro rs
      (DROP (6 + (if call_has_value op then 1 else 0)) a.as_stack)
      (a with as_memory := mem) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `?a1. asm_consume_call_outcome (request_of s) ro rs
    (DROP (6 + (if call_has_value op then 1 else 0)) a.as_stack)
    (a with as_memory := mem) = AsmOK a1` by
    simp[asm_consume_call_outcome_eq] >>
  drule_all asm_frame_outcome_effects_restore >> disch_tac >>
  pure_rewrite_tac[asm_frame_step_ok_def] >> disj2_tac >>
  gvs[] >> qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem asm_frame_call_effects_step_ok:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\ t.contexts = (ct,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  run_call t = run_call s /\
  wf_state t /\ t.txParams = s.txParams /\ (?d. t.msdomain = Collect d) /\
  ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\
  ct.pc = SUC c.pc /\
  take_outcome (request_of s) a.as_outcomes = (out,MAP SND (call_trace t)) /\
  gas_readings t = gas_readings s /\
  record_request (request_of s) a.as_requests ++ call_requests t = call_requests es0 /\
  mem = asm_call_memory ao az ro rs a.as_memory /\
  ct.stack = (if out.co_success then 1w else 0w)::
    DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
  ct.returnData = out.co_returnData /\
  buffer_to_list ct.memory = TAKE ro mem ++ TAKE rs out.co_returnData ++
    DROP (ro + LENGTH (TAKE rs out.co_returnData)) mem /\
  adopt_outcome (request_of s) out (a.as_accounts,a.as_transient,a.as_logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
  adopt_outcome_deletions (request_of s) out a.as_pending_deletions =
    t.rollback.toDelete ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_frame_call_consume >> disch_tac >>
  `asm_pc_to_offset (prog ++ [AsmDataItem data]) (a.as_pc + 1) =
   asm_pc_to_offset (prog ++ [AsmDataItem data]) a.as_pc + 1` by
    (`a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
     drule asm_pc_to_offset_suc >>
     simp[arithmeticTheory.ADD1, EL_APPEND1] >>
     Cases_on `EL a.as_pc prog = AsmOp "CALL"` >>
     gvs[asm_inst_size_def]) >>
  qpat_x_assum `mem = _` SUBST_ALL_TAC >>
  `asm_call_memory ao az ro rs a.as_memory =
   asm_call_memory ao az ro rs a.as_memory` by simp[] >>
  drule_all asm_frame_outcome_effects_step_ok >> simp[]
QED

Theorem asm_take_outcome_result_agrees:
  (~observed.co_success ==> observed.co_returnData = []) /\
  (computed_precompile rq /\ observed.co_success ==>
    precompile_result rq.cr_target rq.cr_data = SOME (SOME observed.co_returnData)) ==>
  (FST (take_outcome rq (observed::tail))).co_success = observed.co_success /\
  (FST (take_outcome rq (observed::tail))).co_returnData = observed.co_returnData
Proof
  strip_tac >> Cases_on `computed_precompile rq`
  >- (Cases_on `observed.co_success`
      >- (gvs[] >> simp[take_outcome_def, failed_outcome_def]) >>
      gvs[take_outcome_def] >>
      Cases_on `precompile_result rq.cr_target rq.cr_data` >>
      simp[failed_outcome_def] >>
      rename1 `SOME result` >> Cases_on `result` >> simp[failed_outcome_def]) >>
  simp[take_outcome_def]
QED

Theorem asm_buffer_take_extend_read:
  (az = 0 \/ ao + az <= buffer_length mem + n) ==>
  buffer_take ao az (buffer_extend n mem) = buffer_read ao az mem
Proof
  strip_tac >> Cases_on `az = 0` >> simp[buffer_take_to_list, buffer_read_to_list] >>
  gvs[] >>
  simp[buffer_to_list_extend, take_pad_0_def, PAD_RIGHT, GSYM REPLICATE_GENLIST] >>
  irule LIST_EQ >>
  simp[LENGTH_TAKE_EQ, EL_TAKE, EL_DROP, EL_APPEND_EQN, EL_REPLICATE] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[EL_DROP]
QED

Theorem asm_call_expanded_input:
  max_expansion_range (ao,az) (ro,rs) = (off,sz) /\
  n = MAX (buffer_length mem)
        (if 0 < sz then word_size (off+sz) * 32 else 0) - buffer_length mem ==>
  buffer_take ao az (buffer_extend n mem) = buffer_read ao az mem
Proof
  strip_tac >> irule asm_buffer_take_extend_read >>
  Cases_on `az = 0` >> simp[] >>
  mp_tac (Q.SPEC `off+sz` spillSimTheory.n_le_round_up_32) >>
  gvs[max_expansion_range_def, vfmConstantsTheory.word_size_def] >>
  Cases_on `rs = 0` >> gvs[] >>
  Cases_on `ao + az < ro + rs` >> gvs[] >>
  rpt strip_tac >> gvs[] >> rw[arithmeticTheory.MAX_DEF] >> decide_tac
QED

Theorem asm_call_prepared_input:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  buffer_take ao az (FST (HD u.contexts)).memory = buffer_read ao az c.memory
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_assum `u = _` (fn th => rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >>
  Cases_on `max_expansion_range (ao,az) (ro,rs)` >>
  rename1 `max_expansion_range (ao,az) (ro,rs) = (off,sz)` >>
  simp_tac (srw_ss()) [] >>
  irule asm_call_expanded_input >>
  goal_assum (drule_at Any) >> simp_tac (srw_ss()) []
QED

Theorem asm_call_prepared_request:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  next_opcode c = SOME op /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  (request_of s).cr_kind = MessageCall /\
  (request_of s).cr_target = address /\ (request_of s).cr_value = value /\
  (request_of s).cr_data = buffer_read ao az c.memory /\
  (request_of s).cr_static = (op = StaticCall) /\
  (request_of s).cr_accounts = s.rollback.accounts /\
  (request_of s).cr_tStorage = s.rollback.tStorage
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  Cases_on `op = Call` >> gvs[call_has_value_def, request_of_def, EL_TAKE]
QED

Theorem asm_call_prepared_enter_ordinary:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  next_opcode c = SOME op /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (),v) ==>
  ~computed_precompile (request_of s)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepared_request >> strip_tac >>
  drule_all asm_call_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `u = s with <| contexts := (parent,rb)::rest;
    rollback := _; msdomain := _ |>` >>
  `u.contexts = (parent,rb)::rest` by simp[] >>
  `LENGTH u.contexts <= 1024` by
    (qpat_x_assum `LENGTH s.contexts <= 1024` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  drule_all asm_call_finish_proceed >>
  disch_then (fn th => qpat_assum `asm_call_finish _ _ _ = _` mp_tac >>
    rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `proceed_call _ _ _ _ _ _ _ _ _ p` >> disch_tac >>
  `p.contexts <> []` by simp[Abbr `p`] >>
  drule_all vfmRunCallTheory.proceed_call_inl_nonprecompile >>
  gvs[computed_precompile_addresses, vfmContextTheory.precompile_addresses_def,
      finite_setTheory.fIN_fset_ABS]
QED

Theorem asm_call_prepared_enter_take_outcome:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  next_opcode c = SOME op /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (),v) ==>
  take_outcome (request_of s) (outcome_of kind t n m::outcomes) =
    (outcome_of kind t n m,outcomes) /\
  record_request (request_of s) requests = requests ++ [request_of s]
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepared_enter_ordinary >>
  metis_tac[take_outcome_ordinary]
QED

Theorem asm_computed_proceed_success:
  s.contexts = (c,rb)::rest /\ (op = Call \/ op = StaticCall) /\
  (address = 1w \/ address = 2w \/ address = 6w \/ address = 7w) /\
  proceed_call op sender address 0 ao az code stipend outputTo s = (INR NONE,t) ==>
  precompile_result address (buffer_take ao az c.memory) =
    SOME (SOME (FST (HD t.contexts)).returnData) /\
  t.rollback = s.rollback /\ (FST (HD t.contexts)).logs = []
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `fIN address precompile_addresses` by
    gvs[vfmContextTheory.precompile_addresses_def, finite_setTheory.fIN_fset_ABS] >>
  qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, bind_def, ignore_bind_def, get_rollback_def,
       read_memory_def, get_current_context_def, get_caller_def, get_value_def,
       get_static_def, return_def, push_context_def] >>
  qmatch_goalsub_abbrev_tac `dispatch_precompiles address pushed` >>
  disch_tac >>
  qmatch_assum_abbrev_tac `Abbrev (pushed = s with contexts updated_by CONS (child,s.rollback))` >>
  `pushed.contexts = (child,s.rollback)::(c,rb)::rest /\ child.returnData = []` by
    simp[Abbr `pushed`, Abbr `child`, vfmContextTheory.initial_context_def] >>
  drule_all asm_computed_precompile_success >>
  simp[Abbr `pushed`, Abbr `child`, vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def]
QED

Theorem asm_call_computed_finish_success:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  next_opcode c = SOME op /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  computed_precompile (request_of s) /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR NONE,v) ==>
  precompile_result (request_of s).cr_target (request_of s).cr_data =
    SOME (SOME (FST (HD v.contexts)).returnData) /\
  v.rollback = u.rollback /\ (FST (HD v.contexts)).logs = []
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepared_request >> strip_tac >>
  drule_all asm_call_prepared_input >> disch_tac >>
  `value = 0` by fs[computed_precompile_addresses] >>
  (Q.SUBGOAL_THEN `address = 1w \/ address = 2w \/ address = 6w \/ address = 7w`
    assume_tac >- fs[computed_precompile_addresses]) >>
  drule_all asm_call_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `u = s with <| contexts := (parent,rb)::rest;
    rollback := _; msdomain := _ |>` >>
  `u.contexts = (parent,rb)::rest` by simp[] >>
  `LENGTH u.contexts <= 1024` by
    (qpat_x_assum `LENGTH s.contexts <= 1024` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  drule_all asm_call_finish_proceed >>
  disch_then (fn th => qpat_assum `asm_call_finish _ _ _ = _` mp_tac >>
    rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `proceed_call _ _ _ _ _ _ _ _ _ p` >> disch_tac >>
  `p.contexts = (parent with returnData := [],rb)::rest` by simp[Abbr `p`] >>
  qpat_x_assum `value = 0` SUBST_ALL_TAC >>
  drule_all asm_computed_proceed_success >> strip_tac >>
  gvs[Abbr `p`]
QED

Theorem asm_proceed_call_saved_checkpoint:
  s.contexts <> [] /\
  proceed_call op sender address value ao az code stipend outputTo s = (r,t) ==>
  SND (HD t.contexts) = s.rollback /\ t.txParams = s.txParams /\
  msdomain_compatible s.msdomain t.msdomain
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, update_accounts_def,
       push_context_def, get_current_context_def, return_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  Cases_on `fIN address precompile_addresses` >> simp[return_def] >>
  strip_tac >> gvs[update_accounts_def, get_current_context_def, return_def] >>
  qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed` >>
  `pushed.contexts <> []` by simp[Abbr `pushed`] >>
  qspec_then `address` mp_tac
    (GEN_ALL (INST_TYPE [alpha |-> ``:unit``]
      vfmSameFrameTheory.preserves_same_frame_dispatch_precompiles)) >>
  rewrite_tac[vfmSameFrameTheory.preserves_same_frame_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[vfmSameFrameTheory.same_frame_rel_def, Abbr `pushed`]
QED

Theorem asm_proceed_call_terminal_kind:
  s.contexts <> [] /\
  proceed_call op sender address value ao az code stipend outputTo s = (INR e,t) ==>
  ~vfm_abort e /\ e <> SOME Reverted
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, update_accounts_def,
       push_context_def, get_current_context_def, return_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  Cases_on `fIN address precompile_addresses` >> simp[return_def] >>
  strip_tac >> gvs[update_accounts_def, get_current_context_def, return_def] >>
  qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed` >>
  `pushed.contexts <> []` by simp[Abbr `pushed`] >>
  drule_all dispatch_precompiles_inr_not_reverted_not_abort >> simp[]
QED

Theorem asm_proceed_call_zero_terminal_effects:
  s.contexts <> [] /\
  proceed_call op sender address 0 ao az code stipend outputTo s = (INR e,t) ==>
  t.rollback.accounts = s.rollback.accounts /\
  t.rollback.tStorage = s.rollback.tStorage /\
  t.rollback.toDelete = s.rollback.toDelete /\
  (FST (HD t.contexts)).logs = []
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, push_context_def,
       get_current_context_def, return_def] >>
  Cases_on `fIN address precompile_addresses` >> simp[return_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed` >>
  `pushed.contexts <> []` by simp[Abbr `pushed`] >>
  qspec_then `address` mp_tac
    (GEN_ALL (INST_TYPE [alpha |-> ``:unit``]
      vfmStaticCallsTheory.cp_dispatch_precompiles)) >>
  rewrite_tac[vfmStaticCallsTheory.cp_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[Abbr `pushed`, vfmContextTheory.initial_context_def]
QED

Theorem asm_proceed_call_terminal_effects:
  s.contexts <> [] /\
  proceed_call op sender address value ao az code stipend outputTo s = (INR e,t) ==>
  t.rollback.toDelete = s.rollback.toDelete /\
  (FST (HD t.contexts)).logs = []
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, update_accounts_def, push_context_def,
       get_current_context_def, return_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  Cases_on `fIN address precompile_addresses` >> simp[return_def] >> strip_tac >>
  gvs[update_accounts_def, get_current_context_def, return_def] >>
  qmatch_asmsub_abbrev_tac `dispatch_precompiles address pushed` >>
  `pushed.contexts <> []` by simp[Abbr `pushed`] >>
  qspec_then `address` mp_tac
    (GEN_ALL (INST_TYPE [alpha |-> ``:unit``]
      vfmStaticCallsTheory.cp_dispatch_precompiles)) >>
  rewrite_tac[vfmStaticCallsTheory.cp_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  gvs[Abbr `pushed`, vfmContextTheory.initial_context_def]
QED

Theorem asm_call_finish_terminal_kind:
  u.contexts = (c,rb)::rest /\
  value <= (lookup_account sender accounts).balance /\
  LENGTH u.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR e,t) ==>
  ~vfm_abort e /\ e <> SOME Reverted
Proof
  strip_tac >> drule_all asm_call_finish_proceed >>
  disch_then (fn th => qpat_x_assum `asm_call_finish _ _ _ = _` mp_tac >>
    rewrite_tac[th]) >> strip_tac >>
  irule asm_proceed_call_terminal_kind >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem asm_message_prepared_terminal_kind:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall \/ op = DelegateCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR e,t) ==>
  ~vfm_abort e /\ e <> SOME Reverted
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_message_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `u = s with <| contexts := (parent,rb)::rest;
    rollback := _; msdomain := _ |>` >>
  `u.contexts = (parent,rb)::rest` by simp[] >>
  `LENGTH u.contexts <= 1024` by
    (qpat_x_assum `LENGTH s.contexts <= 1024` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  drule_all asm_call_finish_terminal_kind >> simp[]
QED

Theorem asm_call_prepared_terminal_kind:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR e,t) ==>
  ~vfm_abort e /\ e <> SOME Reverted
Proof
  strip_tac >> irule asm_message_prepared_terminal_kind >> simp[] >> metis_tac[]
QED

Theorem asm_frame_call_same_depth_transport:
  asm_frame_rel prog data es0 a s /\ s.contexts = (c,rb)::rest /\
  step s = (INL (),t) /\ LENGTH t.contexts = LENGTH s.contexts /\
  observable_call c ==>
  let observed = outcome_of (request_of s).cr_kind t
        (LENGTH c.logs) (LENGTH s.rollback.toDelete) in
  a.as_outcomes = observed::MAP SND (call_trace t) /\
  gas_readings t = gas_readings s /\
  record_request (request_of s) a.as_requests ++ call_requests t = call_requests es0 /\
  take_outcome (request_of s) a.as_outcomes =
    (FST (take_outcome (request_of s) (observed::MAP SND (call_trace t))),
     MAP SND (call_trace t))
Proof
  strip_tac >>
  drule frame_obs_call_same_depth >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `a.as_outcomes = outcome_of (request_of s).cr_kind t
      (LENGTH c.logs) (LENGTH s.rollback.toDelete)::MAP SND (call_trace t)` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `record_request (request_of s) a.as_requests ++ call_requests t =
     call_requests es0` by
    (fs[asm_frame_rel_def, call_requests_def, record_request_def] >>
     gvs[] >> IF_CASES_TAC >> gvs[]) >>
  simp[] >>
  qspecl_then [`request_of s`,`a.as_outcomes`] mp_tac (GEN_ALL take_outcome_rest) >>
  simp[] >> strip_tac >>
  metis_tac[pairTheory.PAIR]
QED

Theorem asm_frame_call_same_depth_effects_step_ok:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\ t.contexts = (ct,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  step s = (INL (),t) /\ observable_call c /\
  t.txParams = s.txParams /\ (?d. t.msdomain = Collect d) /\
  ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\ ct.pc = SUC c.pc /\
  out = FST (take_outcome (request_of s)
    (outcome_of (request_of s).cr_kind t (LENGTH c.logs)
      (LENGTH s.rollback.toDelete)::MAP SND (call_trace t))) /\
  ct.stack = (if out.co_success then 1w else 0w)::
    DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
  ct.returnData = out.co_returnData /\
  buffer_to_list ct.memory = TAKE ro (asm_call_memory ao az ro rs a.as_memory) ++
    TAKE rs out.co_returnData ++
    DROP (ro + LENGTH (TAKE rs out.co_returnData))
      (asm_call_memory ao az ro rs a.as_memory) /\
  adopt_outcome (request_of s) out (a.as_accounts,a.as_transient,a.as_logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
  adopt_outcome_deletions (request_of s) out a.as_pending_deletions =
    t.rollback.toDelete ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `wf_state s` by fs[asm_frame_rel_def] >>
  `LENGTH t.contexts = LENGTH s.contexts` by simp[] >>
  `run_call t = run_call s` by metis_tac[run_call_same_depth_step] >>
  `wf_state t` by (drule step_preserves_wf_state >> simp[]) >>
  drule_all asm_frame_call_same_depth_transport >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `take_outcome (request_of s) a.as_outcomes = (out,MAP SND (call_trace t))` by
    metis_tac[] >>
  `asm_call_memory ao az ro rs a.as_memory =
     asm_call_memory ao az ro rs a.as_memory` by simp[] >>
  drule_all asm_frame_call_effects_step_ok >> simp[]
QED

Theorem asm_frame_call_terminal_exception:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR (SOME exc),v) /\ exc <> Reverted /\ ~vfm_abort (SOME exc) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\ wf_state s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  (Q.SUBGOAL_THEN `op = Call \/ op = StaticCall` assume_tac >- metis_tac[]) >>
  `next_opcode c = SOME op` by
    (drule_all asm_frame_call_decode >> simp[] >> metis_tac[]) >>
  drule_at (Pat `asm_call_prepare _ _ = _`) asm_call_prepare_success_view >>
  disch_then (qspecl_then [`rest`,`rb`,`d`,`c`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `u = s with <| contexts := (parent,rb)::rest;
    rollback := _; msdomain := _ |>` >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`sender = _`, `accounts = _`, `address = _`, `value = _`,
     `ao = _`, `az = _`, `ro = _`, `rs = _`] >>
  `u.contexts = (parent,rb)::rest` by simp[] >>
  `LENGTH u.contexts <= 1024` by
    (qpat_x_assum `LENGTH s.contexts <= 1024` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  drule_all asm_call_finish_proceed >>
  disch_then (fn th => qpat_assum `asm_call_finish _ _ _ = _` mp_tac >>
    rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `proceed_call _ _ _ _ _ _ _ _ _ p` >>
  disch_tac >>
  `p.contexts = (parent with returnData := [],rb)::rest /\ p.contexts <> []` by
    simp[Abbr `p`] >>
  `EVERY (wf_context o FST) s.contexts` by fs[wf_state_def] >>
  `stipend <= parent.gasUsed /\ LENGTH parent.stack < stack_limit` by
    (drule_all asm_call_prepare_stack_room >>
     drule_all asm_call_prepare_stipend_paid >> simp[]) >>
  `step_call op s = (INR (SOME exc),v)` by
    (rewrite_tac[asm_step_call_factor, bind_def] >>
     qpat_assum `asm_call_prepare _ _ = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [] >>
     qpat_assum `asm_call_finish _ _ _ = _` (fn th => rewrite_tac[th])) >>
  `EVERY (wf_context o FST) p.contexts` by
    (drule_all asm_call_prepare_contexts_wf >>
     simp[Abbr `p`, wf_context_def]) >>
  ` (FST (HD v.contexts)).gasUsed <= (FST (HD v.contexts)).msgParams.gasLimit` by
    (drule_all asm_proceed_call_child_gas >> simp[]) >>
  `stipend <= (parent with returnData := []).gasUsed /\
   LENGTH (parent with returnData := []).stack < stack_limit` by
    fs[vfmConstantsTheory.stack_limit_def] >>
  drule_all asm_call_step_memory_exception >> strip_tac >>
  suspend "returned"
QED

Resume asm_frame_call_terminal_exception[returned]:
  drule_all asm_proceed_call_saved_checkpoint >> strip_tac >>
  `child_rb = s.rollback with accesses := acc /\
   v.txParams = s.txParams /\ (?dt. v.msdomain = Collect dt)` by
    (gvs[Abbr `p`, vfmSameFrameTheory.msdomain_compatible_def] >>
     Cases_on `v.msdomain` >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `step s = (INL (),t)` >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`asm_call_finish _ _ _ = _`, `proceed_call _ _ _ _ _ _ _ _ _ _ = _`,
     `step_call _ _ = _`, `EVERY _ p.contexts`,
     `stipend <= (parent with returnData := []).gasUsed`,
     `LENGTH (parent with returnData := []).stack < stack_limit`] >>
  `LENGTH t.contexts = LENGTH s.contexts` by simp[Abbr `t`] >>
  `run_call t = run_call s` by metis_tac[run_call_same_depth_step] >>
  `wf_state t` by (drule step_preserves_wf_state >> simp[]) >>
  `observable_call c` by
    (simp[observable_call_def] >> Cases_on `op = Call` >> gvs[call_has_value_def]) >>
  drule frame_obs_call_same_depth >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `outcome_of (request_of s).cr_kind t (LENGTH c.logs)
     (LENGTH s.rollback.toDelete) = failed_outcome (request_of s)` by
    (irule asm_call_abort_outcome >>
     simp[Abbr `t`, Abbr `parent`] >>
     Cases_on `EL a.as_pc prog = AsmOp "CALL"` >> gvs[]) >>
  suspend "effects"
QED

Resume asm_frame_call_terminal_exception[effects]:
  `a.as_outcomes = failed_outcome (request_of s)::MAP SND (call_trace t)` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `record_request (request_of s) a.as_requests ++ call_requests t =
     call_requests es0` by
    (fs[asm_frame_rel_def, call_requests_def, record_request_def] >>
     gvs[] >> IF_CASES_TAC >> gvs[]) >>
  `(request_of s).cr_kind = MessageCall` by
    (Cases_on `EL a.as_pc prog = AsmOp "CALL"` >> gvs[request_of_def]) >>
  `take_outcome (request_of s) a.as_outcomes =
     (failed_outcome (request_of s),MAP SND (call_trace t))` by
    simp[asm_take_outcome_failed_head] >>
  `buffer_to_list c.memory = a.as_memory /\
   a.as_accounts = s.rollback.accounts /\
   a.as_transient = s.rollback.tStorage /\ a.as_logs = c.logs /\
   a.as_pending_deletions = s.rollback.toDelete` by gvs[asm_evm_rel_def] >>
  `buffer_to_list parent.memory = asm_call_memory ao az ro rs a.as_memory` by
    (simp[Abbr `parent`] >>
     qpat_assum `buffer_to_list c.memory = _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     Cases_on `max_expansion_range (ao,az) (ro,rs)` >>
     rename1 `max_expansion_range (ao,az) (ro,rs) = (off,sz)` >>
     simp_tac (srw_ss()) [] >>
     irule asm_call_memory_buffer_extend >>
     qexistsl_tac [`off`,`sz`] >> simp_tac (srw_ss()) [] >>
     simp_tac std_ss [arithmeticTheory.MULT_COMM] >>
     first_assum ACCEPT_TAC) >>
  suspend "apply"
QED

Resume asm_frame_call_terminal_exception[apply]:
  qpat_x_assum `Abbrev (t = _)` mp_tac >>
  qmatch_goalsub_abbrev_tac `(ct,rb)::rest` >> disch_tac >>
  `t.contexts = (ct,rb)::rest /\ t.txParams = s.txParams /\
   t.msdomain = Collect dt /\
   t.rollback.accounts = s.rollback.accounts /\
   t.rollback.tStorage = s.rollback.tStorage /\
   t.rollback.toDelete = s.rollback.toDelete` by simp[Abbr `t`] >>
  `ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\
   ct.pc = SUC c.pc /\ ct.logs = c.logs /\ ct.returnData = [] /\
   ct.stack = 0w::DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
   ct.memory = parent.memory` by simp[Abbr `ct`, Abbr `parent`] >>
  qpat_x_assum `Abbrev (t = _)` kall_tac >>
  qpat_x_assum `Abbrev (ct = _)` kall_tac >>
  `ct.stack = (if (failed_outcome (request_of s)).co_success then 1w else 0w)::
       DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
   ct.returnData = (failed_outcome (request_of s)).co_returnData /\
   buffer_to_list ct.memory =
       TAKE ro (asm_call_memory ao az ro rs a.as_memory) ++
       TAKE rs (failed_outcome (request_of s)).co_returnData ++
       DROP (ro + LENGTH (TAKE rs (failed_outcome (request_of s)).co_returnData))
         (asm_call_memory ao az ro rs a.as_memory) /\
   adopt_outcome (request_of s) (failed_outcome (request_of s))
     (a.as_accounts,a.as_transient,a.as_logs) =
       (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
   adopt_outcome_deletions (request_of s) (failed_outcome (request_of s))
     a.as_pending_deletions = t.rollback.toDelete` by
    ASM_SIMP_TAC (srw_ss()) [failed_outcome_def, adopt_outcome_def,
      adopt_outcome_deletions_def, TAKE_DROP] >>
  (Q.SUBGOAL_THEN `?d. t.msdomain = Collect d` assume_tac >- metis_tac[]) >>
  `gas_readings t = gas_readings s` by metis_tac[] >>
  `asm_call_memory ao az ro rs a.as_memory =
     asm_call_memory ao az ro rs a.as_memory` by simp[] >>
  drule_all asm_frame_call_effects_step_ok >> simp[]
QED

Finalise asm_frame_call_terminal_exception

Theorem asm_message_prepared_terminal_success_view:
  wf_state s /\ s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall \/ op = DelegateCall) /\
  next_opcode c = SOME op /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR NONE,v) ==>
  ?t ct. step s = (INL (),t) /\ t.contexts = (ct,rb)::rest /\
    t.txParams = s.txParams /\ (?dt. t.msdomain = Collect dt) /\
    ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\ ct.pc = SUC c.pc /\
    ct.stack = 1w::DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
    ct.returnData = (FST (HD v.contexts)).returnData /\
    buffer_to_list ct.memory =
      TAKE ro (asm_call_memory ao az ro rs (buffer_to_list c.memory)) ++
      TAKE rs ct.returnData ++
      DROP (ro + LENGTH (TAKE rs ct.returnData))
        (asm_call_memory ao az ro rs (buffer_to_list c.memory)) /\
    t.rollback.accounts = v.rollback.accounts /\
    t.rollback.tStorage = v.rollback.tStorage /\
    t.rollback.toDelete = s.rollback.toDelete /\ ct.logs = c.logs /\
    (value = 0 ==> t.rollback.accounts = s.rollback.accounts /\
                  t.rollback.tStorage = s.rollback.tStorage) /\
    (op = StaticCall ==> value = 0)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `EVERY (wf_context o FST) s.contexts` by fs[wf_state_def] >>
  drule_all asm_message_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `u = s with <| contexts := (parent,rb)::rest;
    rollback := _; msdomain := _ |>` >>
  `u.contexts = (parent,rb)::rest` by simp[] >>
  `LENGTH u.contexts <= 1024` by
    (qpat_x_assum `LENGTH s.contexts <= 1024` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  drule_all asm_call_finish_proceed >>
  disch_then (fn th => qpat_assum `asm_call_finish _ _ _ = _` mp_tac >>
    rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `proceed_call _ _ _ _ _ _ _ _ _ p` >> disch_tac >>
  `p.contexts = (parent with returnData := [],rb)::rest /\ p.contexts <> []` by
    simp[Abbr `p`] >>
  `step_call op s = (INR NONE,v)` by
    (rewrite_tac[asm_step_call_factor, bind_def] >>
     qpat_assum `asm_call_prepare _ _ = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [] >>
     qpat_assum `asm_call_finish _ _ _ = _` (fn th => rewrite_tac[th])) >>
  `stipend <= (parent with returnData := []).gasUsed /\
   LENGTH (parent with returnData := []).stack < stack_limit` by
    (`wf_context c` by gvs[] >>
     simp[Abbr `parent`, LENGTH_DROP] >>
     qpat_x_assum `wf_context c` mp_tac >>
     simp[wf_context_def, vfmConstantsTheory.stack_limit_def] >>
     Cases_on `call_has_value op` >> simp[] >> decide_tac) >>
  drule_all asm_message_step_terminal >> disch_tac >>
  drule_all asm_proceed_call_memory_boundary >> strip_tac >>
  drule_all asm_handle_step_memory >> disch_tac >>
  drule_all asm_handle_exception_memory_success >> disch_tac >>
  `step s = (INL (), v with contexts :=
    (parent with <|
      gasUsed := parent.gasUsed - (child.msgParams.gasLimit-child.gasUsed);
      pc := SUC parent.pc; stack := b2w T :: parent.stack;
      returnData := child.returnData;
      memory := buffer_write ro (TAKE rs child.returnData) parent.memory;
      logs := parent.logs ++ child.logs;
      addRefund := parent.addRefund + child.addRefund;
      subRefund := parent.subRefund + child.subRefund |>,rb)::rest)` by
    gvs[vfm_abort_def] >>
  suspend "returned"
QED

Resume asm_message_prepared_terminal_success_view[returned]:
  drule_all asm_proceed_call_saved_checkpoint >> strip_tac >>
  drule_all asm_proceed_call_terminal_effects >> strip_tac >>
  `op = StaticCall ==> value = 0` by
    (strip_tac >> qpat_x_assum `value = _` mp_tac >>
     simp[call_has_value_def]) >>
  `value = 0 ==> v.rollback.accounts = s.rollback.accounts /\
                 v.rollback.tStorage = s.rollback.tStorage` by
    (strip_tac >> qpat_x_assum `value = 0` SUBST_ALL_TAC >>
     drule_all asm_proceed_call_zero_terminal_effects >>
     simp[Abbr `p`]) >>
  `child.logs = [] /\ v.txParams = s.txParams /\
   v.rollback.toDelete = s.rollback.toDelete /\
   ?dt. v.msdomain = Collect dt` by
    (gvs[Abbr `p`, vfmSameFrameTheory.msdomain_compatible_def] >>
     Cases_on `v.msdomain` >> gvs[]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`sender = _`, `accounts = _`, `address = _`, `value = _`,
     `ao = _`, `az = _`, `ro = _`, `rs = _`,
     `asm_call_prepare _ _ = _`, `asm_call_finish _ _ _ = _`,
     `proceed_call _ _ _ _ _ _ _ _ _ _ = _`, `step_call _ _ = _`] >>
  qmatch_asmsub_abbrev_tac `step s = (INL (),t)` >>
  qexists_tac `t` >>
  simp[Abbr `t`, Abbr `parent`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `max_expansion_range (ao,az) (ro,rs)` >>
  simp_tac (srw_ss()) [] >>
  irule asm_call_memory_buffer_write >>
  goal_assum (drule_at Any) >> simp_tac std_ss [arithmeticTheory.MULT_COMM]
QED

Finalise asm_message_prepared_terminal_success_view

Theorem asm_call_prepared_terminal_success_view:
  wf_state s /\ s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  next_opcode c = SOME op /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR NONE,v) ==>
  ?t ct. step s = (INL (),t) /\ t.contexts = (ct,rb)::rest /\
    t.txParams = s.txParams /\ (?dt. t.msdomain = Collect dt) /\
    ct.msgParams = c.msgParams /\ ct.jumpDest = c.jumpDest /\ ct.pc = SUC c.pc /\
    ct.stack = 1w::DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
    ct.returnData = (FST (HD v.contexts)).returnData /\
    buffer_to_list ct.memory =
      TAKE ro (asm_call_memory ao az ro rs (buffer_to_list c.memory)) ++
      TAKE rs ct.returnData ++
      DROP (ro + LENGTH (TAKE rs ct.returnData))
        (asm_call_memory ao az ro rs (buffer_to_list c.memory)) /\
    t.rollback.accounts = v.rollback.accounts /\
    t.rollback.tStorage = v.rollback.tStorage /\
    t.rollback.toDelete = s.rollback.toDelete /\ ct.logs = c.logs /\
    (value = 0 ==> t.rollback.accounts = s.rollback.accounts /\
                  t.rollback.tStorage = s.rollback.tStorage) /\
    (op = StaticCall ==> value = 0)
Proof
  strip_tac >> irule asm_message_prepared_terminal_success_view >>
  simp[] >> metis_tac[]
QED

Theorem asm_call_terminal_success_selected_effects:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  next_opcode c = SOME op /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR NONE,v) /\
  t.contexts = (ct,rb)::rest /\ ct.stack = 1w::stk /\
  ct.returnData = (FST (HD v.contexts)).returnData /\ ct.logs = c.logs /\
  t.rollback.toDelete = s.rollback.toDelete /\
  (value = 0 ==> t.rollback.accounts = s.rollback.accounts /\
                t.rollback.tStorage = s.rollback.tStorage) /\
  (op = StaticCall ==> value = 0) /\
  a.as_accounts = s.rollback.accounts /\ a.as_transient = s.rollback.tStorage /\
  a.as_logs = c.logs /\ a.as_pending_deletions = s.rollback.toDelete /\
  out = FST (take_outcome (request_of s)
    (outcome_of (request_of s).cr_kind t (LENGTH c.logs)
      (LENGTH s.rollback.toDelete)::tail)) ==>
  out.co_success /\ out.co_returnData = ct.returnData /\
  adopt_outcome (request_of s) out (a.as_accounts,a.as_transient,a.as_logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
  adopt_outcome_deletions (request_of s) out a.as_pending_deletions =
    t.rollback.toDelete
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepared_request >> strip_tac >>
  `computed_precompile (request_of s) ==>
   precompile_result (request_of s).cr_target (request_of s).cr_data =
     SOME (SOME ct.returnData)` by
    (strip_tac >> drule_all asm_call_computed_finish_success >> simp[]) >>
  qpat_x_assum `asm_call_prepare _ _ = _` kall_tac >>
  qpat_x_assum `asm_call_finish _ _ _ = _` kall_tac >>
  Cases_on `computed_precompile (request_of s)`
  >- (`value = 0` by fs[computed_precompile_def] >>
      gvs[take_outcome_def, outcome_of_def, failed_outcome_def,
          adopt_outcome_def, adopt_outcome_deletions_def]) >>
  gvs[take_outcome_def, outcome_of_def,
      adopt_outcome_def, adopt_outcome_deletions_def] >>
  Cases_on `op = StaticCall` >> gvs[]
QED

Theorem asm_frame_call_terminal_none:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR NONE,v) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a s /\ wf_state s /\
   ~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  (Q.SUBGOAL_THEN `op = Call \/ op = StaticCall` assume_tac >- metis_tac[]) >>
  `next_opcode c = SOME op` by
    (drule_all asm_frame_call_decode >> simp[] >> metis_tac[]) >>
  `a.as_accounts = s.rollback.accounts /\ a.as_transient = s.rollback.tStorage /\
   a.as_logs = c.logs /\ a.as_pending_deletions = s.rollback.toDelete /\
   a.as_memory = buffer_to_list c.memory` by gvs[asm_evm_rel_def] >>
  drule_all asm_call_prepared_terminal_success_view >> strip_tac >>
  qabbrev_tac `out = FST (take_outcome (request_of s)
    (outcome_of (request_of s).cr_kind t (LENGTH c.logs)
      (LENGTH s.rollback.toDelete)::MAP SND (call_trace t)))` >>
  `out = FST (take_outcome (request_of s)
    (outcome_of (request_of s).cr_kind t (LENGTH c.logs)
      (LENGTH s.rollback.toDelete)::MAP SND (call_trace t)))` by simp[Abbr `out`] >>
  drule_all asm_call_terminal_success_selected_effects >> strip_tac >>
  `6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack` by
    (drule_all asm_call_prepare_success_stack >> simp[]) >>
  `observable_call c` by
    (simp[observable_call_def] >> Cases_on `op = Call` >> gvs[call_has_value_def]) >>
  `ct.stack = (if out.co_success then 1w else 0w)::
     DROP (6 + (if call_has_value op then 1 else 0)) c.stack` by
    asm_rewrite_tac[] >>
  `ct.returnData = out.co_returnData` by metis_tac[] >>
  `buffer_to_list ct.memory = TAKE ro (asm_call_memory ao az ro rs a.as_memory) ++
     TAKE rs out.co_returnData ++ DROP (ro + LENGTH (TAKE rs out.co_returnData))
       (asm_call_memory ao az ro rs a.as_memory)` by metis_tac[] >>
  (Q.SUBGOAL_THEN `?d. t.msdomain = Collect d` assume_tac >- metis_tac[]) >>
  drule_all asm_frame_call_same_depth_effects_step_ok >> simp[]
QED

Theorem asm_frame_call_terminal_some:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR (SOME exc),v) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `~c.msgParams.static /\ ?d. s.msdomain = Collect d` by
    (fs[asm_frame_rel_def] >> metis_tac[]) >>
  (Q.SUBGOAL_THEN `op = Call \/ op = StaticCall` assume_tac >- metis_tac[]) >>
  drule_all asm_call_prepared_terminal_kind >> strip_tac >>
  `exc <> Reverted` by gvs[] >>
  drule_all asm_frame_call_terminal_exception >> simp[]
QED

Theorem asm_frame_call_terminal:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR result,v) ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  Cases_on `result`
  >- (drule_all asm_frame_call_terminal_none >> simp[]) >>
  drule_all asm_frame_call_terminal_some >> simp[]
QED

Theorem asm_call_safe_bind:
  (!s r t. P s /\ f s = (r,t) ==>
    (!e. r = INR e ==> ~vfm_abort e) /\ (!x. r = INL x ==> P t)) /\
  (!x s r t. P s /\ g x s = (r,t) ==>
    (!e. r = INR e ==> ~vfm_abort e) /\ (!y. r = INL y ==> P t)) /\
  P s /\ bind f g s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\ (!y. r = INL y ==> P t)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  Cases_on `f s` >> rename1 `f s = (result,u)` >> Cases_on `result`
  >- (simp[bind_def] >> strip_tac >>
      qpat_x_assum `!s r t. _` (qspecl_then [`s`,`INL x`,`u`] mp_tac) >>
      simp[] >> strip_tac >> metis_tac[]) >>
  simp[bind_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem asm_call_safe_get_context:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_current_context s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[get_current_context_def, return_def]
QED

Theorem asm_call_safe_set_context:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  set_current_context c s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[set_current_context_def, return_def]
QED

Theorem asm_call_safe_pop_stack:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  pop_stack n s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[pop_stack_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  IF_CASES_TAC >> simp[vfm_abort_def] >> rpt strip_tac >> gvs[]
QED

Theorem asm_call_safe_push_stack:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  push_stack w s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[push_stack_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  IF_CASES_TAC >> simp[vfm_abort_def] >> rpt strip_tac >> gvs[]
QED

Theorem asm_call_safe_consume_gas:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  consume_gas n s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `s.contexts` >> simp[] >>
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  IF_CASES_TAC >> simp[vfm_abort_def] >> rpt strip_tac >> gvs[]
QED

Theorem asm_call_safe_access_address:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  access_address a s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[access_address_def, domain_check_def, set_domain_def,
      ignore_bind_def, bind_def, return_def]
QED

Theorem asm_call_safe_access_slot:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  access_slot a s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[access_slot_def, domain_check_def, set_domain_def,
      ignore_bind_def, bind_def, return_def]
QED

Theorem asm_call_safe_storage_domain:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  ensure_storage_in_domain a s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[ensure_storage_in_domain_def, domain_check_def, set_domain_def,
      ignore_bind_def, bind_def, return_def]
QED

Theorem asm_call_safe_inc_pc_or_jump:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  inc_pc_or_jump op s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `is_call op`
  >- (rpt strip_tac >> gvs[inc_pc_or_jump_def, return_def]) >>
  Cases_on `s.contexts` >> simp[] >>
  simp[inc_pc_or_jump_def, get_current_context_def, bind_def] >>
  Cases_on `(FST h).jumpDest` >>
  simp[set_current_context_def, return_def, assert_def, ignore_bind_def, bind_def,
       fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), vfm_abort_def]
QED

Theorem asm_call_safe_charge_push:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind (consume_gas n) (\x. push_stack w) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[asm_call_safe_consume_gas] >>
  metis_tac[asm_call_safe_push_stack]
QED

Theorem asm_call_safe_stack_op:
  !cost result n s r t. s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind (pop_stack n) (\args.
    bind (consume_gas (cost args)) (\x. push_stack (result args))) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >>
  ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[asm_call_safe_pop_stack] >>
  metis_tac[asm_call_safe_charge_push]
QED

Theorem asm_call_unuse_gas_credit:
  s.contexts = (c,rb)::rest /\ n <= c.gasUsed ==>
  unuse_gas n s =
    (INL (), s with contexts := (c with gasUsed := c.gasUsed - n,rb)::rest)
Proof
  simp[unuse_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def]
QED

Theorem asm_call_safe_unuse_gas:
  s.contexts <> [] /\ n <= (FST (HD s.contexts)).gasUsed /\
  unuse_gas n s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ t.msdomain = s.msdomain /\
    (FST (HD t.contexts)).gasUsed = (FST (HD s.contexts)).gasUsed - n)
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  rpt strip_tac >> gvs[] >> drule_all asm_call_unuse_gas_credit >>
  strip_tac >> gvs[]
QED

Theorem asm_call_safe_abort_call_value:
  s.contexts = (c,rb)::rest /\ n <= c.gasUsed /\
  abort_call_value n s = (INR e,t) ==> ~vfm_abort e
Proof
  Cases_on `LENGTH c.stack < stack_limit`
  >- (rpt strip_tac >> drule_all asm_abort_call_value_state >> gvs[]) >>
  rpt strip_tac >>
  gvs[abort_call_value_def, push_stack_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def,
       assert_def, fail_def, return_def, vfm_abort_def,
       vfmConstantsTheory.stack_limit_def]
QED

Theorem asm_call_safe_abort_unuse:
  s.contexts = (c,rb)::rest /\ n <= c.gasUsed /\
  abort_unuse n s = (INR e,t) ==> ~vfm_abort e
Proof
  Cases_on `LENGTH c.stack < stack_limit`
  >- (rpt strip_tac >> drule_all asm_abort_unuse_state >> gvs[]) >>
  rpt strip_tac >>
  gvs[abort_unuse_def, unuse_gas_def, push_stack_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, fail_def, return_def, vfm_abort_def,
       vfmConstantsTheory.stack_limit_def]
QED

Theorem asm_call_finish_credit_safe:
  s.contexts = (c,rb)::rest /\ stipend <= c.gasUsed /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) s =
    (INR e,t) ==> ~vfm_abort e
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 2 disch_tac >>
  Cases_on `(lookup_account sender accounts).balance < value`
  >- (simp[asm_call_finish_def] >> strip_tac >>
      drule_all asm_call_safe_abort_call_value >> simp[]) >>
  simp[asm_call_finish_def, set_return_data_def, get_num_contexts_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `(if _ then _ else _) v` >>
  `v.contexts = (c with returnData := [],rb)::rest /\
   stipend <= (c with returnData := []).gasUsed` by simp[Abbr `v`] >>
  IF_CASES_TAC >> strip_tac
  >- (drule_all asm_call_safe_abort_unuse >> simp[]) >>
  `v.contexts <> []` by simp[Abbr `v`] >>
  drule_all asm_proceed_call_terminal_kind >> simp[]
QED

Theorem asm_call_prepared_finish_safe:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  EVERY (wf_context o FST) s.contexts /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INR e,t) ==> ~vfm_abort e
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_stipend_paid >> disch_tac >>
  `u.contexts <> []` by
    (drule_all asm_call_prepare_success_view >> simp[LET_THM] >>
     rpt strip_tac >> gvs[]) >>
  Cases_on `u.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  drule_all asm_call_finish_credit_safe >> simp[]
QED

Theorem asm_create_refund_prefix_credit:
  s.contexts <> [] /\ s.msdomain = Collect d /\
  (do consume_gas n; assert_not_static; set_return_data [];
      get_num_contexts od) s = (INL depth,u) ==>
  u.contexts <> [] /\ u.msdomain = Collect d /\
  n <= (FST (HD u.contexts)).gasUsed /\ depth = LENGTH u.contexts
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  simp[consume_gas_def, assert_not_static_def, get_static_def,
       set_return_data_def, get_num_contexts_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem asm_create_refund_prefix_safe:
  s.contexts <> [] /\ s.msdomain = Collect d /\
  (do consume_gas n; assert_not_static; set_return_data [];
      get_num_contexts od) s = (INL depth,u) /\
  abort_unuse n u = (INR e,t) ==> ~vfm_abort e
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_create_refund_prefix_credit >> strip_tac >>
  Cases_on `u.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  drule_all asm_call_safe_abort_unuse >> simp[]
QED

Theorem asm_create_original_access_boundary:
  s.contexts <> [] /\ s.msdomain = Collect d /\
  (do access_address address; ensure_storage_in_domain address;
      update_accounts (increment_nonce sender); get_rollback od) s =
    (INL rb,u) ==>
  u.contexts = s.contexts /\ u.msdomain = Collect
    (d with <| addresses updated_by fINSERT address;
               fullStorages updated_by fINSERT address |>) /\
  get_original u = (INL u.originalAccounts,u)
Proof
  rpt strip_tac >>
  gvs[access_address_def, ensure_storage_in_domain_def,
      domain_check_def, set_domain_def, update_accounts_def, get_rollback_def,
      get_original_def, bind_def, ignore_bind_def, return_def]
QED

Theorem asm_create_safe_abort_exists:
  s.contexts <> [] /\ abort_create_exists sender s = (INR e,t) ==>
  ~vfm_abort e
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  simp[abort_create_exists_def, update_accounts_def, push_stack_def, inc_pc_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), vfm_abort_def]
QED

Theorem asm_create_charged_finish_safe:
  s.contexts <> [] /\ s.msdomain = Collect d /\
  (do consume_gas n; assert_not_static; set_return_data [];
      get_num_contexts od) s = (INL depth,u) /\
  (if b1 \/ b2 \/ depth > 1024 then abort_unuse n else do
     access_address address; ensure_storage_in_domain address;
     if b3 then abort_create_exists sender
     else proceed_create sender address value code n
   od) u = (INR e,t) ==> ~vfm_abort e
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_create_refund_prefix_credit >> strip_tac >>
  Cases_on `b1 \/ b2 \/ depth > 1024`
  >- (gvs[] >> Cases_on `u.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
      drule_all asm_call_safe_abort_unuse >> simp[]) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  simp[access_address_def, ensure_storage_in_domain_def,
       domain_check_def, set_domain_def, bind_def, ignore_bind_def, return_def] >>
  qmatch_goalsub_abbrev_tac `(if b3 then _ else _) v` >>
  `v.contexts <> []` by simp[Abbr `v`] >>
  Cases_on `b3` >> simp[] >> strip_tac
  >- (drule_all asm_create_safe_abort_exists >> simp[]) >>
  drule_all vfmStepLengthTheory.proceed_create_returns_inl >> simp[]
QED

Theorem asm_call_safe_binop:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_binop op f s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_binop_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[asm_call_safe_pop_stack] >>
  metis_tac[asm_call_safe_charge_push]
QED

Theorem asm_call_safe_exp:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_exp s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_exp_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[asm_call_safe_pop_stack] >>
  metis_tac[asm_call_safe_charge_push]
QED

Theorem asm_call_safe_memory_expansion_info:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  memory_expansion_info offset sz s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[memory_expansion_info_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_expand_memory:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  expand_memory n s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[expand_memory_def, get_current_context_def, set_current_context_def,
      bind_def, return_def]
QED

Theorem asm_call_safe_read_memory:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  read_memory offset sz s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[read_memory_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_write_memory:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  write_memory offset bytes s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[write_memory_def, get_current_context_def, set_current_context_def,
      bind_def, return_def]
QED

Theorem asm_call_safe_get_call_data:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_call_data s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_call_data_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_copy_source:
  (!f. source = SOME f ==> !s r t.
    s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\ f s = (r,t) ==>
    (!e. r = INR e ==> ~vfm_abort e) /\
    (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)) /\
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  (case source of SOME f => do
     bytes <- f; expand_memory n;
     return (take_pad_0 sz (DROP off bytes)) od
   | NONE => do expand_memory n; read_memory off sz od) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `source` >> simp[ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac
  >- (drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
      disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
      BETA_TAC >> disch_then irule >> simp[] >>
      conj_tac >- metis_tac[asm_call_safe_expand_memory] >>
      metis_tac[asm_call_safe_read_memory]) >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[return_def] >>
  metis_tac[asm_call_safe_expand_memory]
QED

Theorem asm_call_safe_copy_to_memory:
  (!f. source = SOME f ==> !s r t.
    s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\ f s = (r,t) ==>
    (!e. r = INR e ==> ~vfm_abort e) /\
    (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)) /\
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  copy_to_memory gas offset off sz source s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[copy_to_memory_def, ignore_bind_def, LET_THM] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  Cases_on `if source = NONE then max_expansion_range (offset,sz) (off,sz)
            else (offset,sz)` >> gvs[] >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_memory_expansion_info] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pat `(case source of _ => _ | _ => _) _ = _`)
        (REWRITE_RULE [ignore_bind_def] asm_call_safe_copy_source) >>
      simp[] >> disch_then irule >> simp[]
      >- (qpat_x_assum `!f. source = SOME f ==> _` mp_tac >>
          simp[GSYM AND_IMP_INTRO]) >>
      metis_tac[]) >>
  metis_tac[asm_call_safe_write_memory]
QED

Theorem asm_call_safe_copy_memory_source:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  copy_to_memory gas offset off sz NONE s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  strip_tac >>
  drule_at (Pat `copy_to_memory _ _ _ _ _ _ = _`) asm_call_safe_copy_to_memory >>
  simp[]
QED

Theorem asm_call_safe_copy_call_data:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  copy_to_memory gas offset off sz (SOME get_call_data) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  strip_tac >>
  drule_at (Pat `copy_to_memory _ _ _ _ _ _ = _`) asm_call_safe_copy_to_memory >>
  simp[] >> impl_tac >- metis_tac[asm_call_safe_get_call_data] >> simp[]
QED

Theorem asm_call_safe_return:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  return v s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[return_def]
QED

Theorem asm_call_safe_get_callee:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_callee s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_callee_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_get_accounts:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_accounts s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[get_accounts_def, return_def]
QED

Theorem asm_call_safe_get_original:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_original s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[get_original_def, return_def]
QED

Theorem asm_call_safe_get_tStorage:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_tStorage s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[get_tStorage_def, return_def]
QED

Theorem asm_call_safe_get_tx_params:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_tx_params s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[get_tx_params_def, return_def]
QED

Theorem asm_call_safe_get_gas_left:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_gas_left s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_gas_left_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_get_code:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_code address s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[get_code_def, get_accounts_def, bind_def, return_def]
QED

Theorem asm_call_safe_get_current_code:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_current_code s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_current_code_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_get_return_data:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_return_data s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_return_data_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_update_accounts:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  update_accounts f s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[update_accounts_def, return_def]
QED

Theorem asm_call_safe_set_tStorage:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  set_tStorage a s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[set_tStorage_def, return_def]
QED

Theorem asm_call_safe_write_storage:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  write_storage address key value s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  simp[write_storage_def] >> metis_tac[asm_call_safe_update_accounts]
QED

Theorem asm_call_safe_write_transient_storage:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  write_transient_storage address key value s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[write_transient_storage_def, get_tStorage_def, set_tStorage_def,
      bind_def, return_def]
QED

Theorem asm_call_safe_set_return_data:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  set_return_data bytes s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[set_return_data_def, get_current_context_def, set_current_context_def,
      bind_def, return_def]
QED

Theorem asm_call_safe_set_jump_dest:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  set_jump_dest dest s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[set_jump_dest_def, get_current_context_def, set_current_context_def,
      bind_def, return_def]
QED

Theorem asm_call_safe_push_logs:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  push_logs logs s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[push_logs_def, get_current_context_def, set_current_context_def,
      bind_def, return_def]
QED

Theorem asm_call_safe_update_gas_refund:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  update_gas_refund refund s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  PairCases_on `refund` >> rpt strip_tac >>
  gvs[update_gas_refund_def, get_current_context_def, set_current_context_def,
      bind_def, return_def]
QED

Theorem asm_call_safe_add_to_delete:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  add_to_delete address s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[add_to_delete_def, return_def]
QED

Theorem asm_call_safe_assert:
  ~vfm_abort (SOME exc) /\
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  assert b exc s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `b` >> rpt strip_tac >> gvs[assert_def]
QED

Theorem asm_call_safe_fail:
  ~vfm_abort (SOME exc) /\
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  fail exc s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[fail_def]
QED

Theorem asm_call_safe_finish:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  finish s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[finish_def]
QED

Theorem asm_call_safe_revert:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  revert s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >> gvs[revert_def]
QED

Theorem asm_call_safe_get_return_data_check:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_return_data_check offset sz s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_return_data_check_def, get_return_data_def, get_current_context_def,
      ignore_bind_def, bind_def, return_def, assert_def, AllCaseEqs()]
QED

Theorem asm_call_safe_assert_not_static:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  assert_not_static s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[assert_not_static_def, get_static_def, get_current_context_def,
      bind_def, return_def, assert_def, AllCaseEqs()]
QED

Theorem asm_call_safe_get_caller:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_caller s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_caller_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_get_value:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_value s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_value_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_get_static:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  get_static s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rpt strip_tac >>
  gvs[get_static_def, get_current_context_def, bind_def, return_def]
QED

Theorem asm_call_safe_monop:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_monop op f s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_monop_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[asm_call_safe_pop_stack] >>
  metis_tac[asm_call_safe_charge_push]
QED

Theorem asm_call_safe_modop:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_modop op f s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_modop_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[asm_call_safe_pop_stack] >>
  metis_tac[asm_call_safe_charge_push]
QED

Theorem asm_call_safe_push:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_push n ws s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_push_def, ignore_bind_def] >>
  strip_tac >> drule_at (Pat `bind _ _ _ = _`) asm_call_safe_charge_push >> simp[]
QED

Theorem asm_call_safe_pop:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_pop s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_pop_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  conj_tac >- metis_tac[asm_call_safe_pop_stack] >>
  metis_tac[asm_call_safe_consume_gas]
QED

Theorem asm_call_safe_context:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_context op f s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_context_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_push_stack] >>
  metis_tac[asm_call_safe_get_context]
QED

Theorem asm_call_safe_delegate_code:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  (case get_delegate code of
     NONE => return (code,0)
   | SOME delegate => do
       cost <- access_address delegate;
       return ((lookup_account delegate accounts).code,cost)
     od) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `get_delegate code` >> simp[]
  >- metis_tac[asm_call_safe_return] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  dxrule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_access_address] >>
  metis_tac[asm_call_safe_return]
QED

Theorem asm_call_safe_static_guard:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  (if b then assert_not_static else return ()) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `b` >> simp[]
  >- metis_tac[asm_call_safe_assert_not_static] >>
  metis_tac[asm_call_safe_return]
QED

Theorem asm_call_prepare_safe:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  asm_call_prepare op s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[asm_call_prepare_def, LET_THM, asm_uncurry_projection,
              ignore_bind_def] >> BETA_TAC >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  rpt (
    dxrule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
    disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
    BETA_TAC >> disch_then irule >> simp[] >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        FIRST (map (drule_at (Pat `_ _ = (_,_)`))
          [asm_call_safe_pop_stack, asm_call_safe_memory_expansion_info,
           asm_call_safe_access_address, asm_call_safe_get_accounts,
           asm_call_safe_delegate_code, asm_call_safe_get_gas_left,
           asm_call_safe_consume_gas, asm_call_safe_static_guard,
           asm_call_safe_expand_memory, asm_call_safe_get_callee]) >> simp[]) >>
    rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac) >>
  gvs[bind_def, get_callee_def, get_current_context_def, return_def,
      fail_def, AllCaseEqs()]
QED

Theorem asm_call_charged_suffix_credit:
  (do consume_gas n;
      if b then assert_not_static else return ();
      expand_memory k;
      sender <- get_callee;
      return (sender,extra)
   od) s = (INL (sender',extra'),u) ==>
  u.contexts <> [] /\ n <= (FST (HD u.contexts)).gasUsed /\
  extra' = extra
Proof
  Cases_on `s.contexts`
  >- simp[consume_gas_def, get_current_context_def, bind_def,
          ignore_bind_def, fail_def] >>
  PairCases_on `h` >> Cases_on `b` >>
  simp[consume_gas_def, assert_not_static_def, get_static_def,
       expand_memory_def, get_callee_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def,
       assert_def, return_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem asm_call_prepare_credit:
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) ==>
  u.contexts <> [] /\ stipend <= (FST (HD u.contexts)).gasUsed
Proof
  rewrite_tac[asm_call_prepare_def, LET_THM, asm_uncurry_projection] >> BETA_TAC >>
  disch_tac >>
  ntac 6
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[Once bind_def, AllCaseEqs()] >> disch_tac >> gvs[]) >>
  ntac 6 (pop_last_assum kall_tac) >>
  dxrule asm_call_charged_suffix_credit >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `call_gas value' gas' left cost (ac + (dc + (cc + vc)))` >>
  qmatch_goalsub_abbrev_tac `SND cg` >>
  `(if 0 < value' then call_stipend else 0) <= ac + (dc + (cc + vc)) + cost` by
    (Cases_on `0 < value'` >>
     gvs[Abbr `vc`, Abbr `value'`, vfmConstantsTheory.call_stipend_def,
         vfmConstantsTheory.call_value_cost_def]) >>
  `SND cg <= FST cg + cost` by
    (irule call_gas_stipend_le_consumed >>
     qexistsl_tac [`gas'`, `left`, `ac + (dc + (cc + vc))`, `value'`] >>
     simp[Abbr `cg`]) >>
  gvs[Abbr `cg`]
QED

Theorem asm_call_raw_safe:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_call op s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [])
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> gvs[asm_step_call_factor, bind_def, AllCaseEqs()]
      >- (PairCases_on `x` >>
          drule asm_call_prepare_credit >> strip_tac >>
          qmatch_asmsub_rename_tac `asm_call_finish _ _ mid = _` >>
          Cases_on `mid.contexts` >> gvs[] >> PairCases_on `h` >> gvs[] >>
          drule_all asm_call_finish_credit_safe >> simp[]) >>
      drule_at (Pat `asm_call_prepare _ _ = _`) asm_call_prepare_safe >>
      simp[]) >>
  rpt strip_tac >>
  `LENGTH t.contexts >= LENGTH s.contexts` by
    (mp_tac vfmStepLengthTheory.same_frame_or_grow_step_call >>
     metis_tac[vfmStepLengthTheory.same_frame_or_grow_length]) >>
  Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
QED

Theorem asm_create_refund_prefix_noabort:
  s.contexts <> [] /\
  (do consume_gas n; assert_not_static; set_return_data [];
      get_num_contexts od) s = (INR e,t) ==> ~vfm_abort e
Proof
  Cases_on `s.contexts` >> simp[] >> PairCases_on `h` >>
  simp[consume_gas_def, assert_not_static_def, get_static_def,
       set_return_data_def, get_num_contexts_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), vfm_abort_def]
QED

Theorem asm_create_charged_safe:
  s.contexts <> [] /\ s.msdomain = Collect d /\
  (do consume_gas n; assert_not_static; set_return_data [];
      depth <- get_num_contexts;
      if b1 \/ b2 \/ depth > 1024 then abort_unuse n else do
        access_address address; ensure_storage_in_domain address;
        if b3 then abort_create_exists sender
        else proceed_create sender address value code n
      od
   od) s = (INR e,t) ==> ~vfm_abort e
Proof
  pure_rewrite_tac[ignore_bind_def, GSYM bind_assoc] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs()]
  >- (rename1 `get_num_contexts _ = (INL depth,u)` >>
      `(do consume_gas n; assert_not_static; set_return_data [];
           get_num_contexts od) s = (INL depth,u)` by
        simp[ignore_bind_def, bind_def] >>
      drule_at (Pat `_ _ = (INL _,_)`) asm_create_charged_finish_safe >>
      simp[ignore_bind_def] >> metis_tac[]) >>
  rename1 `_ _ = (INR e,u)` >>
  `(do consume_gas n; assert_not_static; set_return_data [];
       get_num_contexts od) s = (INR e,u)` by
    simp[ignore_bind_def, bind_def] >>
  drule_all asm_create_refund_prefix_noabort >> simp[]
QED

Theorem asm_create_noabort_bind:
  (!s r t. P s /\ f s = (r,t) ==>
    (!e. r = INR e ==> ~vfm_abort e) /\ (!x. r = INL x ==> P t)) /\
  (!x s e t. P s /\ g x s = (INR e,t) ==> ~vfm_abort e) /\
  P s /\ bind f g s = (INR e,t) ==> ~vfm_abort e
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  Cases_on `f s` >> rename1 `f s = (result,u)` >> Cases_on `result` >>
  simp[bind_def] >> rpt strip_tac >> metis_tac[]
QED


fun asm_create_prefix_tac primitive =
  dxrule_at (Pat `bind _ _ _ = _`) asm_create_noabort_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then match_mp_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_at (Pat `_ _ = (_,_)`) primitive >> simp[vfm_abort_def]) >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac;

Theorem asm_create_raw_noabort:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_create two s = (INR e,t) ==> ~vfm_abort e
Proof
  rewrite_tac[step_create_def, LET_THM, ignore_bind_def] >> BETA_TAC >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  map_every asm_create_prefix_tac
    [asm_call_safe_pop_stack, asm_call_safe_memory_expansion_info,
     asm_call_safe_consume_gas, asm_call_safe_expand_memory,
     asm_call_safe_read_memory, asm_call_safe_get_callee,
     asm_call_safe_get_accounts, asm_call_safe_assert,
     asm_call_safe_get_gas_left] >>
  qpat_x_assum `?d. _ = Collect d` strip_assume_tac >>
  drule_all (PURE_REWRITE_RULE[ignore_bind_def] asm_create_charged_safe) >> simp[]
QED

Theorem asm_create_raw_safe:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_create two s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [])
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_at (Pat `step_create _ _ = _`) asm_create_raw_noabort >> simp[]) >>
  rpt strip_tac >>
  `LENGTH t.contexts >= LENGTH s.contexts` by
    (mp_tac vfmStepLengthTheory.same_frame_or_grow_step_create >>
     metis_tac[vfmStepLengthTheory.same_frame_or_grow_length]) >>
  Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[]
QED

Theorem asm_call_safe_msgParams:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_msgParams op f s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_msgParams_def] >> metis_tac[asm_call_safe_context]
QED

Theorem asm_call_safe_txParams:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_txParams op f s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_txParams_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_get_tx_params] >>
  metis_tac[asm_call_safe_push_stack]
QED

Theorem asm_call_safe_jump:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_jump s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_jump_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  metis_tac[asm_call_safe_set_jump_dest]
QED

Theorem asm_call_safe_jumpi:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_jumpi s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_jumpi_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  metis_tac[asm_call_safe_set_jump_dest]
QED

Theorem asm_call_safe_dup:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_dup n s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_dup_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- (rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
      drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
      disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
      BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
      metis_tac[asm_call_safe_assert, asm_call_safe_push_stack, vfm_abort_def]) >>
  metis_tac[asm_call_safe_get_context]
QED

Theorem asm_call_safe_swap:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_swap n s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_swap_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- (rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
      drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
      disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
      BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
      metis_tac[asm_call_safe_assert, asm_call_safe_set_context, vfm_abort_def]) >>
  metis_tac[asm_call_safe_get_context]
QED

Theorem asm_call_safe_call_data_load:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_call_data_load s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_call_data_load_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_get_call_data, asm_call_safe_push_stack]
QED

Theorem asm_call_safe_step_copy_to_memory:
  (!f. source = SOME f ==> !s r t.
    s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\ f s = (r,t) ==>
    (!e. r = INR e ==> ~vfm_abort e) /\
    (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)) /\
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_copy_to_memory op source s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_copy_to_memory_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 4 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `copy_to_memory _ _ _ _ _ _ = _`) asm_call_safe_copy_to_memory >>
  simp[] >> disch_then irule >> simp[]
  >- (qpat_x_assum `!f. source = SOME f ==> _` mp_tac >>
      simp[GSYM AND_IMP_INTRO]) >>
  metis_tac[]
QED

Theorem asm_call_safe_step_mcopy:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_copy_to_memory op NONE s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  strip_tac >>
  drule_at (Pat `step_copy_to_memory _ _ _ = _`) asm_call_safe_step_copy_to_memory >>
  simp[]
QED

Theorem asm_call_safe_step_call_data_copy:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_copy_to_memory op (SOME get_call_data) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  strip_tac >>
  drule_at (Pat `step_copy_to_memory _ _ _ = _`) asm_call_safe_step_copy_to_memory >>
  simp[] >> impl_tac >- metis_tac[asm_call_safe_get_call_data] >> simp[]
QED

Theorem asm_call_safe_step_code_copy:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_copy_to_memory op (SOME get_current_code) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  strip_tac >>
  drule_at (Pat `step_copy_to_memory _ _ _ = _`) asm_call_safe_step_copy_to_memory >>
  simp[] >> impl_tac >- metis_tac[asm_call_safe_get_current_code] >> simp[]
QED

Theorem asm_call_safe_return_data_copy:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_return_data_copy s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_return_data_copy_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `copy_to_memory _ _ _ _ _ _ = _`) asm_call_safe_copy_to_memory >>
  simp[] >> impl_tac >- metis_tac[asm_call_safe_get_return_data_check] >> simp[]
QED

Theorem asm_call_safe_ext_code_copy:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_ext_code_copy s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_ext_code_copy_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_access_address] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `copy_to_memory _ _ _ _ _ _ = _`) asm_call_safe_copy_to_memory >>
  simp[] >> impl_tac >- metis_tac[asm_call_safe_get_code] >> simp[]
QED

Theorem asm_call_safe_mstore:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_mstore op s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_mstore_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_memory_expansion_info] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_expand_memory, asm_call_safe_write_memory]
QED

Theorem asm_call_safe_mload:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_mload s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_mload_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_memory_expansion_info] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_expand_memory] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_read_memory, asm_call_safe_push_stack]
QED

Theorem asm_call_safe_keccak256:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_keccak256 s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_keccak256_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_memory_expansion_info] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_expand_memory] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_read_memory, asm_call_safe_push_stack]
QED

Theorem asm_call_safe_sstore_gas_consumption:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_sstore_gas_consumption address key value s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_sstore_gas_consumption_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_get_gas_left] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_assert, vfm_abort_def] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_get_accounts] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_get_original] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_access_slot] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_update_gas_refund, asm_call_safe_consume_gas]
QED

Theorem asm_call_safe_sstore_write:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind assert_not_static (\_. if transient then write_transient_storage address key value
                              else write_storage address key value) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  Cases_on `transient` >> simp[] >>
  metis_tac[asm_call_safe_assert_not_static, asm_call_safe_write_storage,
            asm_call_safe_write_transient_storage]
QED

Theorem asm_call_safe_sstore:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_sstore transient s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `transient` >> (rewrite_tac[step_sstore_def, ignore_bind_def] >>
  simp[] >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> reverse conj_tac
  >- metis_tac[asm_call_safe_get_callee] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_sstore_gas_consumption, asm_call_safe_consume_gas,
            SRULE [] (Q.INST [`transient` |-> `T`] asm_call_safe_sstore_write),
            SRULE [] (Q.INST [`transient` |-> `F`] asm_call_safe_sstore_write)])
QED

Theorem asm_call_safe_block_hash:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_block_hash s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_block_hash_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_get_tx_params, asm_call_safe_push_stack]
QED

Theorem asm_call_safe_blob_hash:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_blob_hash s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_blob_hash_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_get_tx_params, asm_call_safe_push_stack]
QED

Theorem asm_call_safe_self_balance:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_self_balance s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_self_balance_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_get_accounts] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_get_callee, asm_call_safe_push_stack]
QED

Theorem asm_call_safe_account_query:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind (pop_stack 1) (\args.
    bind (access_address (w2w (EL 0 args))) (\cost.
    bind (consume_gas ((baseCost:num) + cost)) (\_.
    bind get_accounts (\accounts.
    push_stack (f (w2w (EL 0 args):address) accounts))))) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_access_address] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_get_accounts, asm_call_safe_push_stack]
QED

Theorem asm_call_safe_balance:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_balance s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_balance_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  irule asm_call_safe_account_query >>
  simp[] >> goal_assum (drule_at Any) >>
  qexistsl [`static_gas Balance`, `\address accounts. n2w (lookup_account address accounts).balance`] >>
  gvs[]
QED

Theorem asm_call_safe_ext_code_size:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_ext_code_size s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_ext_code_size_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  irule asm_call_safe_account_query >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl [`static_gas ExtCodeSize`, `\address accounts. n2w (LENGTH (lookup_account address accounts).code)`] >>
  gvs[]
QED

Theorem asm_call_safe_ext_code_hash:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_ext_code_hash s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_ext_code_hash_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  irule asm_call_safe_account_query >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl [`static_gas ExtCodeHash`, `\address accounts.
    if account_empty (lookup_account address accounts) then 0w else
    word_of_bytes T (0w:bytes32) (Keccak_256_w64 (lookup_account address accounts).code)`] >>
  gvs[]
QED

Theorem asm_call_safe_stop:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind (set_return_data []) (\_. finish) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  metis_tac[asm_call_safe_set_return_data, asm_call_safe_finish]
QED

Theorem asm_call_safe_return_end:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind (set_return_data bytes) (\_. if b then finish else revert) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> Cases_on `b` >> simp[] >>
  metis_tac[asm_call_safe_set_return_data, asm_call_safe_finish, asm_call_safe_revert]
QED

Theorem asm_call_safe_step_return:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_return b s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_return_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_memory_expansion_info] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> reverse conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> reverse conj_tac
  >- metis_tac[asm_call_safe_expand_memory] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_read_memory, asm_call_safe_return_end]
QED

Theorem asm_call_safe_sload_read:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind (if transient then bind get_tStorage (\ts. return (lookup_transient_storage address ts))
        else bind get_accounts (\acs. return (lookup_account address acs).storage))
       (\storage. push_stack (lookup_storage key storage)) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `transient` >> (simp[] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_get_accounts, asm_call_safe_get_tStorage,
            asm_call_safe_push_stack])
QED

Theorem asm_call_safe_sload:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_sload transient s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_sload_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> reverse conj_tac
  >- metis_tac[asm_call_safe_get_callee] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- (Cases_on `transient` >> simp[] >> metis_tac[asm_call_safe_return, asm_call_safe_access_slot]) >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_consume_gas, asm_call_safe_sload_read]
QED

Theorem asm_call_safe_log_end:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind get_callee (\address. bind (vfmExecution$read_memory offset memSize) (\bytes.
    push_logs [<| logger := address; topics := topics; data := bytes |>])) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> reverse conj_tac
  >- metis_tac[asm_call_safe_get_callee] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_read_memory, asm_call_safe_push_logs]
QED

Theorem asm_call_safe_log:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_log n s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_log_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_memory_expansion_info] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_expand_memory] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_assert_not_static, asm_call_safe_log_end]
QED

Theorem asm_call_safe_self_destruct_delete:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind (update_accounts (update_account address (sender with balance := 0)))
       (\_. add_to_delete address) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >>
  metis_tac[asm_call_safe_update_accounts, asm_call_safe_add_to_delete]
QED

Theorem asm_call_safe_self_destruct_end:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind get_original (\original.
    bind (if account_empty (lookup_account address original)
          then bind (update_accounts (update_account address (sender with balance := 0)))
                    (\_. add_to_delete address)
          else return ()) (\_. finish)) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_get_original] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  Cases_on `account_empty (lookup_account address x)` >> simp[] >>
  metis_tac[asm_call_safe_self_destruct_delete, asm_call_safe_return, asm_call_safe_finish]
QED

Theorem asm_call_safe_self_destruct_transfer:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  bind (consume_gas cost) (\_. bind assert_not_static (\_.
    bind (update_accounts (transfer_value senderAddress address sender.balance)) (\_.
    bind get_original (\original.
    bind (if account_empty (lookup_account senderAddress original)
          then bind (update_accounts (update_account senderAddress (sender with balance := 0)))
                    (\_. add_to_delete senderAddress)
          else return ()) (\_. finish))))) s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_consume_gas] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> reverse conj_tac
  >- metis_tac[asm_call_safe_assert_not_static] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_update_accounts, asm_call_safe_self_destruct_end]
QED

Theorem asm_call_safe_self_destruct:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_self_destruct s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  rewrite_tac[step_self_destruct_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then irule >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_pop_stack] >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> conj_tac
  >- metis_tac[asm_call_safe_access_address] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> reverse conj_tac
  >- metis_tac[asm_call_safe_get_callee] >>
  POP_ASSUM_LIST (K all_tac) >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >> reverse conj_tac
  >- metis_tac[asm_call_safe_set_return_data] >>
  rpt gen_tac >> pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  drule_at (Pat `bind _ _ _ = _`) asm_call_safe_bind >>
  disch_then (qspec_then `\s. s.contexts <> [] /\ ?d. s.msdomain = Collect d` mp_tac) >>
  BETA_TAC >> disch_then (irule o SRULE []) >> simp[] >>
  metis_tac[asm_call_safe_get_accounts, asm_call_safe_self_destruct_transfer]
QED

Theorem asm_call_safe_ordinary_step_inst:
  ~is_call op /\ s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_inst op s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [] /\ ?d. t.msdomain = Collect d)
Proof
  Cases_on `op` >>
  simp[is_call_def, step_inst_def, ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  FIRST (map (drule_at (Pat `_ _ = (_,_)`)) [
       asm_call_safe_binop, asm_call_safe_monop, asm_call_safe_modop,
       asm_call_safe_exp, asm_call_safe_stop, asm_call_safe_keccak256,
       asm_call_safe_msgParams, asm_call_safe_txParams, asm_call_safe_context,
       asm_call_safe_balance, asm_call_safe_call_data_load,
       asm_call_safe_step_call_data_copy, asm_call_safe_step_code_copy,
       asm_call_safe_ext_code_size, asm_call_safe_ext_code_copy,
       asm_call_safe_return_data_copy, asm_call_safe_ext_code_hash,
       asm_call_safe_block_hash, asm_call_safe_blob_hash, asm_call_safe_self_balance,
       asm_call_safe_pop, asm_call_safe_mload, asm_call_safe_mstore,
       asm_call_safe_sload, asm_call_safe_sstore, asm_call_safe_jump,
       asm_call_safe_jumpi, asm_call_safe_step_mcopy, asm_call_safe_consume_gas,
       asm_call_safe_push, asm_call_safe_dup, asm_call_safe_swap,
       asm_call_safe_log, asm_call_safe_step_return, asm_call_safe_self_destruct,
       asm_call_safe_fail]) >> simp[vfm_abort_def]
QED

Theorem asm_call_safe_call_step_inst:
  is_call op /\ s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  step_inst op s = (r,t) ==>
  (!e. r = INR e ==> ~vfm_abort e) /\
  (!x. r = INL x ==> t.contexts <> [])
Proof
  Cases_on `op` >> simp[is_call_def, step_inst_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  FIRST (map (drule_at (Pat `_ _ = (_,_)`))
    [asm_call_raw_safe, asm_create_raw_safe]) >> simp[]
QED

Theorem asm_call_inst_pc_noabort:
  s.contexts <> [] /\ (?d. s.msdomain = Collect d) /\
  (do step_inst op; inc_pc_or_jump op od) s = (INR e,t) ==> ~vfm_abort e
Proof
  Cases_on `is_call op`
  >- (rpt strip_tac >>
      gvs[inc_pc_or_jump_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
      drule_at (Pat `step_inst _ _ = _`) asm_call_safe_call_step_inst >> simp[]) >>
  rewrite_tac[ignore_bind_def] >>
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> ntac 3 disch_tac >>
  asm_create_prefix_tac asm_call_safe_ordinary_step_inst >>
  drule_at (Pat `inc_pc_or_jump _ _ = _`) asm_call_safe_inc_pc_or_jump >> simp[]
QED

Theorem asm_call_step_inner_noabort:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  step_inner s = (INR e,t) ==> ~vfm_abort e
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  qpat_x_assum `step_inner _ = _` mp_tac >>
  rewrite_tac[step_inner_def, LET_THM, ignore_bind_def] >> BETA_TAC >>
  disch_tac >> asm_create_prefix_tac asm_call_safe_get_context >>
  Cases_on `FLOOKUP x.msgParams.parsed x.pc` >> gvs[]
  >- (Cases_on `LENGTH x.msgParams.code <= x.pc` >> gvs[] >>
      drule_at (Pat `step_inst _ _ = _`) asm_call_safe_ordinary_step_inst >>
      simp[is_call_def]) >>
  drule_at (Pat `_ _ = (INR _,_)`)
    (PURE_REWRITE_RULE[ignore_bind_def] asm_call_inst_pc_noabort) >> simp[]
QED

Theorem asm_call_nested_step_inl:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  2 <= LENGTH s.contexts /\ step s = (q,t) ==> ISL q
Proof
  strip_tac >>
  qpat_x_assum `step _ = _` mp_tac >>
  rewrite_tac[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> rename1 `step_inner s = (result,mid)` >>
  Cases_on `result`
  >- simp[] >>
  rename1 `step_inner s = (INR exc,mid)` >>
  simp[] >> disch_tac >>
  `~vfm_abort exc` by
    (drule_at (Pat `step_inner _ = _`) asm_call_step_inner_noabort >> simp[]) >>
  drule_all asm_call_nested_handler_inl >> simp[]
QED

Theorem asm_call_nested_run_inl:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  2 <= LENGTH s.contexts /\ run_call s = SOME (r,t) ==> ISL r
Proof
  strip_tac >> gvs[run_call_def] >>
  `(\p. wf_state (SND p) /\ (?d. (SND p).msdomain = Collect d) /\
        ISL (FST p)) (r,t)` suffices_by simp[] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  goal_assum $ drule_at Any >> simp[] >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp[] >> strip_tac >>
  Cases_on `step p1` >> rename1 `step p1 = (res,mid)` >> simp[] >>
  conj_tac >- (drule_all step_preserves_wf_state >> simp[]) >>
  conj_tac
  >- (drule_at (Pat `step _ = _`) step_preserves_collect >> simp[]) >>
  `2 <= LENGTH p1.contexts` by decide_tac >>
  drule_at (Pat `step _ = _`) asm_call_nested_step_inl >> simp[]
QED

Theorem asm_call_run_collect:
  (?d. s.msdomain = Collect d) /\ run_call s = SOME (r,t) ==>
  ?d. t.msdomain = Collect d
Proof
  strip_tac >> gvs[run_call_def] >>
  `(\p. ?d. (SND p).msdomain = Collect d) (r,t)` suffices_by simp[] >>
  irule (MP_CANON WhileTheory.OWHILE_INV_IND) >>
  goal_assum $ drule_at Any >> simp[] >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp[] >> strip_tac >>
  Cases_on `step p1` >> rename1 `step p1 = (res,mid)` >> simp[] >>
  drule_at (Pat `step _ = _`) step_preserves_collect >> simp[]
QED

Theorem asm_call_child_run_normal:
  wf_state child /\ (?d. child.msdomain = Collect d) /\
  2 <= LENGTH child.contexts ==>
  ?t. run_call child = SOME (INL (),t) /\ wf_state t /\
      LENGTH t.contexts + 1 = LENGTH child.contexts /\
      (?d. t.msdomain = Collect d)
Proof
  strip_tac >> drule_all asm_call_child_run_classify >>
  disch_then (qx_choose_then `r` (qx_choose_then `t` strip_assume_tac)) >>
  `ISL r` by
    (drule_at (Pat `run_call _ = _`) asm_call_nested_run_inl >> simp[]) >>
  `?d. t.msdomain = Collect d` by
    (drule_at (Pat `run_call _ = _`) asm_call_run_collect >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem asm_call_create_push_saved_tail:
  s.contexts <> [] /\
  proceed_create sender address value code gas s = (r,t) ==>
  TL t.contexts = s.contexts
Proof
  strip_tac >>
  qpat_x_assum `proceed_create _ _ _ _ _ _ = _` mp_tac >>
  simp[proceed_create_def, update_accounts_def, get_rollback_def,
       get_original_def, set_original_def, push_context_def,
       ignore_bind_def, bind_def, return_def, fail_def] >>
  strip_tac >> gvs[]
QED

Theorem asm_call_nested_memory_pop_saved_tail:
  s.contexts = (child,crb)::(parent,prb)::saved /\
  child.msgParams.outputTo = Memory mr /\
  LENGTH parent.stack < stack_limit /\
  child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed /\
  handle_exception NONE s = (q,t) ==>
  TL t.contexts = saved
Proof
  strip_tac >> drule_all asm_handle_exception_memory_success >>
  simp[] >> strip_tac >> gvs[]
QED

Definition asm_call_saved_suffix_def:
  asm_call_saved_suffix saved s <=>
    ?active. active <> [] /\ s.contexts = active ++ saved
End

Theorem asm_call_saved_suffix_intro:
  active <> [] /\ s.contexts = active ++ saved ==>
  asm_call_saved_suffix saved s
Proof
  metis_tac[asm_call_saved_suffix_def]
QED

Theorem asm_call_saved_suffix_view:
  asm_call_saved_suffix saved s <=>
  ?head active. s.contexts = head::(active ++ saved)
Proof
  simp[asm_call_saved_suffix_def] >> eq_tac
  >- (strip_tac >> Cases_on `active` >> gvs[] >> metis_tac[])
  >> strip_tac >> qexists_tac `head::active` >> simp[]
QED

Theorem asm_call_saved_suffix_depth:
  asm_call_saved_suffix saved s ==>
  s.contexts <> [] /\ LENGTH saved < LENGTH s.contexts
Proof
  simp[asm_call_saved_suffix_view] >> rpt strip_tac >> gvs[]
QED

Theorem asm_call_saved_suffix_same_frame:
  same_frame_rel s t /\ asm_call_saved_suffix saved s ==>
  asm_call_saved_suffix saved t
Proof
  simp[asm_call_saved_suffix_view, vfmSameFrameTheory.same_frame_rel_def] >>
  rpt strip_tac >> Cases_on `t.contexts` >> gvs[] >> metis_tac[]
QED

Theorem asm_call_saved_suffix_psf:
  preserves_same_frame f ==> !s. asm_call_saved_suffix saved s ==>
  asm_call_saved_suffix saved (SND (f s))
Proof
  simp[vfmSameFrameTheory.preserves_same_frame_def] >> rpt strip_tac >>
  drule asm_call_saved_suffix_depth >> strip_tac >>
  Cases_on `f s` >> simp[] >>
  irule asm_call_saved_suffix_same_frame >>
  goal_assum $ drule_at Any >> first_x_assum irule >> simp[]
QED

Theorem asm_call_saved_suffix_bind:
  (!s. asm_call_saved_suffix saved s ==>
       asm_call_saved_suffix saved (SND (g s))) /\
  (!x s. asm_call_saved_suffix saved s ==>
         asm_call_saved_suffix saved (SND (f x s))) ==>
  !s. asm_call_saved_suffix saved s ==>
      asm_call_saved_suffix saved (SND (bind g f s))
Proof
  rpt strip_tac >> simp[bind_def] >>
  Cases_on `g s` >> rename1 `g s = (res,mid)` >>
  `asm_call_saved_suffix saved mid` by metis_tac[pairTheory.SND] >>
  Cases_on `res` >> simp[] >> metis_tac[]
QED

Theorem asm_call_saved_suffix_ignore_bind:
  (!s. asm_call_saved_suffix saved s ==>
       asm_call_saved_suffix saved (SND (g s))) /\
  (!s. asm_call_saved_suffix saved s ==>
       asm_call_saved_suffix saved (SND (f s))) ==>
  !s. asm_call_saved_suffix saved s ==>
      asm_call_saved_suffix saved (SND (ignore_bind g f s))
Proof
  simp[ignore_bind_def] >> strip_tac >>
  ho_match_mp_tac asm_call_saved_suffix_bind >> simp[]
QED

Theorem asm_call_saved_suffix_proceed_create:
  asm_call_saved_suffix saved s ==>
  asm_call_saved_suffix saved
    (SND (proceed_create sender address value code gas s))
Proof
  strip_tac >> drule asm_call_saved_suffix_depth >> strip_tac >>
  Cases_on `proceed_create sender address value code gas s` >> simp[] >>
  drule_all asm_call_create_push_saved_tail >> strip_tac >>
  fs[asm_call_saved_suffix_def] >>
  Cases_on `r.contexts` >> gvs[] >>
  qexists_tac `h::active` >> simp[]
QED

Theorem asm_call_saved_suffix_abort_create_exists:
  !s. asm_call_saved_suffix saved s ==>
  asm_call_saved_suffix saved (SND (abort_create_exists senderAddress s))
Proof
  rewrite_tac[abort_create_exists_def] >>
  ho_match_mp_tac asm_call_saved_suffix_ignore_bind >> conj_tac
  >- simp[asm_call_saved_suffix_def, update_accounts_contexts]
  >> ho_match_mp_tac asm_call_saved_suffix_ignore_bind >> conj_tac >>
  gen_tac >> qmatch_goalsub_abbrev_tac `SND (action s)` >>
  `preserves_same_frame action` by simp[Abbr `action`] >>
  drule asm_call_saved_suffix_psf >> simp[]
QED

Theorem asm_call_saved_suffix_step_create:
  !s. asm_call_saved_suffix saved s ==>
  asm_call_saved_suffix saved (SND (step_create two s))
Proof
  rewrite_tac[step_create_def] >> simp_tac (srw_ss()) [LET_THM] >>
  rpt (FIRST [
    ho_match_mp_tac asm_call_saved_suffix_bind >> conj_tac,
    ho_match_mp_tac asm_call_saved_suffix_ignore_bind >> conj_tac,
    (qmatch_goalsub_abbrev_tac `SND (action s)` >>
     `preserves_same_frame action` by simp[Abbr `action`] >>
     drule asm_call_saved_suffix_psf >> simp[] >> NO_TAC),
    (simp[asm_call_saved_suffix_proceed_create,
          asm_call_saved_suffix_abort_create_exists] >> NO_TAC),
    (qid_spec_tac `s` >> ho_match_mp_tac asm_call_saved_suffix_bind >> conj_tac),
    (qid_spec_tac `s` >> ho_match_mp_tac asm_call_saved_suffix_ignore_bind >> conj_tac),
    gen_tac,
    IF_CASES_TAC,
    CHANGED_TAC (simp_tac (srw_ss()) [LET_THM])])
QED

Theorem asm_call_saved_suffix_step_grow:
  wf_state s /\ asm_call_saved_suffix saved s /\ step s = (r,t) /\
  LENGTH s.contexts < LENGTH t.contexts ==>
  asm_call_saved_suffix saved t
Proof
  strip_tac >> drule_all step_grow_dispatch >> strip_tac
  >- (drule asm_call_saved_suffix_depth >> strip_tac >>
      drule step_call_push_structure >> simp[] >> strip_tac >>
      fs[asm_call_saved_suffix_view] >>
      namedCases_on `t.contexts` ["", "child remaining"] >> gvs[] >>
      namedCases_on `remaining` ["", "parent tail"] >> gvs[] >>
      qexists_tac `child` >> simp[])
  >> drule asm_call_saved_suffix_step_create >>
  disch_then (qspec_then `two` mp_tac) >> simp[]
QED

Theorem asm_call_saved_suffix_step:
  wf_state s /\ asm_call_saved_suffix saved s /\ step s = (r,t) /\
  LENGTH saved < LENGTH t.contexts ==>
  asm_call_saved_suffix saved t
Proof
  strip_tac >> Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (irule asm_call_saved_suffix_step_grow >> metis_tac[])
  >> Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac >>
      fs[asm_call_saved_suffix_view] >>
      Cases_on `t.contexts` >> gvs[] >> metis_tac[])
  >> `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_foreign >> strip_tac >>
  fs[asm_call_saved_suffix_def] >>
  namedCases_on `active` ["", "first others"] >> gvs[] >>
  namedCases_on `others` ["", "second above"] >> gvs[] >>
  qexists_tac `(new_head,SND parent)::above` >> simp[]
QED

Theorem asm_call_saved_suffix_finite:
  !n. wf_state s /\ asm_call_saved_suffix saved s /\
    (!k. k <= n ==>
      LENGTH saved < LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts) ==>
    wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
    asm_call_saved_suffix saved (SND (FUNPOW (step o SND) n (INL (),s)))
Proof
  Induct >- simp[] >> strip_tac >>
  `wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
   asm_call_saved_suffix saved (SND (FUNPOW (step o SND) n (INL (),s)))` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  simp[arithmeticTheory.FUNPOW_SUC] >> qmatch_goalsub_abbrev_tac `step mid` >>
  `wf_state mid /\ asm_call_saved_suffix saved mid` by simp[Abbr `mid`] >>
  `LENGTH saved < LENGTH (SND (step mid)).contexts` by
    (first_x_assum (qspec_then `SUC n` mp_tac) >> simp[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  Cases_on `step mid` >> gvs[] >> conj_tac
  >- (drule_all step_preserves_wf_state >> simp[])
  >> irule asm_call_saved_suffix_step >> metis_tac[]
QED

Theorem asm_call_child_trace_saved_suffix:
  wf_state s /\ s.contexts = child::(parent::rest) /\
  (!k. k <= n ==>
    LENGTH (parent::rest) <
      LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts) ==>
  ?active. active <> [] /\
    (SND (FUNPOW (step o SND) n (INL (),s))).contexts =
      active ++ (parent::rest)
Proof
  strip_tac >>
  `asm_call_saved_suffix (parent::rest) s` by
    (simp[asm_call_saved_suffix_view] >> metis_tac[APPEND]) >>
  drule_all asm_call_saved_suffix_finite >>
  simp[asm_call_saved_suffix_def]
QED

(* The saved suffix is intentionally unconstrained: the caller need not be static. *)
Theorem asm_call_cp_static_prefix:
  cp f /\ f s = (r,t) /\ active <> [] /\
  s.contexts = active ++ saved /\
  s.rollback.accounts = a /\ s.rollback.tStorage = ts /\
  s.rollback.toDelete = ds /\
  EVERY (\(c,rb). c.msgParams.static /\
    (!x. c.msgParams.outputTo <> Code x) /\ c.logs = [] /\
    rb.accounts = a /\ rb.tStorage = ts /\ rb.toDelete = ds) active ==>
  t.rollback.accounts = a /\ t.rollback.tStorage = ts /\
  t.rollback.toDelete = ds /\
  ?active'. active' <> [] /\ LENGTH active' = LENGTH active /\
    t.contexts = active' ++ saved /\
    EVERY (\(c,rb). c.msgParams.static /\
      (!x. c.msgParams.outputTo <> Code x) /\ c.logs = [] /\
      rb.accounts = a /\ rb.tStorage = ts /\ rb.toDelete = ds) active'
Proof
  strip_tac >> Cases_on `active` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  qpat_x_assum `cp f` mp_tac >> simp[cp_def] >>
  disch_then drule >> simp[] >> strip_tac >> gvs[] >>
  qexists_tac `(q',h1)::t'` >> simp[]
QED

Theorem asm_call_static_push_snapshot:
  s.contexts = (c,rb)::saved /\ c.msgParams.static /\
  ~fIN address precompile_addresses /\
  proceed_call op sender address 0 ao az code stipend (Memory mr) s = (r,t) ==>
  t.rollback = s.rollback /\ TL t.contexts = s.contexts /\
  (FST (HD t.contexts)).msgParams.static /\
  (FST (HD t.contexts)).msgParams.outputTo = Memory mr /\
  (FST (HD t.contexts)).logs = [] /\
  SND (HD t.contexts) = s.rollback
Proof
  strip_tac >> qpat_x_assum `proceed_call _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[proceed_call_def, get_rollback_def, read_memory_def,
       get_caller_def, get_value_def, get_static_def,
       get_current_context_def, push_context_def,
       vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def,
       bind_def, ignore_bind_def, return_def] >>
  strip_tac >> gvs[]
QED

Theorem asm_call_static_memory_pop_effects:
  s.contexts = (child,crb)::(parent,prb)::saved /\
  child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
  LENGTH parent.stack < stack_limit /\
  child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed /\
  crb.accounts = s.rollback.accounts /\
  crb.tStorage = s.rollback.tStorage /\
  crb.toDelete = s.rollback.toDelete /\
  (ex <> NONE /\ ex <> SOME Reverted ==>
    child.gasUsed <= child.msgParams.gasLimit) /\
  handle_exception ex s = (q,t) ==>
  t.rollback.accounts = s.rollback.accounts /\
  t.rollback.tStorage = s.rollback.tStorage /\
  t.rollback.toDelete = s.rollback.toDelete /\
  (FST (HD t.contexts)).logs = parent.logs /\
  TL t.contexts = saved
Proof
  strip_tac >> Cases_on `ex`
  >- (drule_all asm_handle_exception_memory_success >> simp[] >>
      strip_tac >> gvs[])
  >> Cases_on `x = Reverted`
  >- (qpat_x_assum `x = Reverted` SUBST_ALL_TAC >>
      drule_all asm_handle_exception_memory_reverted >> simp[] >>
      strip_tac >> gvs[])
  >> drule asm_handle_exception_memory_exception >> simp[] >>
  strip_tac >> gvs[]
QED

Definition asm_call_static_prefix_def:
  asm_call_static_prefix saved a ts ds s <=>
    s.rollback.accounts = a /\ s.rollback.tStorage = ts /\
    s.rollback.toDelete = ds /\
    ?active. active <> [] /\ s.contexts = active ++ saved /\
      EVERY (\(c,rb). c.msgParams.static /\
        (!x. c.msgParams.outputTo <> Code x) /\ c.logs = [] /\
        rb.accounts = a /\ rb.tStorage = ts /\ rb.toDelete = ds) active
End

Theorem asm_call_static_prefix_intro:
  s.rollback.accounts = a /\ s.rollback.tStorage = ts /\
  s.rollback.toDelete = ds /\ active <> [] /\
  s.contexts = active ++ saved /\
  EVERY (\(c,rb). c.msgParams.static /\
    (!x. c.msgParams.outputTo <> Code x) /\ c.logs = [] /\
    rb.accounts = a /\ rb.tStorage = ts /\ rb.toDelete = ds) active ==>
  asm_call_static_prefix saved a ts ds s
Proof
  rw[asm_call_static_prefix_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem asm_call_static_prefix_head:
  asm_call_static_prefix saved a ts ds s ==>
  s.contexts <> [] /\ (FST (HD s.contexts)).msgParams.static /\
  (!x. (FST (HD s.contexts)).msgParams.outputTo <> Code x) /\
  (FST (HD s.contexts)).logs = [] /\
  (SND (HD s.contexts)).accounts = a /\
  (SND (HD s.contexts)).tStorage = ts /\
  (SND (HD s.contexts)).toDelete = ds
Proof
  rw[asm_call_static_prefix_def] >> Cases_on `active` >> gvs[] >>
  PairCases_on `h` >> gvs[]
QED

Theorem asm_call_static_prefix_cp:
  cp f /\ asm_call_static_prefix saved a ts ds s /\ f s = (r,t) ==>
  asm_call_static_prefix saved a ts ds t
Proof
  strip_tac >> fs[asm_call_static_prefix_def] >>
  drule_at (Pat `EVERY _ _`) asm_call_cp_static_prefix >>
  disch_then drule_all >> simp[] >> strip_tac >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem asm_call_static_prefix_push:
  asm_call_static_prefix saved a ts ds s /\
  ~fIN address precompile_addresses /\
  proceed_call op sender address 0 ao az code stipend (Memory mr) s = (r,t) ==>
  asm_call_static_prefix saved a ts ds t
Proof
  strip_tac >> drule asm_call_static_prefix_head >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> fs[] >>
  drule asm_call_static_push_snapshot >> simp[] >> disch_then drule_all >>
  strip_tac >> gvs[asm_call_static_prefix_def] >>
  qexists_tac `HD t.contexts :: active` >> simp[] >>
  Cases_on `t.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
QED

Theorem asm_call_static_prefix_cp_snd:
  cp f /\ asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (f s))
Proof
  strip_tac >> Cases_on `f s` >> simp[] >>
  drule_all asm_call_static_prefix_cp >> simp[]
QED

Theorem asm_call_static_prefix_bind_cp:
  cp g /\
  (!x t. asm_call_static_prefix saved a ts ds t ==>
    asm_call_static_prefix saved a ts ds (SND (f x t))) /\
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (bind g f s))
Proof
  strip_tac >> drule_all asm_call_static_prefix_cp_snd >>
  simp[bind_def] >> Cases_on `g s` >> Cases_on `q` >> simp[]
QED

Theorem asm_call_static_prefix_ignore_bind_cp:
  cp g /\
  (!t. asm_call_static_prefix saved a ts ds t ==>
    asm_call_static_prefix saved a ts ds (SND (f t))) /\
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (ignore_bind g f s))
Proof
  simp[ignore_bind_def] >> strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[]
QED

Theorem asm_call_static_prefix_assert:
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds
    (SND (bind assert_not_static f s))
Proof
  strip_tac >> drule asm_call_static_prefix_head >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> fs[] >>
  drule_all assert_not_static_static >>
  simp[bind_def] >> disch_then SUBST1_TAC >> simp[]
QED

Theorem asm_call_static_prefix_ignore_assert:
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds
    (SND (ignore_bind assert_not_static f s))
Proof
  simp[ignore_bind_def, asm_call_static_prefix_assert]
QED

Theorem asm_call_static_prefix_sstore:
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (step_sstore transient s))
Proof
  strip_tac >> simp[step_sstore_def] >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_assert >> simp[]
QED

Theorem asm_call_static_prefix_log:
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (step_log n s))
Proof
  strip_tac >> simp[step_log_def] >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_assert >> simp[]
QED

Theorem asm_call_static_prefix_self_destruct:
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (step_self_destruct s))
Proof
  strip_tac >> simp[step_self_destruct_def] >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_assert >> simp[]
QED

Theorem asm_call_static_prefix_create:
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (step_create two s))
Proof
  strip_tac >> simp[step_create_def] >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_ignore_assert >> simp[]
QED

Theorem asm_call_static_prefix_proceed_call:
  asm_call_static_prefix saved a ts ds s /\
  (value = 0 \/ op = CallCode) ==>
  asm_call_static_prefix saved a ts ds
    (SND (proceed_call op sender address value ao az code stipend (Memory mr) s))
Proof
  strip_tac >> drule asm_call_static_prefix_head >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >> fs[] >>
  simp[proceed_call_def, get_rollback_def, read_memory_def,
       get_caller_def, get_value_def, get_static_def,
       get_current_context_def, push_context_def,
       bind_def, ignore_bind_def, return_def] >>
  irule asm_call_static_prefix_cp_snd >> simp[] >>
  gvs[asm_call_static_prefix_def] >>
  simp[vfmContextTheory.initial_context_def,
       vfmContextTheory.initial_msg_params_def]
QED

Theorem asm_call_static_prefix_uncurry:
  (!x y. asm_call_static_prefix saved a ts ds (SND (f x y s))) ==>
  asm_call_static_prefix saved a ts ds (SND (UNCURRY f p s))
Proof
  Cases_on `p` >> simp[]
QED

Theorem asm_call_static_prefix_guard:
  asm_call_static_prefix saved a ts ds s /\
  (~b ==> asm_call_static_prefix saved a ts ds (SND (f s))) ==>
  asm_call_static_prefix saved a ts ds
    (SND (ignore_bind (if b then assert_not_static else return ()) f s))
Proof
  Cases_on `b`
  >- simp[asm_call_static_prefix_ignore_assert] >>
  simp[ignore_bind_def, bind_def, return_def]
QED

Theorem asm_call_static_prefix_cond:
  asm_call_static_prefix saved a ts ds (SND (f s)) /\
  asm_call_static_prefix saved a ts ds (SND (g s)) ==>
  asm_call_static_prefix saved a ts ds (SND ((if b then f else g) s))
Proof
  Cases_on `b` >> simp[]
QED

Theorem asm_call_static_prefix_step_call:
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (step_call op s))
Proof
  strip_tac >> simp[step_call_def] >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_uncurry >> rpt gen_tac >> simp[] >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_uncurry >> rpt gen_tac >> simp[] >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_uncurry >> rpt gen_tac >> simp[] >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_guard >> simp[] >> strip_tac >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_cond >> conj_tac
  >- (irule asm_call_static_prefix_cp_snd >> simp[]) >>
  irule asm_call_static_prefix_ignore_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_bind_cp >> simp[] >> rpt strip_tac >>
  irule asm_call_static_prefix_cond >> conj_tac
  >- (irule asm_call_static_prefix_cp_snd >> simp[]) >>
  irule asm_call_static_prefix_proceed_call >> simp[] >>
  Cases_on `op` >> gvs[call_has_value_def]
QED

Theorem asm_call_static_prefix_step_inst:
  asm_call_static_prefix saved a ts ds s ==>
  asm_call_static_prefix saved a ts ds (SND (step_inst op s))
Proof
  strip_tac >> Cases_on `cp (step_inst op)`
  >- (irule asm_call_static_prefix_cp_snd >> simp[]) >>
  Cases_on `op` >> fs[] >>
  simp[step_inst_def, asm_call_static_prefix_sstore,
       asm_call_static_prefix_log, asm_call_static_prefix_self_destruct,
       asm_call_static_prefix_create, asm_call_static_prefix_step_call]
QED

Theorem asm_call_static_prefix_inner:
  asm_call_static_prefix saved a ts ds s /\
  (do
    ctxt <- get_current_context;
    case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
    | SOME op => do step_inst op; inc_pc_or_jump op od
    | NONE => if LENGTH ctxt.msgParams.code <= ctxt.pc then step_inst Stop
              else step_inst Invalid
  od) s = (r,t) ==>
  asm_call_static_prefix saved a ts ds t
Proof
  strip_tac >> drule asm_call_static_prefix_head >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  gvs[bind_def, get_current_context_def, return_def] >>
  Cases_on `FLOOKUP h0.msgParams.parsed h0.pc` >> gvs[]
  >- (Cases_on `LENGTH h0.msgParams.code <= h0.pc` >> gvs[] >>
      drule_at (Pos (el 3)) asm_call_static_prefix_cp >> simp[]) >>
  gvs[ignore_bind_def, bind_def] >>
  drule asm_call_static_prefix_step_inst >>
  disch_then (qspec_then `x` assume_tac) >>
  Cases_on `step_inst x s` >> Cases_on `q` >> gvs[] >>
  metis_tac[asm_call_static_prefix_cp, cp_inc_pc_or_jump]
QED

Theorem asm_call_static_prefix_internal_pop:
  asm_call_static_prefix saved a ts ds s /\
  LENGTH saved + 1 < LENGTH s.contexts /\
  LENGTH (FST (HD (TL s.contexts))).stack < stack_limit /\
  (FST (HD s.contexts)).msgParams.gasLimit - (FST (HD s.contexts)).gasUsed <=
    (FST (HD (TL s.contexts))).gasUsed /\
  (ex <> NONE /\ ex <> SOME Reverted ==>
    (FST (HD s.contexts)).gasUsed <= (FST (HD s.contexts)).msgParams.gasLimit) /\
  handle_exception ex s = (q,t) ==>
  asm_call_static_prefix saved a ts ds t
Proof
  strip_tac >> fs[asm_call_static_prefix_def] >>
  Cases_on `active` >> gvs[] >> PairCases_on `h` >> fs[] >>
  Cases_on `t'` >> gvs[] >> PairCases_on `h` >> fs[] >>
  Cases_on `h0.msgParams.outputTo` >> fs[] >>
  Cases_on `ex`
  >- (drule asm_handle_exception_memory_success >> simp[] >>
      strip_tac >> gvs[asm_call_static_prefix_def]) >>
  Cases_on `x = Reverted`
  >- (qpat_x_assum `x = Reverted` SUBST_ALL_TAC >>
      drule asm_handle_exception_memory_reverted >> simp[] >>
      strip_tac >> gvs[asm_call_static_prefix_def]) >>
  drule asm_handle_exception_memory_exception >> simp[] >>
  strip_tac >> gvs[asm_call_static_prefix_def]
QED

Theorem asm_call_memory_pop_bounds:
  2 <= LENGTH s.contexts /\ EVERY (wf_context o FST) s.contexts /\
  stack_room_ok s /\ gas_stack_ok s ==>
  LENGTH (FST (HD (TL s.contexts))).stack < stack_limit /\
  (FST (HD s.contexts)).msgParams.gasLimit - (FST (HD s.contexts)).gasUsed <=
    (FST (HD (TL s.contexts))).gasUsed /\
  (FST (HD s.contexts)).gasUsed <= (FST (HD s.contexts)).msgParams.gasLimit
Proof
  strip_tac >> Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  Cases_on `t` >> gvs[] >> PairCases_on `h` >>
  fs[stack_room_ok_def, wf_context_def] >>
  qpat_x_assum `gas_stack_ok _` mp_tac >> simp[gas_stack_ok_def] >>
  disch_then (qspec_then `0` mp_tac) >> simp[unused_gas_def]
QED

Theorem asm_call_static_prefix_internal_pop_safe:
  asm_call_static_prefix saved a ts ds s /\
  LENGTH saved + 1 < LENGTH s.contexts /\
  EVERY (wf_context o FST) s.contexts /\ stack_room_ok s /\ gas_stack_ok s /\
  handle_exception ex s = (q,t) ==>
  asm_call_static_prefix saved a ts ds t
Proof
  strip_tac >>
  `2 <= LENGTH s.contexts` by decide_tac >>
  drule_all asm_call_memory_pop_bounds >> strip_tac >>
  drule_at (Pat `handle_exception _ _ = _`) asm_call_static_prefix_internal_pop >>
  simp[]
QED

Theorem asm_call_static_prefix_step_inner:
  asm_call_static_prefix saved a ts ds s /\ step_inner s = (r,t) ==>
  asm_call_static_prefix saved a ts ds t
Proof
  simp[step_inner_def] >> metis_tac[asm_call_static_prefix_inner]
QED

Theorem asm_call_step_inner_pop_invariants:
  wf_state s /\ step_inner s = (r,t) ==>
  EVERY (wf_context o FST) t.contexts /\ stack_room_ok t /\ gas_stack_ok t
Proof
  strip_tac >> drule_all step_inner_preserves_stack_room_gas_ok >> strip_tac >>
  simp[] >> mp_tac decreases_gas_cred_step_inner >>
  simp[decreases_gas_cred_def] >> disch_then (qspec_then `s` mp_tac) >>
  simp[wf_state_def] >> strip_tac >> gvs[wf_state_def]
QED

Theorem asm_call_step_drop_raw_view:
  wf_state s /\ s.contexts <> [] /\ step s = (r,t) /\
  LENGTH t.contexts < LENGTH s.contexts ==>
  ?ex u. step_inner s = (INR ex,u) /\ handle_step ex u = (r,t) /\
    same_frame_rel s u /\
    EVERY (wf_context o FST) u.contexts /\ stack_room_ok u /\ gas_stack_ok u
Proof
  strip_tac >> qpat_x_assum `step s = _` mp_tac >>
  simp[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q` >> simp[]
  >- (strip_tac >> gvs[] >>
      assume_tac same_frame_or_grow_step_inner_named >>
      drule_all same_frame_or_grow_length >> strip_tac >>
      strip_tac >> gvs[])
  >> strip_tac >>
  `LENGTH s.contexts <= LENGTH r'.contexts` by
    (assume_tac same_frame_or_grow_step_inner_named >>
     drule_all same_frame_or_grow_length >> simp[]) >>
  `r'.contexts <> []` by (Cases_on `r'.contexts` >> gvs[]) >>
  `LENGTH r'.contexts <= LENGTH t.contexts + 1` by
    (drule vfmHandleStepTheory.handle_step_shrinks_by_one >> simp[]) >>
  `LENGTH r'.contexts = LENGTH s.contexts` by decide_tac >>
  `same_frame_rel s r'` by
    (assume_tac same_frame_or_grow_step_inner_named >>
     drule_all same_frame_or_grow_eq_length >> simp[]) >>
  drule_all asm_call_step_inner_pop_invariants >> strip_tac >>
  simp[]
QED

Theorem asm_call_memory_handle_step:
  s.contexts <> [] /\
  (FST (HD s.contexts)).msgParams.outputTo = Memory mr /\
  ~vfm_abort ex ==>
  handle_step ex s = handle_exception ex s
Proof
  strip_tac >>
  `!a. (FST (HD s.contexts)).msgParams.outputTo <> Code a` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises) >>
  disch_then (qspec_then `ex` assume_tac) >>
  simp[handle_step_def, handle_def, reraise_def]
QED

Theorem asm_call_push_message_tail:
  wf_state s /\ step s = (r,t) /\
  LENGTH s.contexts < LENGTH t.contexts ==>
  MAP (\p. (FST p).msgParams) (TL t.contexts) =
  MAP (\p. (FST p).msgParams) s.contexts
Proof
  strip_tac >>
  `s.contexts <> [] /\ outputTo_consistent_stack s` by gvs[wf_state_def] >>
  drule step_push_structure >> simp[] >> strip_tac >>
  Cases_on `s.contexts` >> gvs[] >>
  namedCases_on `t.contexts` ["", "child below"] >> gvs[] >>
  namedCases_on `below` ["", "parent rest"] >> gvs[] >>
  fs[MAP_MAP_o, combinTheory.o_DEF] >>
  qpat_x_assum `MAP FST rest = _` (mp_tac o AP_TERM ``MAP (\c:context. c.msgParams)``) >>
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem asm_call_message_last:
  a <> [] /\ b <> [] /\
  MAP (\p. (FST p).msgParams) a = MAP (\p. (FST p).msgParams) b ==>
  (FST (LAST a)).msgParams = (FST (LAST b)).msgParams
Proof
  strip_tac >>
  qpat_x_assum `MAP _ a = _` (mp_tac o AP_TERM ``LAST : message_parameters list -> message_parameters``) >>
  simp[LAST_MAP]
QED

Theorem asm_call_bottom_message_step:
  wf_state s /\ active <> [] /\ s.contexts = active ++ saved /\
  step s = (r,t) /\ LENGTH saved < LENGTH t.contexts ==>
  ?active'. active' <> [] /\ t.contexts = active' ++ saved /\
    (FST (LAST active')).msgParams = (FST (LAST active)).msgParams
Proof
  strip_tac >>
  `asm_call_saved_suffix saved s` by
    (simp[asm_call_saved_suffix_def] >> metis_tac[]) >>
  drule_all asm_call_saved_suffix_step >>
  simp[asm_call_saved_suffix_def] >> strip_tac >>
  rename1 `t.contexts = next ++ saved` >>
  qexists_tac `next` >> simp[] >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (drule_all asm_call_push_message_tail >>
      Cases_on `next` >> gvs[] >>
      Cases_on `t'` >> gvs[MAP_APPEND] >>
      strip_tac >> irule asm_call_message_last >> simp[] >> metis_tac[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac >>
      Cases_on `active` >> Cases_on `next` >> gvs[] >>
      Cases_on `t'` >> gvs[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_foreign >> strip_tac >>
  namedCases_on `active` ["", "first others"] >> gvs[] >>
  namedCases_on `others` ["", "second above"] >> gvs[] >>
  Cases_on `above` >> gvs[]
QED

Theorem asm_call_bottom_message_finite:
  !n. wf_state s /\ s.contexts = child::saved /\
    (!k. k <= n ==>
      LENGTH saved < LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts) ==>
    wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
    ?active. active <> [] /\
      (SND (FUNPOW (step o SND) n (INL (),s))).contexts = active ++ saved /\
      (FST (LAST active)).msgParams = (FST child).msgParams
Proof
  Induct
  >- (strip_tac >> simp[] >> qexists_tac `[child]` >> simp[]) >>
  strip_tac >>
  `wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
   ?active. active <> [] /\
     (SND (FUNPOW (step o SND) n (INL (),s))).contexts = active ++ saved /\
     (FST (LAST active)).msgParams = (FST child).msgParams` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  qmatch_goalsub_abbrev_tac `step mid` >>
  `wf_state mid /\ mid.contexts = active ++ saved` by simp[Abbr `mid`] >>
  `LENGTH saved < LENGTH (SND (step mid)).contexts` by
    (first_x_assum (qspec_then `SUC n` mp_tac) >>
     simp[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  Cases_on `step mid` >> gvs[] >> conj_tac
  >- (drule_all step_preserves_wf_state >> simp[]) >>
  drule_all asm_call_bottom_message_step >> strip_tac >>
  qexists_tac `active'` >> simp[]
QED

Theorem asm_call_trace_before_final_pop:
  wf_state s /\ s.contexts = child::saved /\
  (!k. k <= n ==>
    LENGTH saved < LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts) /\
  mid = SND (FUNPOW (step o SND) n (INL (),s)) /\
  step mid = (r,t) /\ LENGTH t.contexts = LENGTH saved ==>
  wf_state mid /\ ?c rb. mid.contexts = (c,rb)::saved /\
    c.msgParams = (FST child).msgParams
Proof
  strip_tac >> drule_all asm_call_bottom_message_finite >> strip_tac >>
  gvs[] >>
  drule_all step_length_not_drop_more_than_one >> strip_tac >>
  namedCases_on `active` ["", "head tail"] >> gvs[] >>
  `tail = []` by (Cases_on `tail` >> gvs[]) >> gvs[] >>
  PairCases_on `head` >> gvs[]
QED

Theorem asm_call_final_memory_raw:
  wf_state mid /\ (?d. mid.msdomain = Collect d) /\
  mid.contexts = (c,rb)::(parent,prb)::rest /\
  c.msgParams.outputTo = Memory mr /\
  step mid = (r,t) /\ LENGTH t.contexts < LENGTH mid.contexts ==>
  ?ex u c'. step_inner mid = (INR ex,u) /\
    u.contexts = (c',rb)::(parent,prb)::rest /\
    c'.msgParams = c.msgParams /\ ~vfm_abort ex /\
    handle_exception ex u = (r,t) /\
    EVERY (wf_context o FST) u.contexts /\ stack_room_ok u /\ gas_stack_ok u
Proof
  strip_tac >>
  `mid.contexts <> []` by simp[] >>
  drule_all asm_call_step_drop_raw_view >> strip_tac >>
  `~vfm_abort ex` by
    (drule_at (Pat `step_inner _ = _`) asm_call_step_inner_noabort >> simp[]) >>
  qpat_x_assum `same_frame_rel _ _` mp_tac >>
  simp[vfmSameFrameTheory.same_frame_rel_def] >> strip_tac >>
  `u.contexts <> []` by (Cases_on `u.contexts` >> gvs[]) >>
  `handle_step ex u = handle_exception ex u` by
    (irule asm_call_memory_handle_step >> simp[] >> metis_tac[]) >>
  Cases_on `u.contexts` >> gvs[] >> PairCases_on `h` >> gvs[]
QED

Theorem asm_call_finite_collect:
  !n. (?d. s.msdomain = Collect d) ==>
    ?d. (SND (FUNPOW (step o SND) n (INL (),s))).msdomain = Collect d
Proof
  Induct >- simp[] >> strip_tac >>
  first_x_assum mp_tac >> simp[] >> strip_tac >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  qmatch_goalsub_abbrev_tac `step mid` >>
  `?d. mid.msdomain = Collect d` by simp[Abbr `mid`] >>
  Cases_on `step mid` >> gvs[] >>
  drule_at (Pat `step _ = _`) step_preserves_collect >> simp[]
QED

Theorem asm_call_run_last_source:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = child::saved /\ run_call s = SOME (INL (),t) /\
  LENGTH t.contexts = LENGTH saved ==>
  ?mid c rb. wf_state mid /\ (?d. mid.msdomain = Collect d) /\
    mid.contexts = (c,rb)::saved /\ c.msgParams = (FST child).msgParams /\
    step mid = (INL (),t)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  Cases_on `n` >- gvs[] >>
  qmatch_asmsub_abbrev_tac `FUNPOW (step o SND) (SUC n') start` >>
  qabbrev_tac `mid = SND (FUNPOW (step o SND) n' start)` >>
  `step mid = (INL (),t)` by
    (gvs[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  `!k. k <= n' ==> LENGTH saved <
      LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts` by
    (rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  `wf_state mid /\ ?c rb. mid.contexts = (c,rb)::saved /\
      c.msgParams = (FST child).msgParams` by
    (irule asm_call_trace_before_final_pop >>
     conj_tac
     >- (qexistsl_tac [`n'`,`s`] >> simp[Abbr `mid`, Abbr `start`]) >>
     qexistsl_tac [`INL ()`,`t`] >> simp[]) >>
  `?d. mid.msdomain = Collect d` by
    (simp[Abbr `mid`, Abbr `start`] >> irule asm_call_finite_collect >> simp[]) >>
  qexistsl_tac [`mid`,`c`,`rb`] >> simp[]
QED

Theorem asm_call_run_final_memory_view:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  ?mid ex u c rb. wf_state mid /\ (?d. mid.msdomain = Collect d) /\
    step mid = (INL (),t) /\ step_inner mid = (INR ex,u) /\
    u.contexts = (c,rb)::(parent,prb)::rest /\
    c.msgParams = child.msgParams /\ ~vfm_abort ex /\
    handle_exception ex u = (INL (),t) /\
    EVERY (wf_context o FST) u.contexts /\ stack_room_ok u /\ gas_stack_ok u
Proof
  strip_tac >> drule_at (Pat `run_call _ = _`) asm_call_run_last_source >>
  simp[] >> strip_tac >>
  `c.msgParams.outputTo = Memory mr` by simp[] >>
  `LENGTH t.contexts < LENGTH mid.contexts` by simp[] >>
  drule_at (Pat `step _ = _`) asm_call_final_memory_raw >> simp[] >> strip_tac >>
  qexistsl_tac [`mid`,`ex`,`u`,`c'`,`rb`] >> simp[]
QED

Theorem asm_call_memory_pop_selectors:
  u.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  EVERY (wf_context o FST) u.contexts /\ stack_room_ok u /\ gas_stack_ok u /\
  handle_exception ex u = (INL (),t) ==>
  ?c. t.contexts = (c,prb)::rest /\ c.msgParams = parent.msgParams /\
    c.pc = SUC parent.pc /\ c.stack = b2w (ex = NONE)::parent.stack /\
    c.returnData = (if ex = NONE \/ ex = SOME Reverted then child.returnData else []) /\
    c.memory = buffer_write mr.offset (TAKE mr.size c.returnData) parent.memory
Proof
  strip_tac >> `2 <= LENGTH u.contexts` by simp[] >>
  drule_all asm_call_memory_pop_bounds >> strip_tac >>
  `LENGTH parent.stack < stack_limit /\
   child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed /\
   child.gasUsed <= child.msgParams.gasLimit` by
    (qpat_x_assum `u.contexts = _` (fn th => fs[th])) >>
  Cases_on `ex`
  >- (drule_all asm_handle_exception_memory_success >> strip_tac >> gvs[]) >>
  Cases_on `x = Reverted`
  >- (qpat_x_assum `x = Reverted` SUBST_ALL_TAC >>
      drule_all asm_handle_exception_memory_reverted >> strip_tac >> gvs[]) >>
  drule_all asm_handle_exception_memory_exception >> strip_tac >> gvs[]
QED

Theorem asm_call_run_memory_selectors:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  ?ex u raw rb c.
    u.contexts = (raw,rb)::(parent,prb)::rest /\
    raw.msgParams = child.msgParams /\ ~vfm_abort ex /\
    handle_exception ex u = (INL (),t) /\
    t.contexts = (c,prb)::rest /\ c.msgParams = parent.msgParams /\
    c.pc = SUC parent.pc /\ c.stack = b2w (ex = NONE)::parent.stack /\
    c.returnData = (if ex = NONE \/ ex = SOME Reverted then raw.returnData else []) /\
    c.memory = buffer_write mr.offset (TAKE mr.size c.returnData) parent.memory
Proof
  strip_tac >>
  drule_at (Pat `run_call _ = _`) asm_call_run_final_memory_view >>
  simp[] >> strip_tac >>
  `c.msgParams.outputTo = Memory mr` by simp[] >>
  drule_all asm_call_memory_pop_selectors >> strip_tac >>
  qexistsl_tac [`ex`,`u`,`c`,`rb`,`c'`] >> simp[]
QED

Theorem asm_call_returned_message_adoption:
  (rq.cr_kind = MessageCall \/ rq.cr_kind = DelegateMessageCall) /\
  t.contexts = (c,rb)::rest /\
  out = outcome_of rq.cr_kind t (LENGTH logs) (LENGTH pending) /\
  ((rq.cr_static \/ ~out.co_success) ==>
    t.rollback.accounts = accounts /\ t.rollback.tStorage = ts /\
    c.logs = logs /\ t.rollback.toDelete = pending) /\
  ((~rq.cr_static /\ out.co_success) ==>
    (?added. c.logs = logs ++ added) /\
    (?added. t.rollback.toDelete = added ++ pending)) ==>
  adopt_outcome rq out (accounts,ts,logs) =
    (t.rollback.accounts,t.rollback.tStorage,c.logs) /\
  adopt_outcome_deletions rq out pending = t.rollback.toDelete
Proof
  strip_tac >>
  (Cases_on `rq.cr_static \/ ~out.co_success`
   >- gvs[adopt_outcome_def, adopt_outcome_deletions_def]) >>
  `~rq.cr_static /\ out.co_success` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[adopt_outcome_def, adopt_outcome_deletions_def, outcome_of_def,
      TAKE_LENGTH_APPEND, DROP_APPEND]
QED

Theorem asm_call_returned_outcome_adoption:
  rq.cr_kind = MessageCall /\ t.contexts = (c,rb)::rest /\
  out = outcome_of MessageCall t (LENGTH logs) (LENGTH pending) /\
  ((rq.cr_static \/ ~out.co_success) ==>
    t.rollback.accounts = accounts /\ t.rollback.tStorage = ts /\
    c.logs = logs /\ t.rollback.toDelete = pending) /\
  ((~rq.cr_static /\ out.co_success) ==>
    (?added. c.logs = logs ++ added) /\
    (?added. t.rollback.toDelete = added ++ pending)) ==>
  adopt_outcome rq out (accounts,ts,logs) =
    (t.rollback.accounts,t.rollback.tStorage,c.logs) /\
  adopt_outcome_deletions rq out pending = t.rollback.toDelete
Proof
  strip_tac >> irule asm_call_returned_message_adoption >> simp[] >>
  metis_tac[]
QED

Theorem asm_call_memory_pop_jumpDest:
  u.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  EVERY (wf_context o FST) u.contexts /\ stack_room_ok u /\ gas_stack_ok u /\
  handle_exception ex u = (INL (),t) /\ t.contexts = (c,prb)::rest ==>
  c.jumpDest = parent.jumpDest
Proof
  strip_tac >> `2 <= LENGTH u.contexts` by simp[] >>
  drule_all asm_call_memory_pop_bounds >> strip_tac >>
  `LENGTH parent.stack < stack_limit /\
   child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed /\
   child.gasUsed <= child.msgParams.gasLimit` by
    (qpat_x_assum `u.contexts = _` (fn th => fs[th])) >>
  Cases_on `ex`
  >- (drule_all asm_handle_exception_memory_success >> strip_tac >> gvs[]) >>
  Cases_on `x = Reverted`
  >- (qpat_x_assum `x = Reverted` SUBST_ALL_TAC >>
      drule_all asm_handle_exception_memory_reverted >> strip_tac >> gvs[]) >>
  drule_all asm_handle_exception_memory_exception >> strip_tac >> gvs[]
QED

Theorem asm_call_run_memory_jumpDest:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) /\
  t.contexts = (c,prb)::rest ==> c.jumpDest = parent.jumpDest
Proof
  strip_tac >>
  drule_at (Pat `run_call _ = _`) asm_call_run_final_memory_view >>
  simp[] >> strip_tac >>
  `c'.msgParams.outputTo = Memory mr` by simp[] >>
  drule_all asm_call_memory_pop_jumpDest >> simp[]
QED

Theorem asm_call_bottom_snapshot_step:
  wf_state s /\ saved <> [] /\ active <> [] /\ s.contexts = active ++ saved /\
  step s = (r,t) /\ LENGTH saved < LENGTH t.contexts ==>
  ?active'. active' <> [] /\ t.contexts = active' ++ saved /\
    SND (LAST active') = SND (LAST active)
Proof
  strip_tac >>
  `asm_call_saved_suffix saved s` by
    (simp[asm_call_saved_suffix_def] >> metis_tac[]) >>
  drule_all asm_call_saved_suffix_step >>
  simp[asm_call_saved_suffix_def] >> strip_tac >>
  rename1 `t.contexts = next ++ saved` >>
  qexists_tac `next` >> simp[] >>
  Cases_on `LENGTH s.contexts < LENGTH t.contexts`
  >- (`0 < LENGTH saved` by (Cases_on `saved` >> gvs[]) >>
      drule_all step_push_foreign >> strip_tac >>
      namedCases_on `active` ["", "first others"] >> gvs[] >>
      namedCases_on `next` ["", "new below"] >> gvs[] >>
      namedCases_on `below` ["", "parent above"] >> gvs[FRONT_APPEND] >>
      Cases_on `saved` >> gvs[] >>
      qpat_x_assum `FRONT _ = FRONT _` mp_tac >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, FRONT_APPEND] >>
      simp[] >> strip_tac >> Cases_on `others` >> gvs[]) >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac >>
      Cases_on `active` >> Cases_on `next` >> gvs[] >>
      Cases_on `t'` >> gvs[]) >>
  `LENGTH t.contexts < LENGTH s.contexts` by decide_tac >>
  drule_all step_pop_foreign >> strip_tac >>
  namedCases_on `active` ["", "first others"] >> gvs[] >>
  namedCases_on `others` ["", "second above"] >> gvs[] >>
  Cases_on `above` >> gvs[]
QED

Theorem asm_call_bottom_snapshot_finite:
  !n. wf_state s /\ saved <> [] /\ s.contexts = child::saved /\
    (!k. k <= n ==>
      LENGTH saved < LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts) ==>
    wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
    ?active. active <> [] /\
      (SND (FUNPOW (step o SND) n (INL (),s))).contexts = active ++ saved /\
      SND (LAST active) = SND child
Proof
  Induct
  >- (strip_tac >> simp[] >> qexists_tac `[child]` >> simp[]) >>
  strip_tac >>
  `wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
   ?active. active <> [] /\
     (SND (FUNPOW (step o SND) n (INL (),s))).contexts = active ++ saved /\
     SND (LAST active) = SND child` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  qmatch_goalsub_abbrev_tac `step mid` >>
  `wf_state mid /\ mid.contexts = active ++ saved` by simp[Abbr `mid`] >>
  `LENGTH saved < LENGTH (SND (step mid)).contexts` by
    (first_x_assum (qspec_then `SUC n` mp_tac) >>
     simp[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  Cases_on `step mid` >> gvs[] >> conj_tac
  >- (drule_all step_preserves_wf_state >> simp[]) >>
  drule_all asm_call_bottom_snapshot_step >> strip_tac >>
  qexists_tac `active'` >> simp[]
QED

Theorem asm_call_run_last_snapshot:
  wf_state s /\ (?d. s.msdomain = Collect d) /\ saved <> [] /\
  s.contexts = child::saved /\ run_call s = SOME (INL (),t) /\
  LENGTH t.contexts = LENGTH saved ==>
  ?mid c. wf_state mid /\ (?d. mid.msdomain = Collect d) /\
    mid.contexts = (c,SND child)::saved /\ c.msgParams = (FST child).msgParams /\
    step mid = (INL (),t)
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  Cases_on `n` >- gvs[] >>
  qmatch_asmsub_abbrev_tac `FUNPOW (step o SND) (SUC n') start` >>
  qabbrev_tac `mid = SND (FUNPOW (step o SND) n' start)` >>
  `step mid = (INL (),t)` by
    (gvs[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  `!k. k <= n' ==> LENGTH saved <
      LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts` by
    (rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  `wf_state mid /\ ?active. active <> [] /\ mid.contexts = active ++ saved /\
      SND (LAST active) = SND child` by
    (simp[Abbr `mid`, Abbr `start`] >>
     irule asm_call_bottom_snapshot_finite >> simp[]) >>
  `wf_state mid /\ ?c rb. mid.contexts = (c,rb)::saved /\
      c.msgParams = (FST child).msgParams` by
    (irule asm_call_trace_before_final_pop >>
     conj_tac
     >- (qexistsl_tac [`n'`,`s`] >> simp[Abbr `mid`, Abbr `start`]) >>
     qexistsl_tac [`INL ()`,`t`] >> simp[]) >>
  `active = [(c,rb)]` by
    (qpat_x_assum `mid.contexts = active ++ saved` mp_tac >> simp[]) >>
  `rb = SND child` by gvs[] >>
  `?d. mid.msdomain = Collect d` by
    (simp[Abbr `mid`, Abbr `start`] >> irule asm_call_finite_collect >> simp[]) >>
  qexistsl_tac [`mid`,`c`] >> simp[]
QED

Theorem asm_call_run_final_memory_snapshot:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  ?ex u c. u.contexts = (c,crb)::(parent,prb)::rest /\
    c.msgParams = child.msgParams /\ ~vfm_abort ex /\
    handle_exception ex u = (INL (),t) /\
    EVERY (wf_context o FST) u.contexts /\ stack_room_ok u /\ gas_stack_ok u
Proof
  strip_tac >> drule_at (Pat `run_call _ = _`) asm_call_run_last_snapshot >>
  simp[] >> strip_tac >>
  `c.msgParams.outputTo = Memory mr` by simp[] >>
  `LENGTH t.contexts < LENGTH mid.contexts` by simp[] >>
  drule_at (Pat `step _ = _`) asm_call_final_memory_raw >> simp[] >> strip_tac >>
  qexistsl_tac [`ex`,`u`,`c'`] >> simp[]
QED

Theorem asm_call_memory_pop_failure_effects:
  u.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  EVERY (wf_context o FST) u.contexts /\ stack_room_ok u /\ gas_stack_ok u /\
  handle_exception ex u = (INL (),t) /\ ex <> NONE ==>
  t.rollback.accounts = crb.accounts /\ t.rollback.tStorage = crb.tStorage /\
  t.rollback.toDelete = crb.toDelete /\ (FST (HD t.contexts)).logs = parent.logs
Proof
  strip_tac >> `2 <= LENGTH u.contexts` by simp[] >>
  drule_all asm_call_memory_pop_bounds >> strip_tac >>
  `LENGTH parent.stack < stack_limit /\
   child.msgParams.gasLimit - child.gasUsed <= parent.gasUsed /\
   child.gasUsed <= child.msgParams.gasLimit` by
    (qpat_x_assum `u.contexts = _` (fn th => fs[th])) >>
  Cases_on `ex` >- gvs[] >>
  Cases_on `x = Reverted`
  >- (qpat_x_assum `x = Reverted` SUBST_ALL_TAC >>
      drule_all asm_handle_exception_memory_reverted >> strip_tac >> gvs[]) >>
  drule_all asm_handle_exception_memory_exception >> strip_tac >> gvs[]
QED

Theorem asm_call_run_memory_failure_effects:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) /\
  HD (FST (HD t.contexts)).stack = 0w ==>
  t.rollback.accounts = crb.accounts /\ t.rollback.tStorage = crb.tStorage /\
  t.rollback.toDelete = crb.toDelete /\ (FST (HD t.contexts)).logs = parent.logs
Proof
  strip_tac >>
  drule_at (Pat `run_call _ = _`) asm_call_run_final_memory_snapshot >>
  simp[] >> strip_tac >>
  `c.msgParams.outputTo = Memory mr` by simp[] >>
  drule_all asm_call_memory_pop_selectors >> strip_tac >>
  `ex <> NONE` by (strip_tac >> gvs[]) >>
  drule_all asm_call_memory_pop_failure_effects >> simp[]
QED

(* Exact list suffixes: proof-only interfaces, preserving order and duplicates. *)
val call_pending_suffix = ``\(pending:address list) xs. ?added. xs = added ++ pending``;
val call_pending_inv = ``\pending saved (s:execution_state).
  ?active. active <> [] /\ s.contexts = active ++ saved /\
    ^call_pending_suffix pending s.rollback.toDelete /\
    EVERY (\p. ^call_pending_suffix pending (SND p).toDelete) active``;

Theorem asm_call_pending_initial:
  s.contexts = (child,crb)::saved /\
  s.rollback.toDelete = pending /\ crb.toDelete = pending ==>
  ^call_pending_inv pending saved s
Proof
  BETA_TAC >> strip_tac >> qexists_tac `[(child,crb)]` >> simp[] >>
  qexists_tac `[]` >> simp[]
QED

Theorem asm_call_pending_projection:
  ^call_pending_inv pending saved s /\ asm_call_saved_suffix saved t /\
  t.rollback.toDelete = s.rollback.toDelete /\
  MAP (\p. (SND p).toDelete) t.contexts =
    MAP (\p. (SND p).toDelete) s.contexts ==>
  ^call_pending_inv pending saved t
Proof
  simp[asm_call_saved_suffix_def] >> strip_tac >>
  qexists_tac `active'` >> simp[] >>
  `MAP (\p. (SND p).toDelete) active' =
   MAP (\p. (SND p).toDelete) active` by gvs[] >>
  `EVERY (\xs. ?added. xs = added ++ pending)
     (MAP (\p. (SND p).toDelete) active')` suffices_by simp[EVERY_MAP] >>
  asm_rewrite_tac[] >> simp[EVERY_MAP]
QED

Theorem asm_call_pending_cp:
  cp m /\ ^call_pending_inv pending saved s /\ m s = (r,t) ==>
  ^call_pending_inv pending saved t
Proof
  BETA_TAC >> strip_tac >>
  `s.contexts <> []` by (Cases_on `active` >> gvs[]) >>
  qpat_x_assum `cp m` mp_tac >> simp[cp_def] >>
  disch_then drule_all >> strip_tac >>
  namedCases_on `active` ["", "head tail"] >> gvs[] >>
  qexists_tac `(q',SND head)::tail` >> simp[]
QED

Theorem asm_call_pending_add_to_delete:
  ^call_pending_inv pending saved s /\ add_to_delete address s = (r,t) ==>
  ^call_pending_inv pending saved t
Proof
  simp[add_to_delete_def, return_def] >> strip_tac >> gvs[] >>
  qexists_tac `active` >> simp[] >> qexists_tac `address::added` >> simp[]
QED

Theorem asm_call_pending_push_projection:
  ^call_pending_inv pending saved s /\ asm_call_saved_suffix saved t /\
  t.rollback.toDelete = s.rollback.toDelete /\
  MAP (\p. (SND p).toDelete) t.contexts =
    s.rollback.toDelete :: MAP (\p. (SND p).toDelete) s.contexts ==>
  ^call_pending_inv pending saved t
Proof
  simp[asm_call_saved_suffix_def] >> strip_tac >>
  qexists_tac `active'` >> simp[] >>
  `MAP (\p. (SND p).toDelete) active' =
   s.rollback.toDelete :: MAP (\p. (SND p).toDelete) active` by gvs[] >>
  `EVERY (\xs. ?added. xs = added ++ pending)
     (MAP (\p. (SND p).toDelete) active')` suffices_by simp[EVERY_MAP] >>
  asm_rewrite_tac[] >> simp[EVERY_MAP]
QED

Theorem asm_call_pending_proceed_call:
  ^call_pending_inv pending saved s /\
  proceed_call op sender address value ao az code stipend output s = (r,t) ==>
  ^call_pending_inv pending saved t
Proof
  strip_tac >> `s.contexts <> []` by
    (qpat_x_assum `^call_pending_inv pending saved s` mp_tac >>
     simp[] >> strip_tac >> Cases_on `active` >> gvs[]) >>
  `asm_call_saved_suffix saved t` by
    (drule_all proceed_call_push_structure >> strip_tac >>
     qpat_x_assum `^call_pending_inv pending saved s` mp_tac >>
     simp[asm_call_saved_suffix_def] >> strip_tac >>
     Cases_on `t.contexts` >> gvs[] >>
     qexists_tac `h::active` >> simp[]) >>
  drule_all proceed_call_deletion_projections >> strip_tac >>
  irule asm_call_pending_push_projection >> simp[] >> metis_tac[]
QED

Theorem asm_call_pending_proceed_create:
  ^call_pending_inv pending saved s /\
  proceed_create sender address value code gas s = (r,t) ==>
  ^call_pending_inv pending saved t
Proof
  strip_tac >>
  `s.contexts <> [] /\ asm_call_saved_suffix saved s` by
    (qpat_x_assum `^call_pending_inv pending saved s` mp_tac >>
     simp[asm_call_saved_suffix_def] >> strip_tac >>
     conj_tac >- (Cases_on `active` >> gvs[]) >> metis_tac[]) >>
  `asm_call_saved_suffix saved t` by
    (drule asm_call_saved_suffix_proceed_create >>
     disch_then (qspecl_then [`value`,`sender`,`gas`,`code`,`address`] mp_tac) >>
     simp[]) >>
  drule_all proceed_create_deletion_projections >> strip_tac >>
  irule asm_call_pending_push_projection >> simp[] >> metis_tac[]
QED

Theorem asm_call_pending_pop_result:
  ^call_pending_inv pending saved s /\
  s.contexts = head::tail /\
  (t.rollback.toDelete = s.rollback.toDelete \/
   t.rollback.toDelete = (SND head).toDelete) ==>
  ^call_pending_suffix pending t.rollback.toDelete
Proof
  BETA_TAC >> strip_tac >> namedCases_on `active` ["", "first others"] >>
  gvs[] >> metis_tac[]
QED

Theorem asm_call_pending_pop:
  ^call_pending_inv pending saved s /\ asm_call_saved_suffix saved t /\
  2 <= LENGTH s.contexts /\ pop_and_incorporate_context success s = (r,t) ==>
  ^call_pending_inv pending saved t
Proof
  strip_tac >> drule_all pop_context_deletion_projections >> strip_tac >>
  qpat_x_assum `^call_pending_inv pending saved s` mp_tac >>
  simp[] >> strip_tac >>
  qpat_x_assum `asm_call_saved_suffix saved t` mp_tac >>
  simp[asm_call_saved_suffix_def] >> strip_tac >>
  namedCases_on `active` ["", "first others"] >> gvs[] >>
  `MAP (\p. (SND p).toDelete) active' =
   MAP (\p. (SND p).toDelete) others` by gvs[] >>
  `EVERY (\xs. ?added. xs = added ++ pending)
     (MAP (\p. (SND p).toDelete) active')` suffices_by simp[EVERY_MAP] >>
  asm_rewrite_tac[] >> simp[EVERY_MAP]
QED

Theorem asm_call_pending_final_handler:
  ^call_pending_inv pending saved s /\ handle_exception ex s = (r,t) ==>
  ^call_pending_suffix pending t.rollback.toDelete
Proof
  strip_tac >> `s.contexts <> []` by
    (qpat_x_assum `^call_pending_inv pending saved s` mp_tac >>
     simp[] >> strip_tac >> Cases_on `active` >> gvs[]) >>
  drule_all handle_exception_deletion_projections >> strip_tac >>
  irule asm_call_pending_pop_result >>
  Cases_on `s.contexts` >> gvs[] >> metis_tac[]
QED

val call_pending_post = ``\pending saved (s:execution_state) t.
  ^call_pending_inv pending saved t``;

Theorem asm_call_pending_cp_preserves:
  cp m ==> preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) m
Proof
  rewrite_tac[preserves_when_def] >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule_all (SRULE [] asm_call_pending_cp) >> simp[]
QED

Theorem asm_call_pending_bind:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) g /\
  (!x. preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (f x)) ==>
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (bind g f)
Proof
  strip_tac >> irule preserves_when_bind >> simp[]
QED

Theorem asm_call_pending_ignore_bind:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) g /\
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) f ==>
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (ignore_bind g f)
Proof
  simp[ignore_bind_def] >> strip_tac >> irule (SRULE [] asm_call_pending_bind) >> simp[]
QED

Theorem asm_call_pending_update_accounts:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (update_accounts f)
Proof
  simp[preserves_when_def, update_accounts_def, return_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem asm_call_pending_proceed_call_preserves:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved)
    (proceed_call op sender address value ao az code stipend output)
Proof
  simp[preserves_when_def] >> metis_tac[asm_call_pending_proceed_call]
QED

Theorem asm_call_pending_proceed_create_preserves:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved)
    (proceed_create sender address value code gas)
Proof
  simp[preserves_when_def] >> metis_tac[asm_call_pending_proceed_create]
QED

Theorem asm_call_pending_step_call:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (step_call op)
Proof
  simp[step_call_def] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  pairarg_tac >> simp[] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_bind) >> reverse conj_tac
  >- (irule (SRULE [] asm_call_pending_cp_preserves) >> CASE_TAC >> simp[]) >>
  qx_gen_tac `codecost` >> PairCases_on `codecost` >> simp[] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  pairarg_tac >> simp[] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> conj_tac
  >- (irule (SRULE [] asm_call_pending_cp_preserves) >> IF_CASES_TAC >> simp[]) >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  IF_CASES_TAC >- (irule (SRULE [] asm_call_pending_cp_preserves) >> simp[]) >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  IF_CASES_TAC >- (irule (SRULE [] asm_call_pending_cp_preserves) >> simp[]) >>
  simp[SRULE [] asm_call_pending_proceed_call_preserves]
QED

Theorem asm_call_pending_abort_create:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (abort_create_exists sender)
Proof
  simp[abort_create_exists_def] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_update_accounts] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves]
QED

Theorem asm_call_pending_step_create:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (step_create two)
Proof
  simp[step_create_def] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  IF_CASES_TAC >- (irule (SRULE [] asm_call_pending_cp_preserves) >> simp[]) >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  IF_CASES_TAC >- simp[SRULE [] asm_call_pending_abort_create] >>
  simp[SRULE [] asm_call_pending_proceed_create_preserves]
QED

Theorem asm_call_pending_add_preserves:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (add_to_delete address)
Proof
  simp[preserves_when_def] >> metis_tac[asm_call_pending_add_to_delete]
QED

Theorem asm_call_pending_self_destruct:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) step_self_destruct
Proof
  simp[step_self_destruct_def] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_update_accounts] >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >> gen_tac >>
  irule (SRULE [] asm_call_pending_ignore_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  IF_CASES_TAC >- (irule (SRULE [] asm_call_pending_ignore_bind) >>
    simp[SRULE [] asm_call_pending_update_accounts, SRULE [] asm_call_pending_add_preserves]) >>
  irule (SRULE [] asm_call_pending_cp_preserves) >> simp[]
QED

Theorem asm_call_pending_ordinary_inst:
  op <> SelfDestruct /\ op <> Create /\ op <> Create2 /\
  op <> Call /\ op <> CallCode /\ op <> DelegateCall /\ op <> StaticCall ==>
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (step_inst op)
Proof
  strip_tac >> drule_all step_inst_deletion_exact >>
  rewrite_tac[preserves_when_def] >> BETA_TAC >> disch_tac >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `s.contexts <> [] /\ asm_call_saved_suffix saved s` by
    (qpat_x_assum `?active. _` mp_tac >>
     simp[asm_call_saved_suffix_def] >> strip_tac >>
     conj_tac >- (Cases_on `active` >> gvs[]) >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  `LENGTH s'.contexts = LENGTH s.contexts` by metis_tac[LENGTH_MAP] >>
  `same_frame_rel s s'` by
    (irule (INST_TYPE [alpha |-> ``:unit``] same_frame_or_grow_eq_length) >> simp[] >>
     qexistsl_tac [`step_inst op`,`r`] >> simp[]) >>
  `asm_call_saved_suffix saved s'` by
    (irule asm_call_saved_suffix_same_frame >> metis_tac[]) >>
  drule_all (SRULE [] asm_call_pending_projection) >> simp[]
QED

Theorem asm_call_pending_step_inst:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) (step_inst op)
Proof
  Cases_on `op = SelfDestruct` >- gvs[step_inst_def, SRULE [] asm_call_pending_self_destruct] >>
  Cases_on `op = Create` >- gvs[step_inst_def, SRULE [] asm_call_pending_step_create] >>
  Cases_on `op = Create2` >- gvs[step_inst_def, SRULE [] asm_call_pending_step_create] >>
  Cases_on `op = Call` >- gvs[step_inst_def, SRULE [] asm_call_pending_step_call] >>
  Cases_on `op = CallCode` >- gvs[step_inst_def, SRULE [] asm_call_pending_step_call] >>
  Cases_on `op = DelegateCall` >- gvs[step_inst_def, SRULE [] asm_call_pending_step_call] >>
  Cases_on `op = StaticCall` >- gvs[step_inst_def, SRULE [] asm_call_pending_step_call] >>
  irule asm_call_pending_ordinary_inst >> simp[]
QED

Theorem asm_call_pending_step_inner:
  preserves_when (^call_pending_inv pending saved)
    (^call_pending_post pending saved) step_inner
Proof
  rewrite_tac[step_inner_def, LET_THM] >> BETA_TAC >>
  irule (SRULE [] asm_call_pending_bind) >> simp[SRULE [] asm_call_pending_cp_preserves] >>
  qx_gen_tac `ctx` >> Cases_on `FLOOKUP ctx.msgParams.parsed ctx.pc` >> simp[]
  >- (IF_CASES_TAC >> irule (SRULE [] asm_call_pending_cp_preserves) >> simp[]) >>
  irule (SRULE [] asm_call_pending_ignore_bind) >>
  simp[SRULE [] asm_call_pending_step_inst, SRULE [] asm_call_pending_cp_preserves]
QED

Theorem asm_call_pending_handler_projection:
  ^call_pending_inv pending saved s /\ asm_call_saved_suffix saved t /\
  (t.rollback.toDelete = s.rollback.toDelete \/
   t.rollback.toDelete = (SND (HD s.contexts)).toDelete) /\
  (MAP (\p. (SND p).toDelete) t.contexts =
     MAP (\p. (SND p).toDelete) s.contexts \/
   MAP (\p. (SND p).toDelete) t.contexts =
     TL (MAP (\p. (SND p).toDelete) s.contexts)) ==>
  ^call_pending_inv pending saved t
Proof
  simp[asm_call_saved_suffix_def] >> strip_tac >>
  namedCases_on `active` ["", "first others"] >> gvs[] >>
  `EVERY (\xs. ?added. xs = added ++ pending)
     (MAP (\p. (SND p).toDelete) active')` suffices_by simp[EVERY_MAP] >>
  asm_rewrite_tac[] >> simp[EVERY_MAP]
QED

Theorem asm_call_pending_handle_step:
  ^call_pending_inv pending saved s /\ handle_step e s = (r,t) ==>
  ^call_pending_suffix pending t.rollback.toDelete /\
  (asm_call_saved_suffix saved t ==> ^call_pending_inv pending saved t)
Proof
  strip_tac >> `s.contexts <> []` by
    (qpat_x_assum `^call_pending_inv pending saved s` mp_tac >>
     simp[] >> strip_tac >> Cases_on `active` >> gvs[]) >>
  drule_all handle_step_deletion_projections >> strip_tac >>
  (conj_tac
   >- (BETA_TAC >> irule (SRULE [] asm_call_pending_pop_result) >>
       Cases_on `s.contexts` >> gvs[] >> metis_tac[])) >>
  strip_tac >> BETA_TAC >> irule (SRULE [] asm_call_pending_handler_projection) >>
  simp[] >> qexists_tac `s` >> simp[] >> metis_tac[]
QED

Theorem asm_call_pending_inner_result:
  ^call_pending_inv pending saved s /\ step_inner s = (r,t) ==>
  ^call_pending_inv pending saved t
Proof
  BETA_TAC >> strip_tac >>
  irule (SRULE [preserves_when_def] asm_call_pending_step_inner) >>
  qexistsl_tac [`r`,`s`] >> simp[] >> metis_tac[]
QED

Theorem asm_call_pending_step_result:
  ^call_pending_inv pending saved s /\ step s = (r,t) ==>
  ^call_pending_suffix pending t.rollback.toDelete /\
  (asm_call_saved_suffix saved t ==> ^call_pending_inv pending saved t)
Proof
  strip_tac >> qpat_x_assum `step _ = _` mp_tac >>
  rewrite_tac[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> rename1 `step_inner s = (res,mid)` >>
  `^call_pending_inv pending saved mid` by
    (irule asm_call_pending_inner_result >> metis_tac[]) >>
  Cases_on `res` >> simp[] >> disch_tac
  >- (gvs[] >> simp[] >> metis_tac[]) >>
  drule_all asm_call_pending_handle_step >> simp[]
QED

Theorem asm_call_pending_step:
  wf_state s /\ ^call_pending_inv pending saved s /\ step s = (r,t) /\
  LENGTH saved < LENGTH t.contexts ==>
  ^call_pending_inv pending saved t
Proof
  strip_tac >>
  `asm_call_saved_suffix saved s` by
    (qpat_x_assum `^call_pending_inv pending saved s` mp_tac >>
     simp[asm_call_saved_suffix_def] >> metis_tac[]) >>
  `asm_call_saved_suffix saved t` by
    (drule_all asm_call_saved_suffix_step >> simp[]) >>
  drule_all asm_call_pending_step_result >> simp[]
QED

Theorem asm_call_pending_finite:
  !n. wf_state s /\ ^call_pending_inv pending saved s /\
    (!k. k <= n ==>
      LENGTH saved < LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts) ==>
    wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
    ^call_pending_inv pending saved (SND (FUNPOW (step o SND) n (INL (),s)))
Proof
  Induct >- simp[] >> strip_tac >>
  `wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
   ^call_pending_inv pending saved (SND (FUNPOW (step o SND) n (INL (),s)))` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  qmatch_goalsub_abbrev_tac `step mid` >>
  `wf_state mid /\ ^call_pending_inv pending saved mid` by simp[Abbr `mid`] >>
  `LENGTH saved < LENGTH (SND (step mid)).contexts` by
    (first_x_assum (qspec_then `SUC n` mp_tac) >>
     simp[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  Cases_on `step mid` >> gvs[] >> conj_tac
  >- (drule_all step_preserves_wf_state >> simp[]) >>
  irule (SRULE [] asm_call_pending_step) >>
  simp[] >> qexistsl_tac [`q`,`mid`] >> simp[] >> metis_tac[]
QED

Theorem asm_call_run_pending_suffix:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  s.rollback.toDelete = pending /\ crb.toDelete = pending /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  ?added. t.rollback.toDelete = added ++ pending
Proof
  strip_tac >>
  `^call_pending_inv pending ((parent,prb)::rest) s` by
    (irule asm_call_pending_initial >> simp[]) >>
  drule run_call_finite_trace >> strip_tac >>
  Cases_on `n` >- gvs[] >>
  qmatch_asmsub_abbrev_tac `FUNPOW (step o SND) (SUC n') start` >>
  qabbrev_tac `mid = SND (FUNPOW (step o SND) n' start)` >>
  `step mid = (INL (),t)` by
    (gvs[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  `!k. k <= n' ==> LENGTH ((parent,prb)::rest) <
      LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts` by
    (rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  `wf_state mid /\ ^call_pending_inv pending ((parent,prb)::rest) mid` by
    (qspec_then `n'` mp_tac
       (Q.INST [`saved` |-> `(parent,prb)::rest`] asm_call_pending_finite) >>
     simp[Abbr `mid`, Abbr `start`] >> metis_tac[]) >>
  drule_all asm_call_pending_step_result >> simp[]
QED

Theorem asm_frame_call_enter_transport:
  asm_frame_rel prog data es0 a s /\ s.contexts = (c,rb)::rest /\
  step s = (INL (),u) /\ LENGTH u.contexts = SUC (LENGTH s.contexts) /\
  observable_call c /\ run_call u = SOME (INL (),t) /\
  LENGTH t.contexts = LENGTH s.contexts ==>
  let observed = outcome_of (request_of s).cr_kind t
        (LENGTH c.logs) (LENGTH s.rollback.toDelete) in
  run_call t = run_call s /\
  a.as_outcomes = observed::MAP SND (call_trace t) /\
  gas_readings t = gas_readings s /\
  record_request (request_of s) a.as_requests ++ call_requests t = call_requests es0 /\
  take_outcome (request_of s) a.as_outcomes =
    (FST (take_outcome (request_of s) (observed::MAP SND (call_trace t))),
     MAP SND (call_trace t))
Proof
  strip_tac >>
  `run_call t = run_call s` by (drule_all run_call_enter_return >> simp[]) >>
  drule frame_obs_call_enter >> disch_then (qspec_then `t` mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  `a.as_outcomes = outcome_of (request_of s).cr_kind t
      (LENGTH c.logs) (LENGTH s.rollback.toDelete)::MAP SND (call_trace t)` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  `record_request (request_of s) a.as_requests ++ call_requests t =
     call_requests es0` by
    (fs[asm_frame_rel_def, call_requests_def, record_request_def] >>
     gvs[] >> IF_CASES_TAC >> gvs[]) >>
  simp[] >>
  qspecl_then [`request_of s`,`a.as_outcomes`] mp_tac (GEN_ALL take_outcome_rest) >>
  simp[] >> strip_tac >> metis_tac[pairTheory.PAIR]
QED

Theorem asm_call_noncode_handle_step:
  s.contexts <> [] /\
  (!x. (FST (HD s.contexts)).msgParams.outputTo <> Code x) ==>
  handle_step ex s =
    (if vfm_abort ex then reraise ex s else handle_exception ex s)
Proof
  strip_tac >>
  drule_all (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises) >>
  disch_then (qspec_then `ex` assume_tac) >>
  Cases_on `vfm_abort ex` >> simp[handle_step_def, handle_def, reraise_def]
QED

Theorem asm_call_static_prefix_singleton_exception:
  asm_call_static_prefix saved a ts ds s /\ LENGTH s.contexts = 1 /\
  handle_exception ex s = (r,t) ==>
  asm_call_static_prefix saved a ts ds t
Proof
  Cases_on `s.contexts` >> simp[] >> Cases_on `t'` >> simp[] >>
  PairCases_on `h` >>
  Cases_on `ex = NONE` >> Cases_on `ex = SOME Reverted` >>
  simp[handle_exception_def, bind_def, ignore_bind_def,
       get_gas_left_def, get_current_context_def, return_def,
       consume_gas_def, set_return_data_def, set_current_context_def,
       get_num_contexts_def, reraise_def, assert_def, fail_def,
       AllCaseEqs(), asm_call_static_prefix_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `active` >> gvs[] >> Cases_on `t'` >> gvs[]
QED

Theorem asm_call_static_prefix_handle_exception:
  asm_call_static_prefix saved a ts ds s /\
  EVERY (wf_context o FST) s.contexts /\ stack_room_ok s /\ gas_stack_ok s /\
  handle_exception ex s = (r,t) /\ LENGTH saved < LENGTH t.contexts ==>
  asm_call_static_prefix saved a ts ds t
Proof
  strip_tac >>
  `s.contexts <> []` by (drule asm_call_static_prefix_head >> simp[]) >>
  Cases_on `LENGTH s.contexts = 1`
  >- (drule_all asm_call_static_prefix_singleton_exception >> simp[]) >>
  `2 <= LENGTH s.contexts` by (Cases_on `s.contexts` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  `LENGTH t.contexts + 1 = LENGTH s.contexts` by
    (irule vfmHandleStepTheory.handle_exception_ge_2_pops >>
     simp[arithmeticTheory.GREATER_EQ] >> metis_tac[]) >>
  irule asm_call_static_prefix_internal_pop_safe >>
  qexistsl_tac [`ex`,`r`,`s`] >> simp[] >> decide_tac
QED

Theorem asm_call_static_prefix_handle_step:
  asm_call_static_prefix saved a ts ds s /\
  EVERY (wf_context o FST) s.contexts /\ stack_room_ok s /\ gas_stack_ok s /\
  handle_step ex s = (r,t) /\ LENGTH saved < LENGTH t.contexts ==>
  asm_call_static_prefix saved a ts ds t
Proof
  strip_tac >> drule asm_call_static_prefix_head >> strip_tac >>
  drule_all asm_call_noncode_handle_step >>
  disch_then (qspec_then `ex` assume_tac) >>
  Cases_on `vfm_abort ex` >- gvs[reraise_def] >>
  `handle_exception ex s = (r,t)` by gvs[] >>
  drule_all asm_call_static_prefix_handle_exception >> simp[]
QED

Theorem asm_call_static_prefix_step:
  wf_state s /\ asm_call_static_prefix saved a ts ds s /\
  step s = (r,t) /\ LENGTH saved < LENGTH t.contexts ==>
  asm_call_static_prefix saved a ts ds t
Proof
  strip_tac >> qpat_x_assum `step s = _` mp_tac >>
  rewrite_tac[step_eq_handle_step_inner, handle_def] >>
  Cases_on `step_inner s` >> rename1 `step_inner s = (res,mid)` >>
  `asm_call_static_prefix saved a ts ds mid` by
    (drule_all asm_call_static_prefix_step_inner >> simp[]) >>
  `EVERY (wf_context o FST) mid.contexts /\ stack_room_ok mid /\ gas_stack_ok mid` by
    (drule_all asm_call_step_inner_pop_invariants >> simp[]) >>
  Cases_on `res` >> simp[] >> disch_tac >- gvs[] >>
  drule_all asm_call_static_prefix_handle_step >> simp[]
QED

Theorem asm_call_static_prefix_final_exception:
  asm_call_static_prefix ((parent,prb)::rest) a ts ds s /\
  EVERY (wf_context o FST) s.contexts /\ stack_room_ok s /\ gas_stack_ok s /\
  handle_exception ex s = (r,t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  t.rollback.accounts = a /\ t.rollback.tStorage = ts /\ t.rollback.toDelete = ds /\
  (FST (HD t.contexts)).logs = parent.logs /\ TL t.contexts = rest
Proof
  strip_tac >>
  `s.contexts <> []` by (drule asm_call_static_prefix_head >> simp[]) >>
  `LENGTH s.contexts <= LENGTH t.contexts + 1` by
    (drule_all vfmHandleStepTheory.handle_exception_shrinks_by_one >>
     simp[arithmeticTheory.GREATER_EQ]) >>
  fs[asm_call_static_prefix_def] >>
  `LENGTH active = 1` by
    (gvs[LENGTH_APPEND] >> Cases_on `active` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  Cases_on `active` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  Cases_on `h0.msgParams.outputTo` >> gvs[] >>
  `2 <= LENGTH s.contexts /\ EVERY (wf_context o FST) s.contexts` by simp[] >>
  drule_all asm_call_memory_pop_bounds >> strip_tac >> gvs[] >>
  drule_at (Pat `handle_exception _ _ = _`) asm_call_static_memory_pop_effects >>
  simp[]
QED

Theorem asm_call_static_prefix_final_step:
  wf_state s /\ asm_call_static_prefix ((parent,prb)::rest) a ts ds s /\
  step s = (r,t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  t.rollback.accounts = a /\ t.rollback.tStorage = ts /\ t.rollback.toDelete = ds /\
  (FST (HD t.contexts)).logs = parent.logs /\ TL t.contexts = rest
Proof
  strip_tac >>
  `s.contexts <> [] /\ LENGTH t.contexts < LENGTH s.contexts` by
    (fs[asm_call_static_prefix_def] >> Cases_on `active` >> gvs[]) >>
  drule_all asm_call_step_drop_raw_view >> strip_tac >>
  `asm_call_static_prefix ((parent,prb)::rest) a ts ds u` by
    (drule_all asm_call_static_prefix_step_inner >> simp[]) >>
  drule_at (Pat `asm_call_static_prefix _ _ _ _ u`) asm_call_static_prefix_head >>
  strip_tac >>
  drule_all asm_call_noncode_handle_step >>
  disch_then (qspec_then `ex` assume_tac) >>
  Cases_on `vfm_abort ex`
  >- (gvs[reraise_def, asm_call_static_prefix_def] >>
      Cases_on `active'` >> gvs[]) >>
  `handle_exception ex u = (r,t)` by gvs[] >>
  drule_all asm_call_static_prefix_final_exception >> simp[]
QED

Theorem asm_call_static_prefix_finite:
  !n. wf_state s /\ asm_call_static_prefix saved a ts ds s /\
    (!k. k <= n ==>
      LENGTH saved < LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts) ==>
    wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
    asm_call_static_prefix saved a ts ds (SND (FUNPOW (step o SND) n (INL (),s)))
Proof
  Induct >- simp[] >> strip_tac >>
  `wf_state (SND (FUNPOW (step o SND) n (INL (),s))) /\
   asm_call_static_prefix saved a ts ds (SND (FUNPOW (step o SND) n (INL (),s)))` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  qmatch_goalsub_abbrev_tac `step mid` >>
  `wf_state mid /\ asm_call_static_prefix saved a ts ds mid` by simp[Abbr `mid`] >>
  `LENGTH saved < LENGTH (SND (step mid)).contexts` by
    (first_x_assum (qspec_then `SUC n` mp_tac) >>
     simp[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  Cases_on `step mid` >> gvs[] >> conj_tac
  >- (drule_all step_preserves_wf_state >> simp[]) >>
  drule_all asm_call_static_prefix_step >> simp[]
QED

Theorem asm_call_run_static_effects:
  wf_state s /\ asm_call_static_prefix ((parent,prb)::rest) a ts ds s /\
  LENGTH s.contexts = LENGTH ((parent,prb)::rest) + 1 /\
  run_call s = SOME (r,t) /\ LENGTH t.contexts = LENGTH ((parent,prb)::rest) ==>
  t.rollback.accounts = a /\ t.rollback.tStorage = ts /\ t.rollback.toDelete = ds /\
  (FST (HD t.contexts)).logs = parent.logs /\ TL t.contexts = rest
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  Cases_on `n` >- gvs[] >>
  qmatch_asmsub_abbrev_tac `FUNPOW (step o SND) (SUC n') start` >>
  qabbrev_tac `mid = SND (FUNPOW (step o SND) n' start)` >>
  `step mid = (r,t)` by (gvs[arithmeticTheory.FUNPOW_SUC, Abbr `mid`]) >>
  `!k. k <= n' ==> LENGTH ((parent,prb)::rest) <
      LENGTH (SND (FUNPOW (step o SND) k (INL (),s))).contexts` by
    (rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  `wf_state mid /\ asm_call_static_prefix ((parent,prb)::rest) a ts ds mid` by
    (simp[Abbr `mid`, Abbr `start`] >>
     irule asm_call_static_prefix_finite >> simp[]) >>
  `LENGTH t.contexts = SUC (LENGTH rest)` by simp[] >>
  drule_all asm_call_static_prefix_final_step >> simp[]
QED

Theorem asm_call_run_static_child_effects:
  wf_state s /\ s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.static /\ child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
  crb.accounts = s.rollback.accounts /\ crb.tStorage = s.rollback.tStorage /\
  crb.toDelete = s.rollback.toDelete /\ run_call s = SOME (r,t) /\
  LENGTH t.contexts = SUC (LENGTH rest) ==>
  t.rollback.accounts = s.rollback.accounts /\
  t.rollback.tStorage = s.rollback.tStorage /\
  t.rollback.toDelete = s.rollback.toDelete /\
  (FST (HD t.contexts)).logs = parent.logs /\ TL t.contexts = rest
Proof
  strip_tac >>
  `asm_call_static_prefix ((parent,prb)::rest)
     s.rollback.accounts s.rollback.tStorage s.rollback.toDelete s` by
    (irule asm_call_static_prefix_intro >> simp[] >>
     qexists_tac `[(child,crb)]` >> simp[]) >>
  drule_at (Pat `asm_call_static_prefix _ _ _ _ _`) asm_call_run_static_effects >>
  simp[] >> metis_tac[]
QED

Theorem asm_call_run_memory_success_logs:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) /\
  HD (FST (HD t.contexts)).stack = 1w ==>
  ?added. (FST (HD t.contexts)).logs = parent.logs ++ added
Proof
  strip_tac >>
  drule_at (Pat `run_call _ = _`) asm_call_run_final_memory_snapshot >>
  simp[] >> strip_tac >>
  `c.msgParams.outputTo = Memory mr` by simp[] >>
  drule_all asm_call_memory_pop_selectors >> strip_tac >>
  `ex = NONE` by (Cases_on `ex` >> gvs[]) >>
  qpat_x_assum `ex = NONE` SUBST_ALL_TAC >>
  `2 <= LENGTH u.contexts` by simp[] >>
  drule_all asm_call_memory_pop_bounds >> strip_tac >>
  `LENGTH parent.stack < stack_limit /\
   c.msgParams.gasLimit - c.gasUsed <= parent.gasUsed` by
    (qpat_x_assum `u.contexts = _` (fn th => fs[th])) >>
  drule_all asm_handle_exception_memory_success >> strip_tac >>
  gvs[]
QED

Theorem asm_call_run_message_adoption:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
  (rq.cr_kind = MessageCall \/ rq.cr_kind = DelegateMessageCall) /\
  (rq.cr_static ==> child.msgParams.static) /\
  crb.accounts = accounts /\ crb.tStorage = ts /\ crb.toDelete = pending /\
  s.rollback.toDelete = pending /\
  (rq.cr_static ==> s.rollback.accounts = accounts /\ s.rollback.tStorage = ts) /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) /\
  t.contexts = (c,prb)::rest /\
  out = outcome_of rq.cr_kind t (LENGTH parent.logs) (LENGTH pending) ==>
  adopt_outcome rq out (accounts,ts,parent.logs) =
    (t.rollback.accounts,t.rollback.tStorage,c.logs) /\
  adopt_outcome_deletions rq out pending = t.rollback.toDelete
Proof
  strip_tac >> (
  drule_at (Pat `run_call _ = _`) asm_call_run_memory_selectors >>
  simp[] >> strip_tac >>
  irule asm_call_returned_message_adoption >>
  simp[] >> reverse conj_tac
  >- (disch_tac >> Cases_on `rq.cr_static`
      >- (`child.msgParams.static /\ crb.accounts = s.rollback.accounts /\
           crb.tStorage = s.rollback.tStorage /\ crb.toDelete = s.rollback.toDelete` by
            metis_tac[] >>
          drule_all asm_call_run_static_child_effects >> gvs[]) >>
      `HD (FST (HD t.contexts)).stack = 0w` by gvs[outcome_of_def] >>
      drule_at (Pat `run_call _ = _`) asm_call_run_memory_failure_effects >>
      simp[] >> metis_tac[]) >>
  strip_tac >>
  `HD (FST (HD t.contexts)).stack = 1w` by
    (Cases_on `ex` >> gvs[outcome_of_def]) >>
  conj_tac
  >- (drule_at (Pat `run_call _ = _`) asm_call_run_memory_success_logs >>
      simp[]) >>
  drule_at (Pat `run_call _ = _`) asm_call_run_pending_suffix >> simp[])
QED

Theorem asm_call_run_memory_adoption:
  wf_state s /\ (?d. s.msdomain = Collect d) /\
  s.contexts = (child,crb)::(parent,prb)::rest /\
  child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
  rq.cr_kind = MessageCall /\ (rq.cr_static ==> child.msgParams.static) /\
  crb.accounts = accounts /\ crb.tStorage = ts /\ crb.toDelete = pending /\
  s.rollback.toDelete = pending /\
  (rq.cr_static ==> s.rollback.accounts = accounts /\ s.rollback.tStorage = ts) /\
  run_call s = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) /\
  t.contexts = (c,prb)::rest /\
  out = outcome_of MessageCall t (LENGTH parent.logs) (LENGTH pending) ==>
  adopt_outcome rq out (accounts,ts,parent.logs) =
    (t.rollback.accounts,t.rollback.tStorage,c.logs) /\
  adopt_outcome_deletions rq out pending = t.rollback.toDelete
Proof
  strip_tac >> irule asm_call_run_message_adoption >> simp[] >>
  metis_tac[]
QED

Theorem asm_proceed_message_enter_effects:
  s.contexts = (parent,prb)::rest /\
  (op = Call \/ op = StaticCall \/ op = DelegateCall) /\
  ~parent.msgParams.static /\
  proceed_call op sender address value ao az code stipend (Memory mr) s = (INL (),t) ==>
  ?child crb. t.contexts = (child,crb)::(parent,prb)::rest /\
    child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
    child.msgParams.static = (op = StaticCall) /\ crb = s.rollback /\
    t.rollback.toDelete = s.rollback.toDelete /\
    (op = StaticCall /\ value = 0 ==>
      t.rollback.accounts = s.rollback.accounts /\
      t.rollback.tStorage = s.rollback.tStorage)
Proof
  strip_tac >>
  `s.contexts <> []` by simp[] >>
  `~fIN address precompile_addresses` by
    (drule_all vfmRunCallTheory.proceed_call_inl_nonprecompile >> simp[]) >>
  qhdtm_x_assum `proceed_call` mp_tac >>
  simp[proceed_call_def, bind_def, ignore_bind_def,
       get_rollback_def, read_memory_def, get_caller_def,
       get_value_def, get_static_def, update_accounts_def, push_context_def,
       get_current_context_def, return_def] >>
  Cases_on `op <> CallCode /\ 0 < value` >>
  gvs[update_accounts_def, get_current_context_def, return_def] >>
  strip_tac >>
  gvs[vfmContextTheory.initial_context_def, vfmContextTheory.initial_msg_params_def]
QED

Theorem asm_proceed_call_enter_effects:
  s.contexts = (parent,prb)::rest /\ (op = Call \/ op = StaticCall) /\
  ~parent.msgParams.static /\
  proceed_call op sender address value ao az code stipend (Memory mr) s = (INL (),t) ==>
  ?child crb. t.contexts = (child,crb)::(parent,prb)::rest /\
    child.msgParams.outputTo = Memory mr /\ child.logs = [] /\
    child.msgParams.static = (op = StaticCall) /\ crb = s.rollback /\
    t.rollback.toDelete = s.rollback.toDelete /\
    (op = StaticCall /\ value = 0 ==>
      t.rollback.accounts = s.rollback.accounts /\
      t.rollback.tStorage = s.rollback.tStorage)
Proof
  strip_tac >> irule asm_proceed_message_enter_effects >> simp[] >> metis_tac[]
QED

Theorem asm_message_prepared_enter_view:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall \/ op = DelegateCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (),v) ==>
  ?parent child crb. v.contexts = (child,crb)::(parent,rb)::rest /\
    parent.msgParams = c.msgParams /\ parent.jumpDest = c.jumpDest /\ parent.pc = c.pc /\
    parent.stack = DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
    parent.logs = c.logs /\
    parent.memory = buffer_extend
      (MAX (buffer_length c.memory)
        (let range = max_expansion_range (ao,az) (ro,rs) in
         if 0 < SND range then word_size (FST range + SND range) * 32 else 0)
       - buffer_length c.memory) c.memory /\
    buffer_to_list parent.memory = asm_call_memory ao az ro rs (buffer_to_list c.memory) /\
    child.msgParams.outputTo = Memory <|offset := ro; size := rs|> /\
    child.msgParams.static = (op = StaticCall) /\ child.logs = [] /\
    crb.accounts = s.rollback.accounts /\ crb.tStorage = s.rollback.tStorage /\
    crb.toDelete = s.rollback.toDelete /\ v.rollback.toDelete = s.rollback.toDelete /\
    (op = StaticCall ==> v.rollback.accounts = s.rollback.accounts /\
                         v.rollback.tStorage = s.rollback.tStorage)
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_message_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `u = s with <| contexts := (parent,rb)::rest;
    rollback := _; msdomain := _ |>` >>
  `u.contexts = (parent,rb)::rest` by simp[] >>
  `LENGTH u.contexts <= 1024` by
    (qpat_x_assum `LENGTH s.contexts <= 1024` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  drule_all asm_call_finish_proceed >>
  disch_then (fn th => qpat_assum `asm_call_finish _ _ _ = _` mp_tac >>
    rewrite_tac[th]) >>
  qmatch_goalsub_abbrev_tac `proceed_call _ _ _ _ _ _ _ _ _ p` >> disch_tac >>
  `p.contexts = (parent with returnData := [],rb)::rest /\
   ~(parent with returnData := []).msgParams.static` by simp[Abbr `p`, Abbr `parent`] >>
  drule_all asm_proceed_message_enter_effects >> strip_tac >>
  `op = StaticCall ==> value = 0` by
    (strip_tac >> gvs[call_has_value_def]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`sender = _`, `accounts = _`, `address = _`, `value = _`,
     `ao = _`, `az = _`, `ro = _`, `rs = _`] >>
  qexistsl_tac [`parent with returnData := []`,`child`,`crb`] >>
  simp[Abbr `p`, Abbr `parent`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `max_expansion_range (ao,az) (ro,rs)` >>
  simp_tac (srw_ss()) [] >>
  irule asm_call_memory_buffer_extend >>
  goal_assum (drule_at Any) >> simp_tac std_ss [arithmeticTheory.MULT_COMM]
QED

Theorem asm_call_prepared_enter_view:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (),v) ==>
  ?parent child crb. v.contexts = (child,crb)::(parent,rb)::rest /\
    parent.msgParams = c.msgParams /\ parent.jumpDest = c.jumpDest /\ parent.pc = c.pc /\
    parent.stack = DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
    parent.logs = c.logs /\
    parent.memory = buffer_extend
      (MAX (buffer_length c.memory)
        (let range = max_expansion_range (ao,az) (ro,rs) in
         if 0 < SND range then word_size (FST range + SND range) * 32 else 0)
       - buffer_length c.memory) c.memory /\
    buffer_to_list parent.memory = asm_call_memory ao az ro rs (buffer_to_list c.memory) /\
    child.msgParams.outputTo = Memory <|offset := ro; size := rs|> /\
    child.msgParams.static = (op = StaticCall) /\ child.logs = [] /\
    crb.accounts = s.rollback.accounts /\ crb.tStorage = s.rollback.tStorage /\
    crb.toDelete = s.rollback.toDelete /\ v.rollback.toDelete = s.rollback.toDelete /\
    (op = StaticCall ==> v.rollback.accounts = s.rollback.accounts /\
                         v.rollback.tStorage = s.rollback.tStorage)
Proof
  strip_tac >> irule asm_message_prepared_enter_view >> simp[] >> metis_tac[]
QED

Theorem asm_call_prepared_run_adoption:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\ next_opcode c = SOME op /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (),v) /\
  wf_state v /\ (?dv. v.msdomain = Collect dv) /\
  run_call v = SOME (INL (),t) /\ t.contexts = (ct,rb)::rest ==>
  let out = outcome_of MessageCall t (LENGTH c.logs) (LENGTH s.rollback.toDelete) in
  adopt_outcome (request_of s) out (s.rollback.accounts,s.rollback.tStorage,c.logs) =
    (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
  adopt_outcome_deletions (request_of s) out s.rollback.toDelete = t.rollback.toDelete
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  simp_tac (srw_ss()) [LET_THM] >>
  drule_all asm_call_prepared_request >> strip_tac >>
  drule_all asm_call_prepared_enter_view >> strip_tac >>
  `LENGTH t.contexts = SUC (LENGTH rest)` by simp[] >>
  drule_at (Pat `run_call _ = _`) asm_call_run_memory_adoption >>
  simp[]
QED

Theorem asm_call_prepared_run_selectors:
  s.contexts = (c,rb)::rest /\ s.msdomain = Collect d /\
  ~c.msgParams.static /\ (op = Call \/ op = StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (),v) /\ wf_state v /\ (?dv. v.msdomain = Collect dv) /\
  run_call v = SOME (INL (),t) /\ LENGTH t.contexts = SUC (LENGTH rest) ==>
  ?ct. t.contexts = (ct,rb)::rest /\ ct.msgParams = c.msgParams /\
    ct.jumpDest = c.jumpDest /\ ct.pc = SUC c.pc /\
    ct.stack = (if (outcome_of MessageCall t n m).co_success then 1w else 0w)::
      DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
    ct.returnData = (outcome_of MessageCall t n m).co_returnData /\
    buffer_to_list ct.memory =
      TAKE ro (asm_call_memory ao az ro rs (buffer_to_list c.memory)) ++
      TAKE rs ct.returnData ++ DROP (ro + LENGTH (TAKE rs ct.returnData))
        (asm_call_memory ao az ro rs (buffer_to_list c.memory))
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepared_enter_view >> strip_tac >>
  drule_at (Pat `run_call _ = _`) asm_call_run_memory_selectors >>
  simp[] >> strip_tac >>
  rename1 `t.contexts = (ct,rb)::rest` >>
  `ct.jumpDest = parent.jumpDest` by
    (drule_at (Pat `run_call _ = _`) asm_call_run_memory_jumpDest >> simp[]) >>
  qexists_tac `ct` >> simp[outcome_of_def] >> conj_tac
  >- (Cases_on `ex` >> simp[]) >>
  qpat_x_assum `ct.memory = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `parent.memory = _` (fn th => rewrite_tac[th]) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `max_expansion_range (ao,az) (ro,rs)` >>
  simp_tac (srw_ss()) [] >>
  irule asm_call_memory_buffer_write >>
  goal_assum (drule_at Any) >> simp_tac std_ss [arithmeticTheory.MULT_COMM]
QED

Theorem asm_call_finite_txParams:
  !n. (SND (FUNPOW (step o SND) n (r,s))).txParams = s.txParams
Proof
  Induct >> simp[arithmeticTheory.FUNPOW_SUC,
    vfmTxParamsTheory.step_preserves_txParams]
QED

Theorem asm_call_run_txParams:
  run_call s = SOME (r,t) ==> t.txParams = s.txParams
Proof
  strip_tac >> drule run_call_finite_trace >> strip_tac >>
  qspec_then `n` mp_tac (Q.INST [`r` |-> `INL ()`] asm_call_finite_txParams) >> simp[]
QED

Theorem asm_frame_call_enter_step_ok:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a s /\
  a.as_pc < LENGTH prog /\
  (EL a.as_pc prog = AsmOp "CALL" \/ EL a.as_pc prog = AsmOp "STATICCALL") /\
  s.contexts = (c,rb)::rest /\
  op = (if EL a.as_pc prog = AsmOp "CALL" then Call else StaticCall) /\
  asm_call_prepare op s =
    (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u) /\
  value <= (lookup_account sender accounts).balance /\ LENGTH s.contexts <= 1024 /\
  asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u =
    (INL (),v) /\ step s = (INL (),v) /\ observable_call c /\
  run_call v = SOME (INL (),t) /\ LENGTH t.contexts = LENGTH s.contexts ==>
  asm_frame_step_ok prog data es0 a s
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `wf_state s /\ (?d. s.msdomain = Collect d) /\ ~c.msgParams.static /\
   asm_evm_rel (prog ++ [AsmDataItem data]) a s` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  SUBGOAL_THEN ``op = Call \/ op = StaticCall`` assume_tac
  >- (Cases_on `EL a.as_pc prog = AsmOp "CALL"` >> fs[]) >>
  `next_opcode c = SOME op` by (drule_all asm_frame_call_decode >> simp[] >> metis_tac[]) >>
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
  SUBGOAL_THEN ``?dv. v.msdomain = Collect dv`` assume_tac >- simp[] >>
  `LENGTH t.contexts = SUC (LENGTH rest)` by simp[] >>
  drule_all asm_call_prepared_run_selectors >>
  disch_then (qspecl_then [`LENGTH c.logs`,`LENGTH s.rollback.toDelete`] strip_assume_tac) >>
  drule_all asm_call_prepared_run_adoption >> simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  drule_all asm_call_prepared_enter_view >> strip_tac >>
  `LENGTH v.contexts = SUC (LENGTH s.contexts)` by simp[] >>
  drule_all asm_frame_call_enter_transport >> simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
  drule_all asm_call_prepared_request >> strip_tac >>
  drule_all asm_call_prepared_enter_take_outcome >> strip_tac >>
  suspend "consume"
QED

Resume asm_frame_call_enter_step_ok[consume]:
  `a.as_accounts = s.rollback.accounts /\ a.as_transient = s.rollback.tStorage /\
   a.as_logs = c.logs /\ a.as_pending_deletions = s.rollback.toDelete /\
   a.as_memory = buffer_to_list c.memory` by
    (qpat_x_assum `asm_evm_rel _ _ _` mp_tac >> simp[asm_evm_rel_def]) >>
  qmatch_asmsub_abbrev_tac `adopt_outcome (request_of s) out _ = _` >>
  `take_outcome (request_of s) a.as_outcomes = (out,MAP SND (call_trace t))` by
    simp[Abbr `out`] >>
  `ct.stack = (if out.co_success then 1w else 0w)::
     DROP (6 + (if call_has_value op then 1 else 0)) c.stack /\
   ct.returnData = out.co_returnData` by simp[Abbr `out`] >>
  `buffer_to_list ct.memory = TAKE ro (asm_call_memory ao az ro rs a.as_memory) ++
     TAKE rs out.co_returnData ++ DROP (ro + LENGTH (TAKE rs out.co_returnData))
       (asm_call_memory ao az ro rs a.as_memory)` by metis_tac[] >>
  `adopt_outcome (request_of s) out (a.as_accounts,a.as_transient,a.as_logs) =
     (t.rollback.accounts,t.rollback.tStorage,ct.logs) /\
   adopt_outcome_deletions (request_of s) out a.as_pending_deletions = t.rollback.toDelete`
    by metis_tac[] >>
  SUBGOAL_THEN ``?d. t.msdomain = Collect d`` assume_tac >- simp[] >>
  `asm_call_memory ao az ro rs a.as_memory = asm_call_memory ao az ro rs a.as_memory` by simp[] >>
  drule_all asm_frame_call_effects_step_ok >> simp[]
QED

Finalise asm_frame_call_enter_step_ok

Theorem asm_frame_call_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CALL" \/ EL as.as_pc prog = AsmOp "STATICCALL") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `?c rb rest. es.contexts = (c,rb)::rest` by
    metis_tac[asm_frame_rel_def] >>
  qabbrev_tac `op = if EL as.as_pc prog = AsmOp "CALL" then Call else StaticCall` >>
  `op = if EL as.as_pc prog = AsmOp "CALL" then Call else StaticCall` by simp[Abbr `op`] >>
  Cases_on `asm_call_prepare op es` >> rename1 `asm_call_prepare op es = (q,u)` >>
  Cases_on `q`
  >- (PairCases_on `x` >>
      rename1 `asm_call_prepare op es =
        (INL (sender,address,value,ao,az,code,stipend,ro,rs,accounts),u)` >>
      Cases_on `(lookup_account sender accounts).balance < value \/ 1024 < LENGTH es.contexts`
      >- (drule_all asm_frame_call_abort_step >> simp[Abbr `op`]) >>
      `value <= (lookup_account sender accounts).balance /\ LENGTH es.contexts <= 1024`
        by (qpat_x_assum `~(_ \/ _)` mp_tac >> simp[]) >>
      Cases_on `asm_call_finish op (sender,address,value,ao,az,code,stipend,ro,rs,accounts) u` >>
      rename1 `asm_call_finish op _ u = (q,v)` >> Cases_on `q`
      >- (Cases_on `x` >> suspend "entered") >>
      drule_all asm_frame_call_terminal >> simp[Abbr `op`]) >>
  drule_all asm_frame_call_prepare_exit >> simp[Abbr `op`]
QED

Resume asm_frame_call_step[entered]:
  qpat_x_assum `Abbrev _` kall_tac >>
  `wf_state es /\ (?d. es.msdomain = Collect d) /\ ~c.msgParams.static /\
   asm_evm_rel (prog ++ [AsmDataItem data]) as es` by
    (fs[asm_frame_rel_def] >> gvs[]) >>
  SUBGOAL_THEN ``op = Call \/ op = StaticCall`` assume_tac
  >- (Cases_on `EL as.as_pc prog = AsmOp "CALL"` >> simp[]) >>
  `next_opcode c = SOME op` by
    (drule_all asm_frame_call_decode >> simp[] >> metis_tac[]) >>
  `step_call op es = (INL (),v)` by
    (qpat_x_assum `op = if _ then _ else _` kall_tac >>
     simp[asm_step_call_factor, bind_def]) >>
  `step es = (INL (),v)` by (drule_all asm_call_step_success >> simp[]) >>
  `6 + (if call_has_value op then 1 else 0) <= LENGTH c.stack` by
    (drule_all asm_call_prepare_success_stack >> simp[]) >>
  `observable_call c` by
    (simp[observable_call_def] >> Cases_on `op = Call` >> gvs[call_has_value_def]) >>
  drule_all asm_call_prepared_enter_view >> strip_tac >>
  `wf_state v /\ (?d. v.msdomain = Collect d)` by
    (conj_tac >- (drule_all step_preserves_wf_state >> simp[]) >>
     drule_at (Pat `step _ = _`) step_preserves_collect >> simp[]) >>
  `2 <= LENGTH v.contexts` by simp[] >>
  SUBGOAL_THEN ``?d. v.msdomain = Collect d`` assume_tac >- simp[] >>
  drule_all asm_call_child_run_normal >> strip_tac >>
  `LENGTH t.contexts = LENGTH es.contexts` by
    (qpat_x_assum `LENGTH t.contexts + 1 = _` mp_tac >> simp[]) >>
  drule_all asm_frame_call_enter_step_ok >> simp[]
QED

Finalise asm_frame_call_step
