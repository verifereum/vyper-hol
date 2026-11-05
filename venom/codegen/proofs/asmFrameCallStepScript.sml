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
  vfmAccountFrame asmEncodeParse rich_list vfmOperation regularMemorySim vfmBuffer vfmTypes list spillSim
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

Theorem asm_call_step_terminal:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall) /\
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
  qpat_x_assum `op = Call \/ op = StaticCall` strip_assume_tac >>
  gvs[step_inst_def, bind_def, ignore_bind_def]
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

Resume asm_call_prepare_failure_starved[single]:
  drule_all asm_handle_step_oog_singleton >> disch_tac >>
  `step s = (INR (SOME OutOfGas), t with contexts :=
    [(popped with <|gasUsed := popped.msgParams.gasLimit; returnData := []|>,rb)])`
    by metis_tac[] >>
  drule asm_run_call_stops_after_step >> simp[] >> strip_tac >>
  simp[frame_resource_starved_def, frame_outcome_def] >>
  qexistsl_tac [`OutOfGas`, `[]`, `[]`] >> simp[]
QED

Resume asm_call_prepare_failure_starved[nested]:
  `step s = (INL (), t with <| contexts :=
      (h0 with <|pc := SUC h0.pc; stack := 0w::h0.stack; returnData := [];
        memory := buffer_write mr.offset [] h0.memory|>,h1)::t'; rollback := rb|>)`
    by simp[] >>
  drule asm_run_call_stops_after_step >> simp[] >> strip_tac >>
  simp[frame_resource_starved_def, frame_outcome_def] >>
  metis_tac[]
QED
Finalise asm_call_prepare_failure_starved
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

Theorem asm_expand_memory_append_zeros[local]:
  asm_expand_memory n mem =
    mem ++ REPLICATE (MAX (LENGTH mem) (((n + 31) DIV 32) * 32) - LENGTH mem) 0w
Proof
  simp[asm_expand_memory_def] >> rw[arithmeticTheory.MAX_DEF] >> simp[]
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
      simp[asm_expand_memory_append_zeros, APPEND_ASSOC] >>
      rw[arithmeticTheory.MAX_DEF] >>
      simp[REPLICATE_APPEND] >> gvs[] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  `n <= m` by simp[] >> first_x_assum drule >> strip_tac >>
  simp[asm_expand_memory_append_zeros, APPEND_ASSOC] >>
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
    asm_expand_memory_nested, asm_expand_memory_append_zeros] >>
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
  drule_all asm_call_prepare_success_view >>
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

Theorem asm_call_step_success:
  s.contexts = (c,rb)::rest /\
  next_opcode c = SOME op /\ (op = Call \/ op = StaticCall) /\
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
  qpat_x_assum `op = Call \/ op = StaticCall` strip_assume_tac >>
  gvs[step_inst_def, inc_pc_or_jump_def, is_call_def, bind_def,
       ignore_bind_def, return_def]
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
  qpat_x_assum `asm_consume_call_outcome _ _ _ _ _ = _` mp_tac >>
  simp[asm_consume_call_outcome_eq] >> strip_tac >>
  qpat_x_assum `asm_frame_rel prog data es0 a s` mp_tac >>
  rewrite_tac[asm_frame_rel_def] >> strip_tac >>
  gvs[] >> simp[asm_frame_rel_def, asm_next_def] >>
  gvs[asm_evm_rel_def, asm_next_def]
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
  `?a1. asm_consume_call_outcome (request_of s) ro rs
    (DROP (6 + (if call_has_value op then 1 else 0)) a.as_stack)
    (a with as_memory := mem) = AsmOK a1` by
    simp[asm_consume_call_outcome_eq] >>
  drule_all asm_frame_call_effects_restore >> disch_tac >>
  pure_rewrite_tac[asm_frame_step_ok_def] >> disj2_tac >>
  gvs[] >> qexists_tac `t` >> asm_rewrite_tac[]
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
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all asm_call_prepare_success_view >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `u = s with <| contexts := (parent,rb)::rest;
    rollback := _; msdomain := _ |>` >>
  `u.contexts = (parent,rb)::rest` by simp[] >>
  `LENGTH u.contexts <= 1024` by
    (qpat_x_assum `LENGTH s.contexts <= 1024` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  drule_all asm_call_finish_terminal_kind >> simp[]
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
  pure_rewrite_tac[GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  `EVERY (wf_context o FST) s.contexts` by fs[wf_state_def] >>
  drule_all asm_call_prepare_stack_room >> disch_tac >>
  drule_all asm_call_prepare_stipend_paid >> disch_tac >>
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
  `p.contexts = (parent with returnData := [],rb)::rest /\ p.contexts <> []` by
    simp[Abbr `p`] >>
  `step_call op s = (INR NONE,v)` by
    (rewrite_tac[asm_step_call_factor, bind_def] >>
     qpat_assum `asm_call_prepare _ _ = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [] >>
     qpat_assum `asm_call_finish _ _ _ = _` (fn th => rewrite_tac[th])) >>
  `stipend <= (parent with returnData := []).gasUsed /\
   LENGTH (parent with returnData := []).stack < stack_limit` by
    fs[vfmConstantsTheory.stack_limit_def] >>
  drule_all asm_call_step_memory_success >> strip_tac >>
  suspend "returned"
QED

Resume asm_call_prepared_terminal_success_view[returned]:
  drule_all asm_proceed_call_saved_checkpoint >> strip_tac >>
  drule_all asm_proceed_call_terminal_effects >> strip_tac >>
  `op = StaticCall ==> value = 0` by
    (strip_tac >> gvs[call_has_value_def]) >>
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

Finalise asm_call_prepared_terminal_success_view

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

Theorem asm_frame_call_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CALL" \/ EL as.as_pc prog = AsmOp "STATICCALL") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
