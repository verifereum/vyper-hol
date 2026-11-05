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
  vfmExecution vfmExecutionProp vfmRunCall vfmContextLength vfmDecreasesGas
  vfmAccountFrame asmEncodeParse rich_list vfmOperation regularMemorySim vfmBuffer vfmTypes list

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

Theorem asm_frame_call_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CALL" \/ EL as.as_pc prog = AsmOp "STATICCALL") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
