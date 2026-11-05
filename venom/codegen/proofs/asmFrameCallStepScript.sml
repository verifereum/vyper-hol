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
  vfmAccountFrame asmEncodeParse rich_list vfmOperation regularMemorySim vfmBuffer vfmTypes list spillSim

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

Theorem asm_frame_call_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CALL" \/ EL as.as_pc prog = AsmOp "STATICCALL") ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
