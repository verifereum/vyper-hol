Theory asmFrameCreateStatic
Ancestors
  vfmExecution vfmExecutionProp

Theorem asm_create_static_charge[local]:
  s.contexts <> [] /\ (FST (HD s.contexts)).msgParams.static ==>
  (do consume_gas n; assert_not_static; k od) s =
    if (FST (HD s.contexts)).gasUsed + n <=
       (FST (HD s.contexts)).msgParams.gasLimit then
      (INR (SOME WriteInStaticContext),
       s with contexts :=
         (FST (HD s.contexts) with gasUsed :=
            (FST (HD s.contexts)).gasUsed + n,
          SND (HD s.contexts))::TL s.contexts)
    else (INR (SOME OutOfGas),s)
Proof
  strip_tac >>
  Cases_on `(FST (HD s.contexts)).gasUsed + n <=
            (FST (HD s.contexts)).msgParams.gasLimit` >>
  simp[consume_gas_def, assert_not_static_def, get_static_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def]
QED

Theorem asm_create_static_memory[local]:
  s.contexts <> [] /\ (FST (HD s.contexts)).msgParams.static ==>
  (do expand_memory expansion;
      code <- read_memory off sz;
      sender <- get_callee; accounts <- get_accounts;
      assert (LENGTH code <= 2 * max_code_size) OutOfGas;
      gasLeft <- get_gas_left;
      consume_gas (gasLeft - gasLeft DIV 64);
      assert_not_static; k code sender accounts gasLeft
   od) s =
   let c = FST (HD s.contexts);
       p = c with memory := buffer_extend expansion c.memory;
       u = s with contexts := (p,SND (HD s.contexts))::TL s.contexts;
       gas = (c.msgParams.gasLimit - c.gasUsed) -
             (c.msgParams.gasLimit - c.gasUsed) DIV 64
   in
     if LENGTH (buffer_take off sz p.memory) <= 2 * max_code_size then
       if c.gasUsed + gas <= c.msgParams.gasLimit then
         (INR (SOME WriteInStaticContext),
          u with contexts := (p with gasUsed := c.gasUsed + gas,
                              SND (HD s.contexts))::TL s.contexts)
       else (INR (SOME OutOfGas),u)
     else (INR (SOME OutOfGas),u)
Proof
  strip_tac >>
  simp[expand_memory_def, read_memory_def, get_callee_def, get_accounts_def,
       get_gas_left_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def,
       asm_create_static_charge] >>
  simp[SRULE[bind_def, ignore_bind_def] asm_create_static_charge] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem asm_create_static_failure_view:
  s.contexts = (c,rb)::rest /\ wf_state s /\ s.msdomain = Collect d /\
  c.msgParams.static /\ (if two then 4 else 3) <= LENGTH c.stack ==>
  ?ex t p. step_create two s = (INR (SOME ex),t) /\
    (ex = OutOfGas \/ ex = WriteInStaticContext) /\
    t.contexts = (p,rb)::rest /\ p.msgParams = c.msgParams /\
    t.txParams = s.txParams /\ p.gasUsed <= p.msgParams.gasLimit
Proof
  strip_tac >>
  `c.gasUsed <= c.msgParams.gasLimit` by gvs[wf_state_def, wf_context_def] >>
  simp[step_create_def, pop_stack_def, memory_expansion_info_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `consume_gas charge _` >>
  qmatch_goalsub_abbrev_tac `expand_memory expansion _` >>
  simp[Once consume_gas_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def,
       assert_def, return_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `if paid then _ else _` >>
  Cases_on `paid` >>
  simp[SRULE[bind_def, ignore_bind_def, assert_def, return_def, fail_def]
         asm_create_static_memory] >>
  rpt IF_CASES_TAC >> gvs[]
QED

(* The static-frame counterpart of the non-static creation budget: after the
   upfront charge, the reserved 63/64 is consumed and the frame faults, so the
   caller keeps at least a 64th of what remains past any budget B >= k. *)
Theorem asm_create_static_budget:
  s.contexts = (c,rb)::rest /\ wf_state s /\ s.msdomain = Collect d /\
  c.msgParams.static /\ (if two then 4 else 3) <= LENGTH c.stack /\
  w2n (EL 2 c.stack) <= 2 * max_code_size /\
  k = static_gas (if two then Create2 else Create) +
    init_code_word_cost * word_size (w2n (EL 2 c.stack)) +
    (if two then keccak256_per_word_cost * word_size (w2n (EL 2 c.stack)) else 0) +
    memory_expansion_cost (buffer_length c.memory)
      (if 0 < w2n (EL 2 c.stack)
       then word_size (w2n (EL 1 c.stack) + w2n (EL 2 c.stack)) * 32 else 0) /\
  k <= B /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  step_create two s = (r,t) ==>
  r = INR (SOME WriteInStaticContext) /\
  ?p. t.contexts = (p,rb)::rest /\ p.msgParams = c.msgParams /\
    (c.msgParams.gasLimit - c.gasUsed - B) DIV 64 <=
      p.msgParams.gasLimit - p.gasUsed
Proof
  strip_tac >>
  qpat_x_assum `k = _` (assume_tac o GSYM) >>
  `!off b. LENGTH (buffer_take off (w2n (EL 2 c.stack)) b) <=
           2 * max_code_size` by
    (rpt gen_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
     first_assum (irule_at Any) >>
     simp[vfmBufferTheory.buffer_take_to_list, listTheory.LENGTH_TAKE_EQ]) >>
  `(c.msgParams.gasLimit - (k + c.gasUsed)) DIV 64 <=
   c.msgParams.gasLimit - (k + c.gasUsed)` by
    (irule arithmeticTheory.DIV_LESS_EQ >> simp[]) >>
  `c.gasUsed <= c.msgParams.gasLimit` by gvs[wf_state_def, wf_context_def] >>
  `c.gasUsed + k <= c.msgParams.gasLimit` by decide_tac >>
  qpat_x_assum `step_create _ _ = _` mp_tac >>
  simp[step_create_def, pop_stack_def, memory_expansion_info_def,
       get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, return_def, assert_def, fail_def] >>
  qmatch_goalsub_abbrev_tac `consume_gas charge _` >>
  `charge = k` by
    (Cases_on `two` >> fs[Abbr `charge`, listTheory.EL_TAKE]) >>
  qpat_x_assum `Abbrev (charge = _)` kall_tac >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `_ = k` kall_tac >>
  simp[Once consume_gas_def, get_current_context_def,
       set_current_context_def, bind_def, ignore_bind_def,
       assert_def, return_def, fail_def] >>
  simp[SRULE[bind_def, ignore_bind_def, assert_def, return_def, fail_def]
         asm_create_static_memory] >>
  Cases_on `two` >> simp[listTheory.EL_TAKE] >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  irule arithmeticTheory.DIV_LE_MONOTONE >> simp[] >> decide_tac
QED
