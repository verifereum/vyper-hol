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
