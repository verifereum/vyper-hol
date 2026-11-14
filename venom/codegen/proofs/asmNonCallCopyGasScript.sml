(* Copy and log instruction gas accounting before exception handling. *)
Theory asmNonCallCopyGas
Ancestors
  asmFrameRel asmRunBounded frameStep asmFrameLocalStep asmCallGasArithmetic
  vfmExecution vfmExecutionProp vfmConstants vfmOperation asmFrameCallStep codegenRel vfmState asmSem asmWf asmEncodeParse symbolResolve

Theorem step_log_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  c.stack = off::sz::stk /\ n <= 4 /\
  (w2n sz = 0 \/ w2n off + w2n sz <= H) /\
  1875 + 8 * H + memory_cost H <= B /\
  B <= c.msgParams.gasLimit - c.gasUsed /\
  step_log n es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  `memory_expansion_cost (buffer_length c.memory)
    (if 0 < w2n sz then word_size (w2n off + w2n sz) * 32 else 0)
     <= memory_cost H` by
    (Cases_on `w2n sz = 0` >> simp[] >>
     once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     irule memory_expansion_cost_bound >> gvs[]) >>
  gvs[step_log_def, pop_stack_def, memory_expansion_info_def,
      LET_THM, bind_def, ignore_bind_def, get_current_context_def,
      return_def, set_current_context_def, assert_def, fail_def,
      log_topic_cost_def, log_data_cost_def, static_gas_def] >>
  gvs[consume_gas_def, expand_memory_def, read_memory_def,
      assert_not_static_def, get_static_def, get_callee_def, push_logs_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem copy_to_memory_gas_budget:
  !es c rb rest src address szn offset sourceOffset H gas B r s'.
  es.contexts = (c,rb)::rest /\ wf_context c /\
  (src = NONE \/ src = SOME get_call_data \/
   src = SOME get_current_code \/ src = SOME (get_code address)) /\
  (szn = 0 \/ offset + szn <= H) /\
  (src = NONE ==> szn = 0 \/ sourceOffset + szn <= H) /\
  gas + 3 * H + memory_cost H <= B /\
  B <= c.msgParams.gasLimit - c.gasUsed /\
  copy_to_memory gas offset sourceOffset szn src es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `3 * word_size szn <= 3 * H` by
    (Cases_on `szn = 0` >- simp[word_size_def] >>
     `word_size szn <= szn` by simp[word_size_def, arithmeticTheory.DIV_LE_X] >>
     gvs[] >> decide_tac) >>
  `memory_expansion_cost (buffer_length c.memory)
    (if 0 < SND (if src = NONE then max_expansion_range (offset,szn) (sourceOffset,szn)
                else (offset,szn))
     then word_size (FST (if src = NONE then max_expansion_range (offset,szn) (sourceOffset,szn)
                         else (offset,szn)) +
                     SND (if src = NONE then max_expansion_range (offset,szn) (sourceOffset,szn)
                          else (offset,szn))) * 32 else 0) <= memory_cost H` by
    (Cases_on `src = NONE` >> simp[]
     >- (once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
         irule call_memory_expansion_cost_bound >> gvs[]) >>
     Cases_on `szn = 0` >> simp[] >>
     once_rewrite_tac[arithmeticTheory.MULT_COMM] >>
     irule memory_expansion_cost_bound >> gvs[]) >>
  Cases_on `max_expansion_range (offset,szn) (sourceOffset,szn)` >>
  gvs[copy_to_memory_def, memory_expansion_info_def,
      LET_THM, bind_def, ignore_bind_def, get_current_context_def,
      return_def, set_current_context_def, assert_def, fail_def,
      memory_copy_cost_def] >>
  gvs[consume_gas_def, expand_memory_def, read_memory_def, write_memory_def,
      get_call_data_def, get_current_code_def, get_code_def, get_accounts_def,
      bind_def, ignore_bind_def, get_current_context_def, return_def,
      set_current_context_def, assert_def, fail_def, LET_THM,
      wf_context_def, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >> decide_tac
QED

Theorem step_copy_to_memory_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  (op = CallDataCopy /\ src = SOME get_call_data /\ name = "CALLDATACOPY" \/
   op = CodeCopy /\ src = SOME get_current_code /\ name = "CODECOPY" \/
   op = MCopy /\ src = NONE /\ name = "MCOPY") /\
  asm_inst_gas_ok H (AsmOp name) c.stack /\
  3 + 3 * H + memory_cost H <= B /\
  B <= c.msgParams.gasLimit - c.gasUsed /\
  step_copy_to_memory op src es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `c.stack`
  >- gvs[step_copy_to_memory_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::stk` >> Cases_on `stk`
  >- gvs[step_copy_to_memory_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::so::stk'` >> Cases_on `stk'`
  >- gvs[step_copy_to_memory_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::so::sz::tail` >>
  gvs[step_copy_to_memory_def, pop_stack_def, bind_def, ignore_bind_def,
      get_current_context_def, assert_def, fail_def, return_def,
      set_current_context_def] >>
  qmatch_asmsub_abbrev_tac `copy_to_memory _ _ _ _ _ es' = _` >>
  `frame_gas_left es' = frame_gas_left es` by
    simp[Abbr `es'`, frame_gas_left_def] >>
  (qsuff_tac `r <> INR (SOME OutOfGas) /\
     frame_gas_left es' <= frame_gas_left s' + B` >- gvs[]) >>
  irule copy_to_memory_gas_budget >>
  gvs[Abbr `es'`, wf_context_def, static_gas_def] >>
  qexistsl_tac [`H`, `0w`] >> goal_assum (drule_at Any) >>
  gvs[asm_inst_gas_ok_def, asm_mem_ranges_def]
QED

Theorem step_ext_code_copy_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  asm_inst_gas_ok H (AsmOp "EXTCODECOPY") c.stack /\
  2600 + 3 * H + memory_cost H <= B /\
  B <= c.msgParams.gasLimit - c.gasUsed /\
  step_ext_code_copy es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >> Cases_on `c.stack`
  >- gvs[step_ext_code_copy_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = addr::stk` >> Cases_on `stk`
  >- gvs[step_ext_code_copy_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = addr::off::stk'` >> Cases_on `stk'`
  >- gvs[step_ext_code_copy_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = addr::off::so::stk''` >> Cases_on `stk''`
  >- gvs[step_ext_code_copy_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = addr::off::so::sz::tail` >>
  gvs[step_ext_code_copy_def, pop_stack_def, access_address_def,
      domain_check_def, set_domain_def, bind_def, ignore_bind_def,
      get_current_context_def, assert_def, fail_def, return_def,
      set_current_context_def, LET_THM, AllCaseEqs()]
  >~ [`frame_gas_left es <= B + frame_gas_left (es with contexts := _)`]
    >- simp[frame_gas_left_def] >>
  qmatch_asmsub_abbrev_tac `copy_to_memory _ _ _ _ _ es' = _` >>
  `frame_gas_left es' = frame_gas_left es` by
    simp[Abbr `es'`, frame_gas_left_def] >>
  (qsuff_tac `r <> INR (SOME OutOfGas) /\
     frame_gas_left es' <= frame_gas_left s' + B` >- gvs[]) >>
  irule copy_to_memory_gas_budget >>
  gvs[Abbr `es'`, wf_context_def, static_gas_def] >>
  qexistsl_tac [`H`, `w2w addr`] >> goal_assum (drule_at Any) >>
  gvs[asm_inst_gas_ok_def, asm_mem_ranges_def,
      warm_access_cost_def, cold_access_cost_def] >>
  rpt IF_CASES_TAC >> gvs[] >> decide_tac
QED

Theorem step_asm_log_gas_budget:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  (name = "LOG0" /\ n = 0 \/ name = "LOG1" /\ n = 1 \/
   name = "LOG2" /\ n = 2 \/ name = "LOG3" /\ n = 3 \/
   name = "LOG4" /\ n = 4) /\
  asm_inst_gas_ok H (AsmOp name) c.stack /\
  1875 + 8 * H + memory_cost H <= B /\
  B <= c.msgParams.gasLimit - c.gasUsed /\
  step_log n es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `c.stack`
  >- gvs[step_log_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::stk` >> Cases_on `stk`
  >- gvs[step_log_def, pop_stack_def, bind_def, ignore_bind_def,
         get_current_context_def, assert_def, fail_def, return_def,
         frame_gas_left_def] >>
  rename1 `c.stack = off::sz::tail` >>
  irule step_log_gas_budget >> simp[] >>
  (conj_tac >- (qexists_tac `n` >> gvs[])) >>
  qexists_tac `H` >> gvs[asm_inst_gas_ok_def, asm_mem_ranges_def]
QED

Theorem asm_frame_copy_decode[local]:
  asm_frame_prog_ok prog /\ asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  a.as_pc < LENGTH prog /\ EL a.as_pc prog = AsmOp name /\
  MEM name ["CALLDATACOPY";"CODECOPY";"EXTCODECOPY";"MCOPY";
            "LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] ==>
  next_opcode (FST (HD es.contexts)) = SOME
    (if name = "CALLDATACOPY" then CallDataCopy else
     if name = "CODECOPY" then CodeCopy else
     if name = "EXTCODECOPY" then ExtCodeCopy else
     if name = "MCOPY" then MCopy else
     if name = "LOG0" then Log 0 else if name = "LOG1" then Log 1 else
     if name = "LOG2" then Log 2 else if name = "LOG3" then Log 3 else Log 4)
Proof
  strip_tac >> irule asm_frame_opcode_decode >>
  (conj_tac >- gvs[listTheory.MEM, wf_opname_def]) >>
  qexistsl_tac [`a`, `data`, `prog`] >>
  gvs[listTheory.MEM] >>
  simp[is_data_inst_def, encode_inst_def, opcode_def] >> EVAL_TAC >>
  wordsLib.WORD_DECIDE_TAC
QED

Theorem asm_frame_copy_raw_gas:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    EL a.as_pc prog <> AsmOp "RETURNDATACOPY" /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    50000 + 8 * H + memory_cost H <= frame_gas_left es /\
    EL a.as_pc prog <> AsmOp "CALL" /\
    EL a.as_pc prog <> AsmOp "STATICCALL" /\
    (?name. EL a.as_pc prog = AsmOp name /\
      MEM name ["CALLDATACOPY";"CODECOPY";"EXTCODECOPY";"MCOPY";
                "LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]) ==>
    !op r s'.
      next_opcode (FST (HD es.contexts)) = SOME op /\
      step_inst op es = (r,s') /\
      LENGTH s'.contexts = LENGTH es.contexts ==>
      r <> INR (SOME OutOfGas) /\
      frame_gas_left es <= frame_gas_left s' + (50000 + 8 * H + memory_cost H)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `asm_frame_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >>
  `c.stack = a.as_stack` by gvs[asm_evm_rel_def] >>
  `wf_context c` by gvs[wf_state_def] >>
  `50000 + 8 * H + memory_cost H <= c.msgParams.gasLimit - c.gasUsed` by
    gvs[frame_gas_left_def] >>
  drule_all asm_frame_copy_decode >> strip_tac >>
  gvs[listTheory.MEM] >> rpt gen_tac >> strip_tac >> gvs[step_inst_def] >>
  `3 + 3 * H + memory_cost H <= 50000 + 8 * H + memory_cost H` by decide_tac >>
  `2600 + 3 * H + memory_cost H <= 50000 + 8 * H + memory_cost H` by decide_tac >>
  `1875 + 8 * H + memory_cost H <= 50000 + 8 * H + memory_cost H` by decide_tac >>
  (qsuff_tac `r <> INR (SOME OutOfGas) /\
    frame_gas_left es <= frame_gas_left s' + (50000 + 8 * H + memory_cost H)`
   >- (strip_tac >> gvs[] >> decide_tac))
  >~ [`step_ext_code_copy es = (r,s')`]
    >- (irule step_ext_code_copy_gas_budget >> simp[] >> qexists_tac `H` >> simp[])
  >~ [`step_copy_to_memory CallDataCopy _ es = (r,s')`]
    >- (irule step_copy_to_memory_gas_budget >> simp[] >>
        qexists_tac `H` >> goal_assum (drule_at Any) >> simp[])
  >~ [`step_copy_to_memory CodeCopy _ es = (r,s')`]
    >- (irule step_copy_to_memory_gas_budget >> simp[] >>
        qexists_tac `H` >> goal_assum (drule_at Any) >> simp[])
  >~ [`step_copy_to_memory MCopy _ es = (r,s')`]
    >- (irule step_copy_to_memory_gas_budget >> simp[] >>
        qexists_tac `H` >> goal_assum (drule_at Any) >> simp[]) >>
  irule step_asm_log_gas_budget >> simp[] >>
  qexists_tac `H` >> goal_assum (drule_at Any) >> simp[]
QED
