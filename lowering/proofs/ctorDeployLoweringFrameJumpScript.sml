Theory ctorDeployLoweringFrameJump
Ancestors
  ctorDeployLoweringFrameMachine planExec symbolResolve codegenEncodingWf
  asmParseProofs asmToBytecodeProofs vfmExecution vfmOperation vfmState
  vfmContext vfmSameFrame vfmHandleStep vfmRunCall evmStepSim
Libs wordsLib finite_mapLib

Theorem direct_jump_plan_encoding:
  FLOOKUP offsets target = SOME q /\ q < 65536 ==>
  FLAT (MAP (encode_inst offsets)
    (execute_plan initial_fmp [SOPushLabel target; SOEmit "JUMP"])) =
    97w :: (pad_bytes 2 (encode_num_bytes q) ++ [86w]) /\
  LENGTH (pad_bytes 2 (encode_num_bytes q)) = 2 /\
  word_of_bytes F (0w:256 word)
    (REVERSE (pad_bytes 2 (encode_num_bytes q))) = n2w q
Proof
  strip_tac >>
  drule encode_num_bytes_length_le_symbol_size >>
  simp[symbol_size_def] >> strip_tac >>
  simp[execute_plan_def, exec_stack_op_def, encode_inst_def,
       evm_opcode_byte_def, evm_opcode_table_def, symbol_size_def,
       pad_bytes_length] >>
  irule word_of_bytes_pad_encode_roundtrip >> EVAL_TAC
QED

Theorem direct_jump_parse_entry:
  FLOOKUP offsets target = SOME q /\ q < 65536 ==>
  FLOOKUP (parse_code p m
    (FLAT (MAP (encode_inst offsets)
      (execute_plan initial_fmp [SOPushLabel target; SOEmit "JUMP"])) ++ rest)) p =
  SOME (Push 2 (pad_bytes 2 (encode_num_bytes q)))
Proof
  strip_tac >> drule_all direct_jump_plan_encoding >>
  disch_then (qspec_then `initial_fmp` strip_assume_tac) >>
  simp[] >> irule parse_code_entry >> simp[] >>
  mp_tac (Q.SPECL [`2`, `pad_bytes 2 (encode_num_bytes q)`, `86w :: rest`]
    parse_opcode_push) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> simp[]
QED

Theorem root_handler_terminal[local]:
  LENGTH s.contexts = 1 ==> ISR (FST (handle_step e s))
Proof
  strip_tac >> Cases_on `handle_step e s` >> Cases_on `q` >> simp[] >>
  drule handle_step_preserves_length_1 >> simp[] >> strip_tac >>
  `s.contexts <> []` by (strip_tac >> gvs[]) >>
  drule_all handle_step_inl_pops >> simp[]
QED

Theorem direct_push_step[local]:
  s.contexts = [(ctxt,rb)] /\ ctxt.jumpDest = NONE /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME (Push 2 bytes) /\
  LENGTH bytes = 2 /\ step s = (INL (),s1) ==>
  ?ctxt1. s1.contexts = [(ctxt1,rb)] /\
    ctxt1.pc = ctxt.pc + 3 /\ ctxt1.jumpDest = NONE /\
    ctxt1.msgParams = ctxt.msgParams /\
    ctxt1.stack = word_of_bytes F (0w:256 word) (REVERSE bytes) :: ctxt.stack
Proof
  strip_tac >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, step_push_def] >>
  drule consume_gas_cases >> disch_then (qspec_then `3` mp_tac) >>
  strip_tac >> simp[static_gas_def]
  >- (simp[push_stack_def, bind_def, ignore_bind_def,
           get_current_context_def, return_def, assert_def,
           set_current_context_def] >>
      Cases_on `LENGTH ctxt.stack < 1024` >> simp[]
      >- (simp[inc_pc_or_jump_def, is_call_def, opcode_def,
               bind_def, get_current_context_def, return_def,
               set_current_context_def] >> strip_tac >>
          gvs[set_current_context_def]) >>
      disch_tac >>
      `ISR (FST (handle_step (SOME StackOverflow)
        (s with contexts := [(ctxt with gasUsed := ctxt.gasUsed + 3,rb)])))`
        by (irule root_handler_terminal >> simp[]) >> gvs[]) >>
  disch_tac >>
  `ISR (FST (handle_step (SOME OutOfGas) s))` by
    (irule root_handler_terminal >> simp[]) >> gvs[]
QED

Theorem direct_jump_step[local]:
  s.contexts = [(ctxt,rb)] /\
  FLOOKUP ctxt.msgParams.parsed ctxt.pc = SOME Jump /\
  ctxt.stack = (n2w q:256 word) :: stk /\ q < 65536 /\
  step s = (INL (),s1) ==>
  ?ctxt1. s1.contexts = [(ctxt1,rb)] /\ ctxt1.pc = q /\
    ctxt1.jumpDest = NONE /\ ctxt1.msgParams = ctxt.msgParams /\
    ctxt1.stack = stk
Proof
  strip_tac >>
  `w2n (n2w q:256 word) = q` by simp[wordsTheory.dimword_def] >>
  qpat_x_assum `step s = _` mp_tac >>
  simp[step_def, handle_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, step_inst_def, step_jump_def,
       pop_stack_def, assert_def, set_current_context_def] >>
  simp[consume_gas_def, bind_def, ignore_bind_def,
       get_current_context_def, return_def, assert_def,
       set_current_context_def] >>
  Cases_on `ctxt.gasUsed + 8 <= ctxt.msgParams.gasLimit` >> simp[]
  >- (simp[set_jump_dest_def, inc_pc_or_jump_def, is_call_def,
           bind_def, ignore_bind_def, get_current_context_def,
           return_def, set_current_context_def, assert_def] >>
      Cases_on `q < LENGTH ctxt.msgParams.code /\
                FLOOKUP ctxt.msgParams.parsed q = SOME JumpDest` >> simp[]
      >- (strip_tac >> gvs[]) >>
      disch_tac >>
      `ISR (FST (handle_step (SOME InvalidJumpDest)
        (s with contexts := [(ctxt with <|stack := stk;
           jumpDest := SOME q; gasUsed := ctxt.gasUsed + 8|>,rb)])))`
        by (irule root_handler_terminal >> simp[]) >> gvs[]) >>
  disch_tac >>
  `ISR (FST (handle_step (SOME OutOfGas)
      (s with contexts := [(ctxt with stack := stk,rb)])))`
    by (irule root_handler_terminal >> simp[]) >> gvs[]
QED

Theorem direct_jump_machine_boundary:
  wf_state s /\ LENGTH s.contexts = 1 /\
  (FST (HD s.contexts)).pc = p /\
  (FST (HD s.contexts)).jumpDest = NONE /\ q < 65536 /\
  FLOOKUP (FST (HD s.contexts)).msgParams.parsed p =
    SOME (Push 2 (pad_bytes 2 (encode_num_bytes q))) /\
  FLOOKUP (FST (HD s.contexts)).msgParams.parsed (p + 3) = SOME Jump /\
  step s = (INL (),s1) /\ step s1 = (INL (),s2) ==>
  (FST (HD s1.contexts)).pc = p + 3 /\
  (FST (HD s2.contexts)).pc = q /\
  LENGTH s1.contexts = 1 /\ LENGTH s2.contexts = 1 /\
  (FST (HD s1.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
  (FST (HD s2.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
  (FST (HD s2.contexts)).stack = (FST (HD s.contexts)).stack /\
  (FST (HD s2.contexts)).jumpDest = NONE
Proof
  strip_tac >>
  `?ctxt rb. s.contexts = [(ctxt,rb)]` by
    (gvs[listTheory.LENGTH_EQ_NUM_compute] >> metis_tac[pairTheory.PAIR]) >>
  gvs[] >>
  `LENGTH (pad_bytes 2 (encode_num_bytes q)) = 2` by
    (irule pad_bytes_length >>
     drule encode_num_bytes_length_le_symbol_size >> simp[symbol_size_def]) >>
  drule_all direct_push_step >> strip_tac >>
  `word_of_bytes F (0w:256 word)
      (REVERSE (pad_bytes 2 (encode_num_bytes q))) = n2w q` by
    (irule word_of_bytes_pad_encode_roundtrip >> EVAL_TAC) >>
  `FLOOKUP ctxt1.msgParams.parsed ctxt1.pc = SOME Jump` by simp[] >>
  `ctxt1.stack = (n2w q:256 word) :: ctxt.stack` by simp[] >>
  drule_all direct_jump_step >> strip_tac >> simp[]
QED

Theorem direct_jump_parse_second:
  FLOOKUP offsets target = SOME q /\ q < 65536 ==>
  FLOOKUP (parse_code p m
    (FLAT (MAP (encode_inst offsets)
      (execute_plan initial_fmp [SOPushLabel target; SOEmit "JUMP"])) ++ rest))
    (p + 3) = SOME Jump
Proof
  strip_tac >> drule_all direct_jump_plan_encoding >>
  disch_then (qspec_then `initial_fmp` strip_assume_tac) >> simp[] >>
  qabbrev_tac `bytes = pad_bytes 2 (encode_num_bytes q)` >>
  `LENGTH bytes = 2` by simp[Abbr `bytes`] >>
  qpat_x_assum `Abbrev _` kall_tac >>
  gvs[listTheory.LENGTH_EQ_NUM_compute] >>
  simp[Once parse_code_def, parse_opcode_cond_thm, wordsTheory.dimword_8,
       opcode_def] >>
  irule parse_code_entry >>
  simp[parse_opcode_cond_thm, wordsTheory.dimword_8]
QED
