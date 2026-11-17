(* Source normalization and terminal bookkeeping for forwarded reverts.
   The old owner's exact exports become corollaries of these single proofs. *)
Theory symControlForwardSourceFacts
Ancestors
  fnFrameStepsRevertForward symControlTerminalSafetyOwn codegenSymRel
  symFrameControlFacts asmSplice asmSymSem asmSem stackPlanGen planExec
  frameRel contextCodegenRel venomExecSemantics venomInst

Theorem sym_rf_current_normalized_value:
  rf_value_inv fn ra bb j lo entry k s /\
  get_instruction bb k = SOME inst /\ k <= j /\
  MEM op (compute_operands inst) /\
  operand_val (frame_view fn ra s) lo op = value ==>
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] op) = value
Proof
  simp[fnFrameStepsRevertForwardTheory.rf_value_inv_def] >>
  metis_tac[fnFrameStepsRevertForwardTheory.rf_live_use_current]
QED

Theorem sym_rf_copy_normalized_range:
  rf_value_inv fn ra bb j lo entry i s /\
  get_instruction bb i = SOME inst /\ i <= j /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dop;sop;zop] /\
  operand_val (frame_view fn ra s) lo dop = SOME dst /\
  operand_val (frame_view fn ra s) lo zop = SOME sz ==>
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] dop) = SOME dst /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] zop) = SOME sz
Proof
  rpt strip_tac >>
  `MEM dop (compute_operands inst) /\ MEM zop (compute_operands inst)` by
    simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def] >>
  metis_tac[sym_rf_current_normalized_value]
QED

Theorem sym_rf_abort_source_fault:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = Abort ExHalt_abort fault ==>
  a = ExHalt_abort /\ vs_end = fault
Proof
  rpt strip_tac >>
  `i <= vs.vs_inst_idx /\ vs.vs_inst_idx <= j /\
   get_instruction bb vs.vs_inst_idx = SOME inst` by simp[] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_exec_abort_cases >> simp[]
QED

Theorem sym_rf_abort_source_success:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = OK copied ==>
  exec_block fuel ctx bb (copied with vs_inst_idx := SUC i) = Abort a vs_end
Proof
  rpt strip_tac >>
  `i <= vs.vs_inst_idx /\ vs.vs_inst_idx <= j /\
   get_instruction bb vs.vs_inst_idx = SOME inst` by simp[] >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_exec_abort_cases >> simp[]
QED

Theorem sym_rf_entry_future_non_phi:
  revert_forward_pair bb i j ==>
  !r ti. SUC i <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI
Proof
  rpt strip_tac >>
  `i <= r /\ r <> i` by decide_tac >>
  drule_all fnFrameStepsRevertForwardTheory.rf_forward_instruction_opcode >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem sym_rf_revert_runs_compose_mode:
  asm_steps lo o2pc prog n1 ast = AsmOK mid /\
  asm_steps lo o2pc prog n2 mid = AsmRevert out /\
  sym_steps_mode allow_own prog env own n1 ss = SymOK ss_mid /\
  sym_terminal (sym_steps_mode allow_own prog env own n2 ss_mid) ==>
  asm_steps lo o2pc prog (n1 + n2) ast = AsmRevert out /\
  sym_terminal (sym_steps_mode allow_own prog env own (n1 + n2) ss)
Proof
  strip_tac >> conj_tac
  >- (irule blockSimHelpersTheory.asm_steps_compose_revert >> metis_tac[]) >>
  simp[sym_steps_mode_add]
QED

Theorem sym_rf_entry_fault_terminal_mode:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = Abort ExHalt_abort fault /\
  asm_steps lo o2pc prog n ast = AsmFault out /\
  venom_asm_terminal_rel fault out /\
  sym_terminal (sym_steps_mode allow_own prog env own n ss) ==>
  ?m ast_end.
    ((a = Revert_abort /\ asm_steps lo o2pc prog m ast = AsmRevert ast_end) \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog m ast = AsmFault ast_end)) /\
    venom_asm_terminal_rel vs_end ast_end /\
    sym_terminal (sym_steps_mode allow_own prog env own m ss)
Proof
  rpt strip_tac >> drule_all sym_rf_abort_source_fault >> strip_tac >>
  qexistsl [`n`,`out`] >> simp[]
QED

Theorem sym_revert_postamble_steps:
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp revert_postamble) ==>
  sym_terminal (sym_steps p env 4 ss)
Proof
  strip_tac >>
  fs[revert_postamble_def, execute_plan_def, exec_stack_op_def,
     stackOpSimTheory.asm_block_at_cons] >>
  rewrite_tac[numLib.num_CONV ``4:num``, numLib.num_CONV ``3:num``,
              arithmeticTheory.TWO, arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  `word_of_bytes F (0w:bytes32) (REVERSE (encode_num_bytes_fuel 32 0)) = 0w`
    by EVAL_TAC >>
  simp[Once sym_step_def, sym_lift_def, asm_step_def, asm_next_def] >>
  simp[Once sym_step_def, sym_lift_def, asm_step_def, asm_next_def] >>
  simp[Once sym_step_def] >>
  simp[sym_step_op_def, asmSemTheory.dup_table_def, asmSemTheory.swap_table_def,
       sym_dup_def, sym_set_stack_def, asm_next_def] >>
  simp[Once sym_step_def, sym_terminal_opcode_concrete] >>
  simp[sym_step_concrete_def, asm_op_arity_def, asm_op_arity_table_def,
       sval_val_def, asm_op_mem_reads_def, asmSemTheory.log_table_def,
       mem_labels_hit_def, in_mem_range_def] >>
  simp[SRULE [asm_step_def] stackOpAsmSimTheory.asm_step_revert,
       asm_revert_op_def, sym_lift_def, sym_terminal_def]
QED

Theorem sym_revert_postamble_steps_mode:
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp revert_postamble) ==>
  sym_terminal (sym_steps_mode allow_own p env own 4 ss)
Proof
  strip_tac >> drule sym_revert_postamble_steps >>
  disch_then (qspec_then `env` assume_tac) >>
  `!msg. sym_steps p env 4 ss <> SymBad msg` by
    (Cases_on `sym_steps p env 4 ss` >> gvs[sym_terminal_def]) >>
  drule sym_steps_mode_nonbad >> simp[]
QED
