(* Memory-free raw_call result prefix: no intermediate values are needed. *)
Theory rawCallResultFrame
Ancestors
  exprLoweringProps fragExecMem instMemFrontier memSafeRun venomMemProps
  venomInstProofs1 venomState venomInst venomExecSemantics list

Theorem raw_call_result_prefix_mem_ok:
  EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE; LT; XOR; MUL]) code ==>
  run_inst_seq_mem_ok code s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_every >>
  fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
  strip_tac >> gvs[below_frontier_no_ranges, inst_dload_in_section_other]
QED

Theorem raw_call_result_step_operand[local]:
  step_inst_base i s = OK t /\
  MEM i.inst_opcode [RETURNDATASIZE; LT; XOR; MUL] /\
  (!v. op = Var v ==> ~MEM v i.inst_outputs) ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >>
  `~is_terminator i.inst_opcode` by gvs[is_terminator_def] >>
  drule_all step_inst_base_preserves_all >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]
QED

Theorem raw_call_result_prefix_operand:
  EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE; LT; XOR; MUL] /\
    (!v. op = Var v ==> ~MEM v i.inst_outputs)) code /\
  run_inst_seq code s = OK t ==>
  eval_operand op t = eval_operand op s
Proof
  strip_tac >> irule run_inst_seq_preserves_field >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  irule raw_call_result_step_operand >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem raw_call_result_prefix_frontier:
  EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE; LT; XOR; MUL]) code /\
  run_inst_seq code s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule run_inst_seq_preserves_field >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  irule step_inst_base_preserves_alloca_next >>
  qexists_tac `i` >> simp[] >> fs[EVERY_MEM] >>
  first_x_assum drule >> strip_tac >> gvs[]
QED
