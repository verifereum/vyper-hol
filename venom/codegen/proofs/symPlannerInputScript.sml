Theory symPlannerInput
Ancestors
  symPlannerMoves symPlannerBase symPlannerScratch stackPlanGen stackPlanOps
  stackModel stackOpSim planExec asmSymSem asmSem codegenSymRel list
  deepResidualBudget allocMono

Theorem sym_push_kind_step:
  sym_kinds_ok cplan fn ret srest ps ss /\ op_kind_ok fn ret op sv ==>
  ?last. sym_set_stack (sv :: ss.sym_stack) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_push op ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> simp[sym_set_stack_def, asm_next_def,
    sym_kinds_ok_base_change, sym_kinds_ok_push]
QED

Theorem sym_exec_push_kind:
  sym_kinds_ok cplan fn ret srest ps ss /\ op_kind_ok fn ret op sv /\
  execute_plan initial_fmp [sop] = [inst] /\
  sym_step p env inst ss = sym_set_stack (sv :: ss.sym_stack) ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [sop]) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp [sop])) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_push op ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [sop]) /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  rw[] >> drule_all_then strip_assume_tac sym_push_kind_step >>
  metis_tac[sym_steps_singleton]
QED

Theorem sym_exec_push_label:
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOPushLabel l]) ==>
  ?last. sym_steps p env (LENGTH (execute_plan initial_fmp [SOPushLabel l])) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := stack_push (Label l) ps.ps_stack) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [SOPushLabel l]) /\
    last.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> irule sym_exec_push_kind >>
  dsimp[execute_plan_def, exec_stack_op_def, sym_step_def, op_kind_ok_def]
QED
