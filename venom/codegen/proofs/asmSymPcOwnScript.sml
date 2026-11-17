(* PC transport for symbolic steps reading fixed own-code bytes. *)
Theory asmSymPcOwn
Ancestors
  asmSymOwnCode asmSymPc asmSymSem asmSem

Theorem sym_step_own_eq:
  inst ≠ AsmOp "CODESIZE" ∧ inst ≠ AsmOp "CODECOPY" ⇒
  sym_step_own p env own inst ss = sym_step p env inst ss
Proof
  Cases_on `inst` >>
  simp[sym_step_own_def, sym_step_op_own_def, sym_step_def]
QED

Theorem sym_step_own_pc_add:
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ⇒
  sym_step_own p env own inst (sym_with_pc (ss.sym_base.as_pc + n) ss) =
  sym_result_pc_add n (sym_step_own p env own inst ss)
Proof
  strip_tac >> Cases_on `inst = AsmOp "CODESIZE"`
  >- gvs[sym_step_own_def, sym_step_op_own_def, sym_set_stack_pc_add] >>
  Cases_on `inst = AsmOp "CODECOPY"`
  >- (gvs[sym_step_own_def, sym_step_op_own_def, sym_codecopy_own_def] >>
      Cases_on `ss.sym_stack` >- simp[sym_result_pc_add_def] >>
      rename1 `ss.sym_stack = x1 :: t1` >>
      Cases_on `t1` >- simp[sym_result_pc_add_def] >>
      rename1 `ss.sym_stack = x1 :: x2 :: t2` >>
      Cases_on `t2` >- (Cases_on `x1` >> Cases_on `x2` >> simp[sym_result_pc_add_def]) >>
      rename1 `ss.sym_stack = x1 :: x2 :: x3 :: t3` >>
      Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >>
      rw[sym_result_pc_add_def] >>
      irule sym_lift_step_pc_add >> simp[asm_copy_to_mem_pc_add]) >>
  simp[sym_step_own_eq, sym_step_pc_add]
QED

Theorem sym_step_own_pc_next:
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ∧
  sym_step_own p env own inst ss = SymOK ss' ⇒
  ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  strip_tac >> Cases_on `inst = AsmOp "CODESIZE"`
  >- (gvs[sym_step_own_def, sym_step_op_own_def] >>
      drule sym_set_stack_pc_next >> simp[]) >>
  Cases_on `inst = AsmOp "CODECOPY"`
  >- (gvs[sym_step_own_def, sym_step_op_own_def, sym_codecopy_own_def,
          AllCaseEqs()] >>
      drule sym_lift_ok >> strip_tac >>
      gvs[asm_copy_to_mem_def, AllCaseEqs(), asm_next_def]) >>
  gvs[sym_step_own_eq] >> metis_tac[sym_step_pc_next]
QED

Theorem sym_step_own_prog_cong:
  (∀l. MEM (AsmDataHeader l) p ⇔ MEM (AsmDataHeader l) p') ∧
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ⇒
  sym_step_own p env own inst ss = sym_step_own p' env own inst ss
Proof
  strip_tac >> Cases_on `inst = AsmOp "CODESIZE"`
  >- gvs[sym_step_own_def, sym_step_op_own_def] >>
  Cases_on `inst = AsmOp "CODECOPY"`
  >- gvs[sym_step_own_def, sym_step_op_own_def, sym_codecopy_own_def,
         sym_data_label_def] >>
  simp[sym_step_own_eq] >> irule sym_step_prog_cong >> simp[]
QED

Theorem sym_step_own_base_stack:
  ss.sym_base.as_stack = [] ∧ sym_step_own p env own inst ss = SymOK ss' ⇒
  ss'.sym_base.as_stack = []
Proof
  strip_tac >> Cases_on `inst = AsmOp "CODESIZE"`
  >- (gvs[sym_step_own_def, sym_step_op_own_def] >>
      drule sym_set_stack_base >> simp[asm_next_def] >> strip_tac >> gvs[]) >>
  Cases_on `inst = AsmOp "CODECOPY"`
  >- (gvs[sym_step_own_def, sym_step_op_own_def, sym_codecopy_own_def,
          AllCaseEqs()] >> metis_tac[sym_lift_ok]) >>
  gvs[sym_step_own_eq] >> metis_tac[sym_step_base_stack]
QED
