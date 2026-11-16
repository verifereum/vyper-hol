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
  cheat
QED

Theorem sym_step_own_pc_next:
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ∧
  sym_step_own p env own inst ss = SymOK ss' ⇒
  ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  cheat
QED

Theorem sym_step_own_prog_cong:
  (∀l. MEM (AsmDataHeader l) p ⇔ MEM (AsmDataHeader l) p') ∧
  inst ≠ AsmOp "JUMP" ∧ inst ≠ AsmOp "JUMPI" ⇒
  sym_step_own p env own inst ss = sym_step_own p' env own inst ss
Proof
  cheat
QED

Theorem sym_step_own_base_stack:
  ss.sym_base.as_stack = [] ∧ sym_step_own p env own inst ss = SymOK ss' ⇒
  ss'.sym_base.as_stack = []
Proof
  cheat
QED
