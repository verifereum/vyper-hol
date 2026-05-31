(*
 * Algebraic Optimization — Per-Rule step_inst_base Equivalence
 *
 * TOP-LEVEL: ao_rule_*_step_equiv theorems
 *   Each proves that a 1-to-1 peephole replacement produces the same
 *   step_inst_base result as the original instruction.
 *
 * Helper: exec_pure helpers, lit_eq lemmas
 *)
Theory aoRules
Ancestors
  algebraicOptDefs venomExecSemantics venomState passSharedDefs
Libs
  pairLib

(* ===== lit_eq helpers ===== *)


(* ===== exec_pure1 / exec_pure2 / ASSIGN rewrite helpers ===== *)

(* Relate ASSIGN to exec_pure1 with identity *)

(* 0w - 1w = UINT_MAXw (all-ones word) *)
Triviality neg1_is_max[local]:
  (0w : 'a word) - 1w = UINT_MAXw
Proof
  rewrite_tac[GSYM wordsTheory.WORD_NOT_0] >>
  simp[wordsTheory.WORD_NOT, wordsTheory.word_sub_def, wordsTheory.WORD_NEG_0]
QED

(* (0w - 1w) - x = NOT(x) *)
Triviality neg1_sub_is_not[local]:
  (0w : 'a word) - 1w - x = word_1comp x
Proof
  rewrite_tac[wordsTheory.WORD_NOT, wordsTheory.word_sub_def,
              wordsTheory.WORD_ADD_ASSOC] >>
  metis_tac[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_ADD_ASSOC,
            wordsTheory.WORD_ADD_0]
QED

(* ===== Rule: ao_opt_shift — x >> 0 = x, x << 0 = x ===== *)

Theorem ao_rule_shl_zero:
  !inst x out s.
    inst.inst_opcode = SHL /\
    inst.inst_operands = [Lit 0w; x] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand x s` >> simp[wordsTheory.SHIFT_ZERO]
QED

Theorem ao_rule_shr_zero:
  !inst x out s.
    inst.inst_opcode = SHR /\
    inst.inst_operands = [Lit 0w; x] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand x s` >> simp[wordsTheory.SHIFT_ZERO]
QED

Theorem ao_rule_sar_zero:
  !inst x out s.
    inst.inst_opcode = SAR /\
    inst.inst_operands = [Lit 0w; x] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand x s` >> simp[wordsTheory.SHIFT_ZERO]
QED

(* ===== Rule: ao_opt_addsub ===== *)

(* x - x = 0 *)

(* x ^ x = 0 (XOR self) *)

(* x + 0 = x *)
Theorem ao_rule_add_zero:
  !inst op out s.
    inst.inst_opcode = ADD /\
    inst.inst_operands = [op; Lit 0w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[wordsTheory.WORD_ADD_0]
QED


val _ = export_theory();
