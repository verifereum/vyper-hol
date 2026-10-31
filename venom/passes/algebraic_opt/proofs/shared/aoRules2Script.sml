(*
 * Algebraic Optimization — Additional Per-Rule step_inst_base Equivalence
 *
 * TOP-LEVEL: ao_rule_* theorems for opcodes not covered by aoRules:
 *   - signextend identity (31w <=+ w)
 *   - power-of-two reductions (mul↔shl, div↔shr, mod↔and)
 *)
Theory aoRules2
Ancestors
  algebraicOptDefs venomExecSemantics venomState passSharedDefs passSharedPow2 valueRangeDefs
Libs
  pairLib wordsLib

(* ===== Signextend identity: 31w <=+ w ===== *)

Theorem ao_rule_signextend_ge31:
  !inst x out s w.
    inst.inst_opcode = SIGNEXTEND /\
    inst.inst_operands = [Lit w; x] /\
    inst.inst_outputs = [out] /\
    31w <=+ w ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand x s` >> simp[] >>
  `w2n w > 30` by fs[wordsTheory.WORD_LS] >>
  simp[sign_extend_def]
QED

(* ===== Power-of-two reductions ===== *)

(* is_power_of_two_exp is in passSharedPow2Theory, away from the
   integerTheory ancestors whose ** overloading gets in the way. *)

(* Each takes the exponent k explicitly; is_power_of_two_exp supplies it. *)
Theorem ao_rule_mul_pow2:
  !inst op out s w k.
    inst.inst_opcode = MUL /\
    inst.inst_operands = [op; Lit w] /\
    inst.inst_outputs = [out] /\
    w2n w = 2 ** k /\ k < dimindex(:256) ==>
    step_inst_base
      (inst with <| inst_opcode := SHL;
                    inst_operands := [Lit (word_log2 w); op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[word_log2_def, bitTheory.LOG2_TWOEXP] >>
  `k < dimword(:256)` by (
    simp[wordsTheory.dimword_def] >>
    `k < 2 ** k` by simp[arithmeticTheory.X_LT_EXP_X] >>
    `2 ** k < 2 ** 256` by (
      irule bitTheory.TWOEXP_MONO >> simp[]) >>
    decide_tac) >>
  simp[wordsTheory.w2n_n2w] >>
  `w = n2w (2 ** k)` by metis_tac[wordsTheory.n2w_w2n] >>
  simp[wordsTheory.WORD_MUL_LSL, wordsTheory.WORD_MULT_COMM]
QED

Theorem ao_rule_div_pow2:
  !inst op out s w k.
    inst.inst_opcode = Div /\
    inst.inst_operands = [op; Lit w] /\
    inst.inst_outputs = [out] /\
    w2n w = 2 ** k /\ k < dimindex(:256) ==>
    step_inst_base
      (inst with <| inst_opcode := SHR;
                    inst_operands := [Lit (word_log2 w); op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[word_log2_def, safe_div_def, bitTheory.LOG2_TWOEXP] >>
  `w <> 0w` by (strip_tac >> gvs[]) >> simp[] >>
  `k < dimword(:256)` by (
    simp[wordsTheory.dimword_def] >>
    `k < 2 ** k` by simp[arithmeticTheory.X_LT_EXP_X] >>
    `2 ** k < 2 ** 256` by (
      irule bitTheory.TWOEXP_MONO >> simp[]) >>
    decide_tac) >>
  simp[wordsTheory.w2n_n2w] >>
  `w = n2w (2 ** k)` by metis_tac[wordsTheory.n2w_w2n] >>
  simp[] >> simp[wordsTheory.WORD_DIV_LSR]
QED

Theorem ao_rule_mod_pow2:
  !inst op out s w k.
    inst.inst_opcode = Mod /\
    inst.inst_operands = [op; Lit w] /\
    inst.inst_outputs = [out] /\
    w2n w = 2 ** k /\ k < dimindex(:256) ==>
    step_inst_base
      (inst with <| inst_opcode := AND;
                    inst_operands := [op; Lit (w - 1w)] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[safe_mod_def] >>
  `w <> 0w` by (strip_tac >> gvs[]) >> simp[] >>
  simp[wordsTheory.word_mod_def] >>
  `w = n2w (2 ** k)` by metis_tac[wordsTheory.n2w_w2n] >>
  gvs[] >>
  `2 ** k < dimword(:256)` by (
    simp[wordsTheory.dimword_def] >>
    irule bitTheory.TWOEXP_MONO >> simp[]) >>
  simp[wordsTheory.w2n_n2w] >>
  (* n2w(2^k) - 1w = n2w(2^k - 1) by n2w_sub *)
  (* KEY: x AND (n2w(2^k) - 1w) = word_mod x (n2w(2^k)) = n2w(w2n x MOD 2^k)
     Need: n2w(2^k) - 1w = n2w(2^k - 1), then WORD_AND_EXP_SUB1. *)
  `n2w (2 ** k) - 1w = n2w (2 ** k - 1) : bytes32` by
    simp[GSYM wordsTheory.n2w_sub] >>
  gvs[] >>
  `x && n2w (2 ** k - 1) = n2w (w2n x) && n2w (2 ** k - 1)` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[wordsTheory.WORD_AND_EXP_SUB1]
QED


