(*
 * Algebraic Optimization — Per-Rule step_inst_base Equivalence
 *
 * TOP-LEVEL: ao_rule_*_step_equiv theorems
 *   Each proves that a 1-to-1 peephole replacement produces the same
 *   step_inst_base result as the original instruction.
 *
 * Helper: exec_pure helpers, lit_eq lemmas
 *)
Theory algebraicOptRules
Ancestors
  algebraicOptDefs venomExecSemantics venomState passSharedDefs
Libs
  pairLib

(* ===== lit_eq helpers ===== *)

Theorem lit_eq_imp[local]:
  !op v. lit_eq op v ==> op = Lit v
Proof
  Cases >> simp[lit_eq_def]
QED

(* ===== exec_pure1 / exec_pure2 / ASSIGN rewrite helpers ===== *)

(* Relate ASSIGN to exec_pure1 with identity *)
Theorem step_inst_base_assign_1op[local]:
  !inst op1 out s.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op1] /\
    inst.inst_outputs = [out] ==>
    step_inst_base inst s =
      case eval_operand op1 s of
        SOME v => OK (update_var out v s)
      | NONE => Error "undefined operand"
Proof
  rw[step_inst_base_def]
QED

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
Theorem ao_rule_sub_self:
  !inst op out s.
    inst.inst_opcode = SUB /\
    inst.inst_operands = [op; op] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[wordsTheory.WORD_SUB_REFL]
QED

(* x ^ x = 0 (XOR self) *)
Theorem ao_rule_xor_self:
  !inst op out s.
    inst.inst_opcode = XOR /\
    inst.inst_operands = [op; op] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[wordsTheory.WORD_XOR_CLAUSES]
QED

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

(* x - 0 = x *)
Theorem ao_rule_sub_zero:
  !inst op out s.
    inst.inst_opcode = SUB /\
    inst.inst_operands = [op; Lit 0w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[wordsTheory.WORD_SUB_RZERO]
QED

(* x ^ 0 = x (XOR zero) *)
Theorem ao_rule_xor_zero:
  !inst op out s.
    inst.inst_opcode = XOR /\
    inst.inst_operands = [op; Lit 0w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[wordsTheory.WORD_XOR_CLAUSES]
QED

(* (-1) - x = NOT(x) *)
Theorem ao_rule_sub_neg1:
  !inst op out s.
    inst.inst_opcode = SUB /\
    inst.inst_operands = [Lit (0w - 1w); op] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := NOT; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, exec_pure1_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[neg1_sub_is_not]
QED

(* x ^ (-1) = NOT(x) *)
Theorem ao_rule_xor_neg1:
  !inst op out s.
    inst.inst_opcode = XOR /\
    inst.inst_operands = [op; Lit (0w - 1w)] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := NOT; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, exec_pure1_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[neg1_is_max, wordsTheory.WORD_XOR_CLAUSES]
QED

(* ===== Rule: ao_opt_and ===== *)

(* x & MAX = x *)
Theorem ao_rule_and_max:
  !inst op out s.
    inst.inst_opcode = AND /\
    inst.inst_operands = [op; Lit (0w - 1w)] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[neg1_is_max, wordsTheory.WORD_AND_CLAUSES]
QED

(* x & 0 = 0 *)
Theorem ao_rule_and_zero_r:
  !inst op out s.
    inst.inst_opcode = AND /\
    inst.inst_operands = [op; Lit 0w] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[wordsTheory.WORD_AND_CLAUSES]
QED

(* 0 & x = 0 *)
Theorem ao_rule_and_zero_l:
  !inst op out s.
    inst.inst_opcode = AND /\
    inst.inst_operands = [Lit 0w; op] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[wordsTheory.WORD_AND_CLAUSES]
QED

(* ===== Rule: ao_opt_muldiv ===== *)

(* x * 0 = 0 *)
Theorem ao_rule_mul_zero_r:
  !inst op out s.
    inst.inst_opcode = MUL /\
    inst.inst_operands = [op; Lit 0w] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[wordsTheory.WORD_MULT_CLAUSES]
QED

(* 0 * x = 0 *)
Theorem ao_rule_mul_zero_l:
  !inst op out s.
    inst.inst_opcode = MUL /\
    inst.inst_operands = [Lit 0w; op] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[wordsTheory.WORD_MULT_CLAUSES]
QED

(* x * 1 = x *)
Theorem ao_rule_mul_one:
  !inst op out s.
    inst.inst_opcode = MUL /\
    inst.inst_operands = [op; Lit 1w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[wordsTheory.WORD_MULT_CLAUSES]
QED

(* x / 1 = x *)
Theorem ao_rule_div_one:
  !inst op out s.
    inst.inst_opcode = Div /\
    inst.inst_operands = [op; Lit 1w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[safe_div_def, wordsTheory.word_div_1]
QED

(* x % 1 = 0 *)
Theorem ao_rule_mod_one:
  !inst op out s.
    inst.inst_opcode = Mod /\
    inst.inst_operands = [op; Lit 1w] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[safe_mod_def, wordsTheory.WORD_MOD_1]
QED

(* ===== Rule: ao_opt_or ===== *)

(* x | MAX = MAX *)
Theorem ao_rule_or_max:
  !inst op out s.
    inst.inst_opcode = OR /\
    inst.inst_operands = [op; Lit (0w - 1w)] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN;
                    inst_operands := [Lit (0w - 1w)] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[neg1_is_max, wordsTheory.WORD_OR_CLAUSES]
QED

(* x | 0 = x *)
Theorem ao_rule_or_zero:
  !inst op out s.
    inst.inst_opcode = OR /\
    inst.inst_operands = [op; Lit 0w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[wordsTheory.WORD_OR_CLAUSES]
QED

(* ===== Rule: ao_opt_eq (1-to-1 cases) ===== *)

(* x == x = 1 *)
Theorem ao_rule_eq_self:
  !inst op out s.
    inst.inst_opcode = EQ /\
    inst.inst_operands = [op; op] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[bool_to_word_def]
QED

(* x == 0 = iszero(x) *)
Theorem ao_rule_eq_zero:
  !inst op out s.
    inst.inst_opcode = EQ /\
    inst.inst_operands = [op; Lit 0w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ISZERO; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, exec_pure1_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[bool_to_word_def]
QED

(* ===== Rule: ao_opt_comparator (1-to-1 cases) ===== *)

(* x cmp x = 0 (strict comparators are irreflexive) *)
Theorem ao_rule_cmp_self:
  !inst op out s.
    (inst.inst_opcode = GT \/ inst.inst_opcode = LT \/
     inst.inst_opcode = SGT \/ inst.inst_opcode = SLT) /\
    inst.inst_operands = [op; op] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[] >>
  gvs[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[bool_to_word_def, wordsTheory.WORD_LESS_REFL, wordsTheory.WORD_GREATER]
QED

val _ = export_theory();
