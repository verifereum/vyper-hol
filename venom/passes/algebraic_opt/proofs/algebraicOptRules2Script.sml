(*
 * Algebraic Optimization — Additional Per-Rule step_inst_base Equivalence
 *
 * TOP-LEVEL: ao_rule_* theorems for opcodes not covered by algebraicOptRules:
 *   - signextend identity (w >= 31w)
 *   - exp rules (x**0=1, x**1=x, 1**x=1, 0**x=iszero)
 *   - safe_sdiv / safe_smod identities
 *   - power-of-two reductions (mul↔shl, div↔shr, mod↔and)
 *   - comparator boundary rules (GT x MAX=0, LT x 0=0, etc.)
 *)
Theory algebraicOptRules2
Ancestors
  algebraicOptDefs venomExecSemantics venomState passSharedDefs passSharedPow2 valueRangeDefs
Libs
  pairLib wordsLib

(* ===== Signextend identity: w >= 31w ===== *)

(* w >= 31w (signed comparison on bytes32) implies w2n w > 30.
   Proof: w >= 31w iff w2i w >= w2i 31w = 31 (by WORD_GEi).
   w2i w >= 31 > 0 means ~word_msb w, so w2i w = &(w2n w),
   hence w2n w >= 31 > 30. *)
Triviality ge_31w_implies_w2n_gt_30[local]:
  !w : bytes32. w >= 31w ==> w2n w > 30
Proof
  rpt strip_tac >>
  gvs[integer_wordTheory.WORD_GEi, integer_wordTheory.w2i_def] >>
  Cases_on `word_msb w` >> Cases_on `word_msb (31w:bytes32)` >>
  gvs[] >> intLib.ARITH_TAC
QED

Theorem ao_rule_signextend_ge31:
  !inst x out s w.
    inst.inst_opcode = SIGNEXTEND /\
    inst.inst_operands = [Lit w; x] /\
    inst.inst_outputs = [out] /\
    w >= 31w ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [x] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand x s` >> simp[] >>
  imp_res_tac ge_31w_implies_w2n_gt_30 >>
  simp[sign_extend_def]
QED

(* ===== Exp rules ===== *)

(* Helper: word_exp identities from nat EXP *)
Triviality word_exp_zero_exp[local]:
  !v : bytes32. v ** 0w = 1w
Proof
  simp[wordsTheory.word_exp_def]
QED

Triviality word_exp_one_exp[local]:
  !v : bytes32. v ** 1w = v
Proof
  gen_tac >>
  simp[wordsTheory.word_exp_def, arithmeticTheory.EXP_1]
QED

Triviality word_exp_base_one[local]:
  !e : bytes32. 1w ** e = 1w
Proof
  gen_tac >>
  simp[wordsTheory.word_exp_def, arithmeticTheory.EXP_1]
QED

Triviality word_exp_base_zero[local]:
  !e : bytes32. 0w ** e = bool_to_word (e = 0w)
Proof
  gen_tac >>
  simp[wordsTheory.word_exp_def, bool_to_word_def,
       arithmeticTheory.ZERO_EXP] >>
  Cases_on `e = 0w` >> simp[bool_to_word_def]
QED

Theorem ao_rule_exp_zero:
  !inst base_op out s.
    inst.inst_opcode = Exp /\
    inst.inst_operands = [base_op; Lit 0w] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand base_op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand base_op s` >> gvs[word_exp_zero_exp]
QED

Theorem ao_rule_exp_one:
  !inst base_op out s.
    inst.inst_opcode = Exp /\
    inst.inst_operands = [base_op; Lit 1w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [base_op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand base_op s` >> simp[word_exp_one_exp]
QED

Theorem ao_rule_exp_base_one:
  !inst exp_op out s.
    inst.inst_opcode = Exp /\
    inst.inst_operands = [Lit 1w; exp_op] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand exp_op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 1w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand exp_op s` >> gvs[word_exp_base_one]
QED

Theorem ao_rule_exp_base_zero:
  !inst exp_op out s.
    inst.inst_opcode = Exp /\
    inst.inst_operands = [Lit 0w; exp_op] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ISZERO; inst_operands := [exp_op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, exec_pure1_def,
     eval_operand_def] >>
  Cases_on `eval_operand exp_op s` >> simp[word_exp_base_zero]
QED

(* ===== Safe sdiv / smod identities ===== *)

Theorem ao_rule_sdiv_one:
  !inst op out s.
    inst.inst_opcode = SDIV /\
    inst.inst_operands = [op; Lit 1w] /\
    inst.inst_outputs = [out] ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  simp[safe_sdiv_def, wordsTheory.word_quot_def]
QED

Theorem ao_rule_smod_one:
  !inst op out s.
    inst.inst_opcode = SMOD /\
    inst.inst_operands = [op; Lit 1w] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[safe_smod_def, wordsTheory.word_rem_def, wordsTheory.WORD_MOD_1]
QED

(* ===== Power-of-two bridge ===== *)

(* Helper: BIT h (n-1) when 2^h < n < 2^(h+1) *)
Triviality bit_h_pred[local]:
  !h n. 2 ** h < n /\ n < 2 ** SUC h ==> BIT h (n - 1)
Proof
  rpt strip_tac >>
  `0 < 2 ** h` by simp[] >>
  `1 <= 2 ** h` by simp[] >>
  `1 < n` by
    (imp_res_tac arithmeticTheory.LESS_EQ_LESS_TRANS >> fs[]) >>
  `n - 1 <> 0` by simp[] >>
  `LOG2 (n - 1) = h` suffices_by metis_tac[bitTheory.BIT_LOG2] >>
  irule bitTheory.LOG2_UNIQUE >>
  conj_tac >| [
    `0 < 2 ** h` by simp[] >> decide_tac,
    fs[arithmeticTheory.EXP] >>
    `0 < 2 ** h` by simp[] >> decide_tac
  ]
QED

val log2_w2n_lt_256 = SIMP_RULE (srw_ss()) []
  (INST_TYPE [alpha |-> ``:256``] wordsTheory.LOG2_w2n_lt);

(* is_power_of_two_exp imported from passSharedPow2Theory — proved there
   to avoid ** overloading issues from integerTheory ancestors. *)

(* Power-of-two reductions using explicit k. The bridge above
   connects is_power_of_two w to the k precondition. *)
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

(* ===== Comparator boundary rules ===== *)

(* GT x MAX = 0: nothing is greater than MAX_UINT256 *)
Theorem ao_rule_gt_max:
  !inst op out s.
    inst.inst_opcode = GT /\
    inst.inst_operands = [op; Lit (0w - 1w)] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[bool_to_word_def] >>
  `~(w2n x > w2n (0w - 1w : bytes32))` by (
    `w2n x < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
    `w2n (0w - 1w : bytes32) = dimword(:256) - 1` by
      simp[wordsTheory.word_sub_def, wordsTheory.word_2comp_def,
           wordsTheory.w2n_n2w] >>
    decide_tac) >>
  gvs[bool_to_word_def]
QED

(* LT x 0 = 0: nothing is less than 0 (unsigned) *)
Theorem ao_rule_lt_zero:
  !inst op out s.
    inst.inst_opcode = LT /\
    inst.inst_operands = [op; Lit 0w] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[bool_to_word_def]
QED

(* SGT x INT256_MAX = 0: nothing is signed-greater than INT_MAX *)
Theorem ao_rule_sgt_max:
  !inst op out s.
    inst.inst_opcode = SGT /\
    inst.inst_operands = [op; Lit (i2w INT256_MAX)] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[bool_to_word_def] >>
  simp[wordsTheory.WORD_GREATER, integer_wordTheory.WORD_LTi] >>
  `w2i (i2w INT256_MAX : bytes32) = INT256_MAX` by (
    irule integer_wordTheory.w2i_i2w >>
    simp[INT256_MAX_def, integer_wordTheory.INT_MAX_def,
         integer_wordTheory.INT_MIN_def, wordsTheory.dimword_def]) >>
  pop_assum SUBST_ALL_TAC >>
  `w2i x <= INT_MAX(:256)` by simp[integer_wordTheory.w2i_le] >>
  `INT256_MAX = INT_MAX(:256)` by simp[INT256_MAX_def] >>
  `~(INT256_MAX < w2i x)` by intLib.ARITH_TAC >>
  simp[bool_to_word_def]
QED

(* SLT x INT256_MIN = 0: nothing is signed-less than INT_MIN *)
Theorem ao_rule_slt_min:
  !inst op out s.
    inst.inst_opcode = SLT /\
    inst.inst_operands = [op; Lit (i2w INT256_MIN)] /\
    inst.inst_outputs = [out] /\
    IS_SOME (eval_operand op s) ==>
    step_inst_base
      (inst with <| inst_opcode := ASSIGN; inst_operands := [Lit 0w] |>) s =
    step_inst_base inst s
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  simp[bool_to_word_def, integer_wordTheory.WORD_LTi] >>
  `w2i (i2w INT256_MIN : bytes32) = INT256_MIN` by (
    irule integer_wordTheory.w2i_i2w >>
    simp[INT256_MIN_def, integer_wordTheory.INT_MAX_def,
         integer_wordTheory.INT_MIN_def, wordsTheory.dimword_def]) >>
  pop_assum SUBST_ALL_TAC >>
  `INT_MIN(:256) <= w2i x` by simp[integer_wordTheory.w2i_ge] >>
  `INT256_MIN = INT_MIN(:256)` by simp[INT256_MIN_def] >>
  `~(w2i x < INT256_MIN)` by intLib.ARITH_TAC >>
  simp[bool_to_word_def]
QED

val _ = export_theory();
