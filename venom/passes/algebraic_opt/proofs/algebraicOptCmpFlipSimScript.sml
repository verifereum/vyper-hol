(*
 * Algebraic Optimization — CMP Flip Block Simulation
 *
 * Proves semantic equivalence for the comparator flip mini-pass
 * (ao_cmp_flip_function). The flip changes a comparator + iszero/assert
 * pair into a flipped comparator + assign/iszero-insert.
 *
 * TOP-LEVEL:
 *   ao_cmp_flip_null_sim        — NULL flips case: function unchanged → trivial
 *   ao_cmp_flip_function_labels — label preservation
 *   cmp_flip_sgt_slt            — signed GT→LT flip identity
 *   cmp_flip_slt_sgt            — signed LT→GT flip identity
 *   ao_cmp_flip_pair_equiv      — flip+remove pair produces same final value
 *)

Theory algebraicOptCmpFlipSim
Ancestors
  algebraicOptDefs algebraicOptResolveSim
  passSharedDefs passSimulationProps valueRangeDefs
  venomExecSemantics venomState venomInst stateEquiv
Libs
  pairLib BasicProvers intLib

(* ===== NULL flips: function unchanged ===== *)

(* When ao_cmp_flip_scan produces no flips, function is unchanged *)
Theorem ao_cmp_flip_null_sim:
  !dfg fn.
    NULL (FST (ao_cmp_flip_scan dfg (fn_insts fn))) ==>
    ao_cmp_flip_function dfg fn = fn
Proof
  rpt strip_tac >>
  simp[ao_cmp_flip_function_def, LET_THM] >>
  Cases_on `ao_cmp_flip_scan dfg (fn_insts fn)` >>
  Cases_on `r` >> gvs[]
QED

(* ===== Label preservation ===== *)

Theorem ao_cmp_flip_function_labels:
  !dfg fn lbl.
    IS_SOME (lookup_block lbl (ao_cmp_flip_function dfg fn).fn_blocks) <=>
    IS_SOME (lookup_block lbl fn.fn_blocks)
Proof
  rpt gen_tac >>
  simp[ao_cmp_flip_function_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> simp[] >>
  simp[lookup_block_map] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >> simp[]
QED

(* ===== Signed comparison flip semantics ===== *)

(* Helper: bool_to_word equivalences *)
Triviality btw_0[local]:
  !b. (bool_to_word b = 0w) <=> ~b
Proof Cases >> simp[bool_to_word_def]
QED

Triviality btw_1[local]:
  !b. (bool_to_word b = 1w) <=> b
Proof Cases >> simp[bool_to_word_def]
QED

(* word_gt x y = w2i x > w2i y (signed greater-than) *)
(* word_lt x y = w2i x < w2i y (signed less-than) *)

(* Helper: w + 1w = i2w(w2i w + 1) *)
Triviality word_add_1_i2w[local]:
  !w : bytes32. w + 1w = i2w (w2i w + 1)
Proof
  gen_tac >>
  CONV_TAC (LHS_CONV (RATOR_CONV (RAND_CONV
    (ONCE_REWRITE_CONV [GSYM integer_wordTheory.i2w_w2i])))) >>
  CONV_TAC (LHS_CONV (RAND_CONV
    (ONCE_REWRITE_CONV [GSYM (EVAL ``i2w 1 : bytes32``)]))) >>
  rewrite_tac[integer_wordTheory.word_i2w_add]
QED

(* Helper: w - 1w = i2w(w2i w - 1) *)
Triviality word_sub_1_i2w[local]:
  !w : bytes32. w - 1w = i2w (w2i w - 1)
Proof
  gen_tac >>
  rewrite_tac[wordsTheory.word_sub_def] >>
  CONV_TAC (LHS_CONV (RATOR_CONV (RAND_CONV
    (ONCE_REWRITE_CONV [GSYM integer_wordTheory.i2w_w2i])))) >>
  CONV_TAC (LHS_CONV (RAND_CONV
    (ONCE_REWRITE_CONV [GSYM (EVAL ``i2w (-1) : bytes32``)]))) >>
  rewrite_tac[integer_wordTheory.word_i2w_add] >>
  AP_TERM_TAC >> intLib.ARITH_TAC
QED

(* Helper: w2i (w + 1w) = w2i w + 1 when w2i w < INT_MAX *)
Triviality w2i_add_1[local]:
  !w : bytes32.
    w2i w < INT_MAX (:256) ==>
    w2i (w + 1w) = w2i w + 1
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[word_add_1_i2w] >>
  irule integer_wordTheory.w2i_i2w >>
  mp_tac (SPEC ``w:bytes32``
    (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_ge)) >>
  strip_tac >> conj_tac >> intLib.ARITH_TAC
QED

(* Helper: w2i (w - 1w) = w2i w - 1 when INT_MIN < w2i w *)
Triviality w2i_sub_1[local]:
  !w : bytes32.
    INT_MIN (:256) < w2i w ==>
    w2i (w - 1w) = w2i w - 1
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[word_sub_1_i2w] >>
  irule integer_wordTheory.w2i_i2w >>
  mp_tac (SPEC ``w:bytes32``
    (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_le)) >>
  strip_tac >> conj_tac >> intLib.ARITH_TAC
QED

(* Helper: w2i w = c => w = i2w c *)
Triviality w2i_inj_i2w[local]:
  !w : bytes32 c. w2i w = c ==> w = i2w c
Proof
  rpt strip_tac >>
  `w = i2w (w2i w)` by simp[integer_wordTheory.i2w_w2i] >>
  gvs[]
QED

(* For signed GT → SLT flip: iszero(sgt(x, w)) = slt(x, w+1)
   when w < INT256_MAX (i.e. w+1 doesn't overflow signed) *)
Theorem cmp_flip_sgt_slt:
  !x w : bytes32.
    w <> i2w INT256_MAX ==>
    (bool_to_word (word_gt x w) = 0w) =
    (bool_to_word (word_lt x (w + 1w)) = 1w)
Proof
  rpt strip_tac >> simp[btw_0, btw_1] >>
  simp[wordsTheory.WORD_GREATER] >>
  simp[integer_wordTheory.WORD_LTi] >>
  `w2i w < INT_MAX (:256)` by (
    spose_not_then strip_assume_tac >>
    `w2i w = INT_MAX (:256)` by (
      mp_tac (SPEC ``w:bytes32``
        (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_le)) >>
      intLib.ARITH_TAC) >>
    imp_res_tac w2i_inj_i2w >>
    `INT256_MAX = INT_MAX (:256)` by simp[INT256_MAX_def] >>
    gvs[]) >>
  `w2i (w + 1w) = w2i w + 1` by (irule w2i_add_1 >> simp[]) >>
  simp[] >> intLib.ARITH_TAC
QED

(* For signed LT → SGT flip: iszero(slt(x, w)) = sgt(x, w-1)
   when w > INT256_MIN (i.e. w-1 doesn't underflow signed) *)
Theorem cmp_flip_slt_sgt:
  !x w : bytes32.
    w <> i2w INT256_MIN ==>
    (bool_to_word (word_lt x w) = 0w) =
    (bool_to_word (word_gt x (w - 1w)) = 1w)
Proof
  rpt strip_tac >> simp[btw_0, btw_1] >>
  simp[wordsTheory.WORD_GREATER] >>
  simp[integer_wordTheory.WORD_LTi] >>
  `INT_MIN (:256) < w2i w` by (
    spose_not_then strip_assume_tac >>
    `w2i w = INT_MIN (:256)` by (
      mp_tac (SPEC ``w:bytes32``
        (INST_TYPE [alpha |-> ``:256``] integer_wordTheory.w2i_ge)) >>
      intLib.ARITH_TAC) >>
    imp_res_tac w2i_inj_i2w >>
    `INT256_MIN = INT_MIN (:256)` by simp[INT256_MIN_def] >>
    gvs[]) >>
  `w2i (w - 1w) = w2i w - 1` by (irule w2i_sub_1 >> simp[]) >>
  simp[] >> intLib.ARITH_TAC
QED

(* ===== Flip+Remove pair semantic equivalence ===== *)

(* The core insight: executing a comparator followed by ISZERO on the result
   gives the same final output as executing the flipped comparator followed
   by ASSIGN on the result.

   Original:    CMP(x, w) → out_var,  ISZERO(out_var) → iz_out
   Transformed: FLIP_CMP(x, w') → out_var,  ASSIGN(out_var) → iz_out

   iz_out gets the same value in both cases. out_var differs but is dead
   (single-use, consumed by the iszero/assign).

   The guard w <> never ensures the flip doesn't overflow. *)

(* Combined: iszero(cmp(x,w)) = flip_cmp(x,w') for each comparator *)
Theorem cmp_flip_iszero_equiv_gt:
  !x w : bytes32.
    w <> 0w - 1w ==>
    bool_to_word (bool_to_word (w2n x > w2n w) = 0w) =
    bool_to_word (w2n x < w2n (w + 1w))
Proof
  rpt strip_tac >>
  qspecl_then [`x`, `w`] mp_tac cmp_flip_gt_lt >>
  simp[] >> strip_tac >>
  Cases_on `w2n x > w2n w` >> simp[bool_to_word_def] >>
  Cases_on `w2n x < w2n (w + 1w)` >> gvs[bool_to_word_def]
QED

Theorem cmp_flip_iszero_equiv_lt:
  !x w : bytes32.
    w <> 0w ==>
    bool_to_word (bool_to_word (w2n x < w2n w) = 0w) =
    bool_to_word (w2n x > w2n (w - 1w))
Proof
  rpt strip_tac >>
  qspecl_then [`x`, `w`] mp_tac cmp_flip_lt_gt >>
  simp[] >> strip_tac >>
  Cases_on `w2n x < w2n w` >> simp[bool_to_word_def] >>
  Cases_on `w2n x > w2n (w - 1w)` >> gvs[bool_to_word_def]
QED

Theorem cmp_flip_iszero_equiv_sgt:
  !x w : bytes32.
    w <> i2w INT256_MAX ==>
    bool_to_word (bool_to_word (word_gt x w) = 0w) =
    bool_to_word (word_lt x (w + 1w))
Proof
  rpt strip_tac >>
  qspecl_then [`x`, `w`] mp_tac cmp_flip_sgt_slt >>
  simp[] >> strip_tac >>
  Cases_on `word_gt x w` >> simp[bool_to_word_def] >>
  Cases_on `word_lt x (w + 1w)` >> gvs[bool_to_word_def]
QED

Theorem cmp_flip_iszero_equiv_slt:
  !x w : bytes32.
    w <> i2w INT256_MIN ==>
    bool_to_word (bool_to_word (word_lt x w) = 0w) =
    bool_to_word (word_gt x (w - 1w))
Proof
  rpt strip_tac >>
  qspecl_then [`x`, `w`] mp_tac cmp_flip_slt_sgt >>
  simp[] >> strip_tac >>
  Cases_on `word_lt x w` >> simp[bool_to_word_def] >>
  Cases_on `word_gt x (w - 1w)` >> gvs[bool_to_word_def]
QED

(* ===== Flip+Remove step_inst_base equivalence ===== *)

(* For the remove case: executing the flipped comparator gives the
   negation of the original. The subsequent ASSIGN passes through
   the flipped value, which equals iszero(original_value). *)

(* GT case: step_inst_base of flipped LT gives iszero of original GT result *)
Theorem flip_remove_gt_step:
  !inst op1 w out s v1.
    inst.inst_opcode = GT /\
    inst.inst_operands = [op1; Lit w] /\
    inst.inst_outputs = [out] /\
    eval_operand op1 s = SOME v1 /\
    w <> 0w - 1w ==>
    step_inst_base
      (inst with <| inst_opcode := LT;
                    inst_operands := [op1; Lit (w + 1w)] |>) s =
    OK (update_var out (bool_to_word (bool_to_word (w2n v1 > w2n w) = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  simp[cmp_flip_iszero_equiv_gt]
QED

(* LT case *)
Theorem flip_remove_lt_step:
  !inst op1 w out s v1.
    inst.inst_opcode = LT /\
    inst.inst_operands = [op1; Lit w] /\
    inst.inst_outputs = [out] /\
    eval_operand op1 s = SOME v1 /\
    w <> 0w ==>
    step_inst_base
      (inst with <| inst_opcode := GT;
                    inst_operands := [op1; Lit (w - 1w)] |>) s =
    OK (update_var out (bool_to_word (bool_to_word (w2n v1 < w2n w) = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  simp[cmp_flip_iszero_equiv_lt]
QED

(* SGT case *)
Theorem flip_remove_sgt_step:
  !inst op1 w out s v1.
    inst.inst_opcode = SGT /\
    inst.inst_operands = [op1; Lit w] /\
    inst.inst_outputs = [out] /\
    eval_operand op1 s = SOME v1 /\
    w <> i2w INT256_MAX ==>
    step_inst_base
      (inst with <| inst_opcode := SLT;
                    inst_operands := [op1; Lit (w + 1w)] |>) s =
    OK (update_var out (bool_to_word (bool_to_word (word_gt v1 w) = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  simp[cmp_flip_iszero_equiv_sgt]
QED

(* SLT case *)
Theorem flip_remove_slt_step:
  !inst op1 w out s v1.
    inst.inst_opcode = SLT /\
    inst.inst_operands = [op1; Lit w] /\
    inst.inst_outputs = [out] /\
    eval_operand op1 s = SOME v1 /\
    w <> i2w INT256_MIN ==>
    step_inst_base
      (inst with <| inst_opcode := SGT;
                    inst_operands := [op1; Lit (w - 1w)] |>) s =
    OK (update_var out (bool_to_word (bool_to_word (word_lt v1 w) = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  simp[cmp_flip_iszero_equiv_slt]
QED

val _ = export_theory();
