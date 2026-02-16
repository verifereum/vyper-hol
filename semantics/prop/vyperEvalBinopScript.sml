Theory vyperEvalBinop

Ancestors
  vyperInterpreter

Libs
  intLib wordsLib

val within_int_bound_def = vyperTypeValueTheory.within_int_bound_def;
val evaluate_binop_def = vyperInterpreterTheory.evaluate_binop_def;
val bounded_int_op_def = vyperInterpreterTheory.bounded_int_op_def;
val INT_OF_NUM = integerTheory.INT_OF_NUM;
val INT_REM = integerTheory.INT_REM;
val INT_DIV = integerTheory.INT_DIV;
val NUM_OF_INT = integerTheory.NUM_OF_INT;

(* ===== Unsigned helpers ===== *)

(* Shared tactic: prove k < 2^256 from k < 2^n and n <= 256 *)
val lt_2_256_tac =
  `2 ** 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936`
    by EVAL_TAC >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** n` >>
  simp[] >> irule bitTheory.TWOEXP_MONO2 >> simp[];

(* Shared tactic: prove Num v < dimword(:256) from Num v < 2^n and n <= 256 *)
val lt_dimword_tac =
  simp[wordsTheory.dimword_def, EVAL ``dimindex(:256)``] >> lt_2_256_tac;

(* Helper: w2n of word_mod on unsigned values equals integer rem *)
Theorem w2n_word_mod_unsigned:
  ∀x y n.
    0 ≤ x ∧ Num x < 2 ** n ∧ 0 ≤ y ∧ Num y < 2 ** n ∧ y ≠ 0 ∧ n ≤ 256 ⇒
    &(w2n (word_mod ((i2w x):bytes32) (i2w y))) = x rem y
Proof
  rpt strip_tac >>
  `x = &Num x` by simp[Once $ GSYM INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[NUM_OF_INT] >>
  `Num x < dimword (:256)` by lt_dimword_tac >>
  `Num y < dimword (:256)` by lt_dimword_tac >>
  simp[wordsTheory.word_mod_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w] >>
  `Num x MOD Num y < Num y` by simp[] >>
  `Num x MOD Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_TRANS >> qexists_tac `Num y` >> simp[]) >>
  simp[INT_REM] >> lt_2_256_tac
QED

(* Helper: w2n of word_div on unsigned values equals integer div *)
Theorem w2n_word_div_unsigned:
  ∀x y n.
    0 ≤ x ∧ Num x < 2 ** n ∧ 0 ≤ y ∧ Num y < 2 ** n ∧ y ≠ 0 ∧ n ≤ 256 ⇒
    &(w2n (word_div ((i2w x):bytes32) (i2w y))) = x / y
Proof
  rpt strip_tac >>
  `x = &Num x` by simp[Once $ GSYM INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[NUM_OF_INT] >>
  `Num y ≠ 0` by simp[] >>
  `Num x < dimword (:256)` by lt_dimword_tac >>
  `Num y < dimword (:256)` by lt_dimword_tac >>
  `Num x DIV Num y ≤ Num x` by simp[arithmeticTheory.DIV_LESS_EQ] >>
  `Num x DIV Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
    qexists_tac `Num x` >> simp[]) >>
  simp[wordsTheory.word_div_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w, INT_DIV] >> lt_2_256_tac
QED

(* ===== Unsigned Mod ===== *)

Theorem evaluate_binop_mod_unsigned:
  ∀x y n.
    within_int_bound (Unsigned n) x ∧ within_int_bound (Unsigned n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop Mod (IntV (Unsigned n) x) (IntV (Unsigned n) y) =
    INL (IntV (Unsigned n) (x rem y))
Proof
  rpt strip_tac >>
  gvs[within_int_bound_def] >>
  simp[evaluate_binop_def, bounded_int_op_def, within_int_bound_def] >>
  `x = &Num x` by simp[Once $ GSYM INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[NUM_OF_INT] >>
  `Num y ≠ 0` by simp[] >>
  `Num x < dimword (:256)` by lt_dimword_tac >>
  `Num y < dimword (:256)` by lt_dimword_tac >>
  simp[wordsTheory.word_mod_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w] >>
  `Num x MOD Num y < Num y` by simp[] >>
  `Num x MOD Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_TRANS >> qexists_tac `Num y` >> simp[]) >>
  conj_tac >- (
    irule arithmeticTheory.LESS_TRANS >> qexists_tac `Num y` >> fs[NUM_OF_INT]
  ) >>
  simp[INT_REM] >> lt_2_256_tac
QED

(* ===== Unsigned Div ===== *)

Theorem evaluate_binop_div_unsigned:
  ∀x y n.
    within_int_bound (Unsigned n) x ∧ within_int_bound (Unsigned n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop Div (IntV (Unsigned n) x) (IntV (Unsigned n) y) =
    INL (IntV (Unsigned n) (x / y))
Proof
  rpt strip_tac >>
  gvs[within_int_bound_def] >>
  simp[evaluate_binop_def, bounded_int_op_def, within_int_bound_def] >>
  `x = &Num x` by simp[Once $ GSYM INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[NUM_OF_INT] >>
  `Num y ≠ 0` by simp[] >>
  `Num x < dimword (:256)` by lt_dimword_tac >>
  `Num y < dimword (:256)` by lt_dimword_tac >>
  `Num x DIV Num y ≤ Num x` by simp[arithmeticTheory.DIV_LESS_EQ] >>
  `Num x DIV Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
    qexists_tac `Num x` >> simp[]) >>
  simp[wordsTheory.word_div_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w, INT_DIV] >>
  conj_tac >- (
    irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
    qexists_tac `Num x` >> fs[NUM_OF_INT]
  ) >>
  lt_2_256_tac
QED

(* ===== Signed helpers ===== *)

(* Helper: w2i/i2w round-trip for signed values within bounds *)
Theorem w2i_i2w_within_signed:
  ∀x n.
    within_int_bound (Signed n) x ∧ n ≤ 256 ⇒
    w2i ((i2w x):bytes32) = x
Proof
  rpt strip_tac >> gvs[within_int_bound_def] >>
  Cases_on `0 ≤ x` >> gvs[] >- (
    `¬(x < 0)` by intLib.ARITH_TAC >> gvs[] >>
    `x = &Num x` by simp[Once $ GSYM INT_OF_NUM] >>
    pop_assum SUBST_ALL_TAC >>
    fs[NUM_OF_INT] >>
    irule integer_wordTheory.w2i_i2w_pos >>
    `Num x < 2 ** 255` by (
      irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `2 ** (n - 1)` >> simp[] >>
      irule bitTheory.TWOEXP_MONO2 >> simp[]) >>
    `INT_MAX (:256) = 2 ** 255 - 1` by
      simp[wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
           EVAL ``dimindex(:256)``] >>
    pop_assum SUBST_ALL_TAC >>
    `2 ** 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968`
      by EVAL_TAC >>
    simp[]
  ) >> (
    `x < 0` by intLib.ARITH_TAC >> gvs[] >>
    `0 ≤ -x` by intLib.ARITH_TAC >>
    `-x = &Num (-x)` by simp[Once $ GSYM INT_OF_NUM] >>
    `x = -&Num (-x)` by intLib.ARITH_TAC >>
    pop_assum SUBST_ALL_TAC >>
    irule integer_wordTheory.w2i_i2w_neg >>
    fs[NUM_OF_INT] >>
    irule arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `2 ** (n - 1)` >> simp[] >>
    irule arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `2 ** 255` >>
    `2 ** 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968`
      by EVAL_TAC >>
    simp[] >>
    irule bitTheory.TWOEXP_MONO2 >> simp[]
  )
QED

(* Helper: integer < implies Num < for non-negative values *)
Theorem Num_int_lt:
  ∀a b. 0 ≤ a ∧ a < b ⇒ Num a < Num b
Proof
  rpt strip_tac >>
  `0 ≤ b` by intLib.ARITH_TAC >>
  `&Num a = a` by simp[integerTheory.INT_OF_NUM] >>
  `&Num b = b` by simp[integerTheory.INT_OF_NUM] >>
  `&Num a < &Num b` by intLib.ARITH_TAC >>
  fs[integerTheory.INT_LT]
QED

(* Helper: remainder preserves signed bounds *)
Theorem within_int_bound_rem_signed:
  ∀x y n.
    within_int_bound (Signed n) y ∧ y ≠ 0 ⇒
    within_int_bound (Signed n) (x rem y)
Proof
  rpt strip_tac >>
  gvs[within_int_bound_def] >>
  `y ≠ 0` by simp[] >>
  drule integerTheory.INT_REMQUOT >>
  disch_then (qspec_then `x` strip_assume_tac) >>
  `0 ≤ ABS (x rem y)` by intLib.ARITH_TAC >>
  `Num (ABS (x rem y)) < Num (ABS y)` by
    (irule Num_int_lt >> intLib.ARITH_TAC) >>
  `Num (ABS y) ≤ 2 ** (n − 1)` by (
    Cases_on `y < 0` >> gvs[integerTheory.INT_ABS] >>
    simp[arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  Cases_on `x rem y < 0` >> simp[] >>
  gvs[integerTheory.INT_ABS] >>
  irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  metis_tac[]
QED

(* ===== Signed Mod ===== *)

Theorem evaluate_binop_mod_signed:
  ∀x y n.
    within_int_bound (Signed n) x ∧ within_int_bound (Signed n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop Mod (IntV (Signed n) x) (IntV (Signed n) y) =
    INL (IntV (Signed n) (x rem y))
Proof
  rpt strip_tac >>
  simp[evaluate_binop_def, bounded_int_op_def] >>
  `w2i ((i2w x):bytes32) = x` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `w2i ((i2w y):bytes32) = y` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `(i2w y):bytes32 ≠ 0w` by (
    CCONTR_TAC >> fs[] >> fs[integer_wordTheory.word_0_w2i]) >>
  drule integer_wordTheory.word_rem >>
  disch_then (qspecl_then [`(i2w x):bytes32`] mp_tac) >>
  strip_tac >> gvs[] >>
  `within_int_bound (Signed n) (x rem y)` by
    (irule within_int_bound_rem_signed >> metis_tac[]) >>
  `w2i ((i2w (x rem y)):bytes32) = x rem y` by
    (irule w2i_i2w_within_signed >> metis_tac[]) >>
  simp[]
QED

(* ===== Unified Mod theorem ===== *)

Theorem evaluate_binop_mod:
  ∀x y b.
    within_int_bound b x ∧ within_int_bound b y ∧ y ≠ 0 ∧
    (case b of Unsigned n => n ≤ 256 | Signed n => n ≤ 256) ⇒
    evaluate_binop Mod (IntV b x) (IntV b y) =
    INL (IntV b (x rem y))
Proof
  rpt strip_tac >> Cases_on `b` >> gvs[] >>
  metis_tac[evaluate_binop_mod_unsigned, evaluate_binop_mod_signed]
QED
