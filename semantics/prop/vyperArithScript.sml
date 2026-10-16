(*
 * vyperArithScript.sml
 *
 * General integer/word arithmetic lemmas for Vyper proofs.
 * Bridges Vyper's within_int_bound with HOL4 word representations.
 *
 * TOP-LEVEL:
 *   lt_dimword_256           - k < 2^n ∧ n ≤ 256 ⇒ k < dimword(:256)
 *   Num_int_lt               - integer < implies Num < for non-negative
 *   within_int_bound_in_word_range - Signed n bounds fit 256-bit word range
 *   within_int_bound_rem     - remainder preserves within_int_bound
 *)

Theory vyperArith
Ancestors
  vyperValue vfmConstants arithmetic words integer
Libs
  intLib wordsLib

(* ===== Basic bound lemmas ===== *)

Theorem lt_dimword_256:
  ∀n k. k < 2 ** n ∧ n ≤ 256 ⇒ k < dimword (:256)
Proof
  rpt strip_tac
  \\ irule arithmeticTheory.LESS_LESS_EQ_TRANS
  \\ qexists_tac `2 ** n`
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ REWRITE_TAC [dimword_def]
  \\ irule bitTheory.TWOEXP_MONO2
  \\ simp[EVAL ``dimindex(:256)``]
QED

Theorem word_size_le:
  0 < n ==> word_size n ≤ n
Proof
  strip_tac >>
  simp[vfmConstantsTheory.word_size_def] >>
  `n + 31 ≤ 32 * n` by simp[] >>
  `(n + 31) DIV 32 ≤ (32 * n) DIV 32` by
    (irule DIV_LE_MONOTONE >> simp[]) >>
  `(32 * n) DIV 32 = n` by simp[MULT_TO_DIV] >>
  gvs[]
QED

Theorem word_size_not_lt_self:
  0 < n ∧ ¬(word_size n < n) ==> n = 1
Proof
  rw[vfmConstantsTheory.word_size_def] >>
  Cases_on `n` >> gvs[] >>
  Cases_on `n'` >> gvs[arithmeticTheory.DIV_LT_X] >>
  decide_tac
QED

Theorem Num_int_lt:
  ∀a b. 0 ≤ a ∧ a < b ⇒ Num a < Num b
Proof
  rpt strip_tac
  \\ `∃m. a = &m` by (qexists_tac `Num a` \\ simp[integerTheory.INT_OF_NUM])
  \\ `∃k. b = &k` by
       (qexists_tac `Num b` \\ simp[integerTheory.INT_OF_NUM]
        \\ irule integerTheory.INT_LE_TRANS
        \\ qexists_tac `a` \\ simp[integerTheory.INT_LT_IMP_LE])
  \\ gvs[integerTheory.INT_LT, integerTheory.NUM_OF_INT]
QED

(* Helper: establish the symbolic power bound before numeral normalization. *)
Theorem pow2_pred_le_int_min_256:
  n ≤ 256 ⇒ 2 ** (n − 1) ≤ words$INT_MIN (:256)
Proof
  strip_tac
  \\ REWRITE_TAC [wordsTheory.INT_MIN_def]
  \\ irule bitTheory.TWOEXP_MONO2
  \\ simp[EVAL ``dimindex(:256)``]
QED

(* ===== Signed word round-trip ===== *)

Theorem w2i_i2w_within_signed:
  ∀x n.
    within_int_bound (Signed n) x ∧ n ≤ 256 ⇒
    w2i ((i2w x):bytes32) = x
Proof
  rpt strip_tac >>
  `2 ** (n − 1) ≤ words$INT_MIN (:256)` by
    (irule pow2_pred_le_int_min_256 >> first_assum ACCEPT_TAC) >>
  (* Keep the bound outside gvs, which otherwise simplifies it away. *)
  qpat_x_assum `2 ** (n − 1) ≤ words$INT_MIN (:256)` (fn bound =>
  gvs[within_int_bound_def] >>
  Cases_on`n = 0` >> gvs[] >- EVAL_TAC >>
  Cases_on `0 ≤ x` >> gvs[] >- (
    `¬(x < 0)` by intLib.ARITH_TAC >> gvs[] >>
    `x = &Num x` by simp[Once $ GSYM INT_OF_NUM] >>
    pop_assum SUBST_ALL_TAC >>
    fs[integerTheory.NUM_OF_INT] >>
    irule integer_wordTheory.w2i_i2w_pos >>
    `Num x < 2 ** 255` by (
      irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `2 ** (n - 1)` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule bitTheory.TWOEXP_MONO2 >> simp[]) >>
    `words$INT_MAX (:256) = 2 ** 255 - 1` by
      simp[wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
           EVAL ``dimindex(:256)``] >>
    pop_assum SUBST_ALL_TAC >>
    simp[arithmeticTheory.SUB_LESS_OR]
  ) >> (
    `x < 0` by intLib.ARITH_TAC >> gvs[] >>
    `0 ≤ -x` by intLib.ARITH_TAC >>
    `-x = &Num (-x)` by simp[Once $ GSYM INT_OF_NUM] >>
    `x = -&Num (-x)` by intLib.ARITH_TAC >>
    pop_assum SUBST_ALL_TAC >>
    irule integer_wordTheory.w2i_i2w_neg >>
    fs[integerTheory.NUM_OF_INT] >>
    irule arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `2 ** (n - 1)` >>
    conj_tac >- first_assum ACCEPT_TAC >>
    ACCEPT_TAC (CONV_RULE (RAND_CONV EVAL) bound)
  ))
QED

(* ===== Signed word range ===== *)

Theorem within_int_bound_in_word_range:
  ∀n i. within_int_bound (Signed n) i ∧ n ≤ 256 ⇒
    INT_MIN (:256) ≤ i ∧ i ≤ INT_MAX (:256)
Proof
  rpt gen_tac \\ strip_tac
  \\ drule_all w2i_i2w_within_signed
  \\ disch_then (fn roundtrip =>
       ACCEPT_TAC (PURE_REWRITE_RULE [roundtrip]
         (CONJ (ISPEC ``(i2w i):bytes32`` integer_wordTheory.w2i_ge)
               (ISPEC ``(i2w i):bytes32`` integer_wordTheory.w2i_le))))
QED

(* ===== Bound preservation ===== *)

Theorem within_int_bound_rem:
  ∀x y u.
    within_int_bound u x ∧ within_int_bound u y ∧ y ≠ 0 ⇒
    within_int_bound u (x rem y)
Proof
  rpt strip_tac
  \\ Cases_on `u`
  \\ gvs[within_int_bound_def]
  >- ( (* Signed *)
    `y ≠ 0` by simp[]
    \\ drule integerTheory.INT_REMQUOT
    \\ disch_then (qspec_then `x` strip_assume_tac)
    \\ `0 ≤ ABS (x rem y)` by intLib.ARITH_TAC
    \\ `Num (ABS (x rem y)) < Num (ABS y)` by
         (irule Num_int_lt \\ intLib.ARITH_TAC)
    \\ `Num (ABS y) ≤ 2 ** (n − 1)` by
         (Cases_on `y < 0` \\ gvs[integerTheory.INT_ABS]
          \\ simp[arithmeticTheory.LESS_IMP_LESS_OR_EQ])
    \\ Cases_on `x rem y < 0` \\ simp[]
    \\ gvs[integerTheory.INT_ABS]
    \\ irule arithmeticTheory.LESS_IMP_LESS_OR_EQ
    \\ irule arithmeticTheory.LESS_LESS_EQ_TRANS
    \\ metis_tac[]
  )
  >> ( (* Unsigned *)
    `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM]
    \\ `y = &Num y` by simp[Once $ GSYM integerTheory.INT_OF_NUM]
    \\ `0 < Num y` by (CCONTR_TAC >> fs[])
    \\ pop_assum mp_tac
    \\ ntac 2 (pop_assum SUBST_ALL_TAC)
    \\ strip_tac
    \\ fs[integerTheory.NUM_OF_INT, integerTheory.INT_REM]
    \\ `Num x MOD Num y < Num y` by simp[]
    \\ irule arithmeticTheory.LESS_TRANS
    \\ qexists_tac `Num y` \\ simp[]
  )
QED
