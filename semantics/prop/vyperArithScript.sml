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
  vyperValue
Libs
  intLib wordsLib wordsTheory integerTheory

(* ===== Basic bound lemmas ===== *)

Theorem lt_dimword_256:
  ∀n k. k < 2 ** n ∧ n ≤ 256 ⇒ k < dimword (:256)
Proof
  simp[dimword_def, EVAL ``dimindex(:256)``]
  \\ rpt strip_tac
  \\ irule arithmeticTheory.LESS_LESS_EQ_TRANS
  \\ qexists_tac `2 ** n` \\ simp[bitTheory.TWOEXP_MONO2]
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

(* ===== Signed word round-trip ===== *)

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
    fs[integerTheory.NUM_OF_INT] >>
    irule integer_wordTheory.w2i_i2w_pos >>
    `Num x < 2 ** 255` by (
      irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
      qexists_tac `2 ** (n - 1)` >> simp[] >>
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
    qexists_tac `2 ** (n - 1)` >> simp[] >>
    simp[wordsTheory.INT_MIN_def, EVAL ``dimindex(:256)``,
         bitTheory.TWOEXP_MONO2]
  )
QED

(* ===== Signed word range ===== *)

Theorem within_int_bound_in_word_range:
  ∀n i. within_int_bound (Signed n) i ∧ n ≤ 256 ⇒
    INT_MIN (:256) ≤ i ∧ i ≤ INT_MAX (:256)
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs[within_int_bound_def, LET_THM]
  \\ `2 ** (n − 1) ≤ words$INT_MIN (:256)` by
       simp[wordsTheory.INT_MIN_def, arithmeticTheory.EXP_BASE_LE_MONO]
  \\ Cases_on `i < 0` \\ gvs[]
  >- (* i < 0 *)
     (`Num (-i) ≤ words$INT_MIN (:256)` by
        (irule arithmeticTheory.LESS_EQ_TRANS
         \\ qexists_tac `2 ** (n − 1)` \\ simp[])
      \\ `0 ≤ -i` by simp[]
      \\ `-i = &(Num (-i))` by fs[INT_OF_NUM]
      \\ `i = -&(Num (-i))` by
           (qpat_x_assum `-i = _` (SUBST1_TAC o SYM)
            \\ simp[integerTheory.INT_NEG_NEG])
      \\ pop_assum SUBST_ALL_TAC
      \\ gvs[integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def,
             INT_LE_NEG, INT_OF_NUM_LE, wordsTheory.INT_MIN_def])
  (* i ≥ 0 *)
  \\ `Num i < words$INT_MIN (:256)` by
       (irule arithmeticTheory.LESS_LESS_EQ_TRANS
        \\ qexists_tac `2 ** (n − 1)` \\ simp[])
  \\ `0 ≤ i` by fs[integerTheory.INT_NOT_LT]
  \\ `i = &(Num i)` by fs[INT_OF_NUM]
  \\ conj_tac
  >- (simp[integer_wordTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def]
      \\ qpat_x_assum `i = _` SUBST1_TAC
      \\ simp[INT_OF_NUM_LE])
  \\ qpat_x_assum `i = _` SUBST1_TAC
  \\ irule INT_LE_TRANS
  \\ qexists_tac `&(words$INT_MIN (:256) - 1)`
  \\ conj_tac
  >- simp[INT_OF_NUM_LE, arithmeticTheory.SUB_LESS_OR]
  \\ `1 ≤ words$INT_MIN (:256)` by simp[wordsTheory.INT_MIN_def]
  \\ simp[integer_wordTheory.INT_MAX_def, GSYM INT_SUB]
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
