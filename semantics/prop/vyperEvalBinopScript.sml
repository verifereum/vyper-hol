Theory vyperEvalBinop

Ancestors
  vyperInterpreter

Libs
  intLib wordsLib

(* ===== Helpers ===== *)

(* Tactic: prove k < 2^256 from k < 2^n and n <= 256 *)
val lt_2_256_tac =
  `2 ** 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936`
    by EVAL_TAC >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** n` >>
  simp[] >> irule bitTheory.TWOEXP_MONO2 >> simp[];

(* Tactic: prove Num v < dimword(:256) from Num v < 2^n and n <= 256 *)
val lt_dimword_tac =
  simp[wordsTheory.dimword_def, EVAL ``dimindex(:256)``] >> lt_2_256_tac;

(* Helper: w2n of word_mod on unsigned values equals integer rem *)
Theorem w2n_word_mod_unsigned[local]:
  ∀x y n.
    0 ≤ x ∧ Num x < 2 ** n ∧ 0 ≤ y ∧ Num y < 2 ** n ∧ y ≠ 0 ∧ n ≤ 256 ⇒
    &(w2n (word_mod ((i2w x):bytes32) (i2w y))) = x rem y
Proof
  rpt strip_tac >>
  `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[integerTheory.NUM_OF_INT] >>
  `Num x < dimword (:256)` by lt_dimword_tac >>
  `Num y < dimword (:256)` by lt_dimword_tac >>
  simp[wordsTheory.word_mod_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w] >>
  `Num x MOD Num y < Num y` by simp[] >>
  `Num x MOD Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_TRANS >> qexists_tac `Num y` >> simp[]) >>
  simp[integerTheory.INT_REM] >> lt_2_256_tac
QED

(* Helper: w2n of word_div on unsigned values equals integer div *)
Theorem w2n_word_div_unsigned[local]:
  ∀x y n.
    0 ≤ x ∧ Num x < 2 ** n ∧ 0 ≤ y ∧ Num y < 2 ** n ∧ y ≠ 0 ∧ n ≤ 256 ⇒
    &(w2n (word_div ((i2w x):bytes32) (i2w y))) = x / y
Proof
  rpt strip_tac >>
  `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[integerTheory.NUM_OF_INT] >>
  `Num y ≠ 0` by simp[] >>
  `Num x < dimword (:256)` by lt_dimword_tac >>
  `Num y < dimword (:256)` by lt_dimword_tac >>
  `Num x DIV Num y ≤ Num x` by simp[arithmeticTheory.DIV_LESS_EQ] >>
  `Num x DIV Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
    qexists_tac `Num x` >> simp[]) >>
  simp[wordsTheory.word_div_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w, integerTheory.INT_DIV] >> lt_2_256_tac
QED

(* Helper: w2i/i2w round-trip for signed values within bounds *)
Theorem w2i_i2w_within_signed[local]:
  ∀x n.
    within_int_bound (Signed n) x ∧ n ≤ 256 ⇒
    w2i ((i2w x):bytes32) = x
Proof
  rpt strip_tac >> gvs[vyperValueTheory.within_int_bound_def] >>
  Cases_on `0 ≤ x` >> gvs[] >- (
    `¬(x < 0)` by intLib.ARITH_TAC >> gvs[] >>
    `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
    pop_assum SUBST_ALL_TAC >>
    fs[integerTheory.NUM_OF_INT] >>
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
    `-x = &Num (-x)` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
    `x = -&Num (-x)` by intLib.ARITH_TAC >>
    pop_assum SUBST_ALL_TAC >>
    irule integer_wordTheory.w2i_i2w_neg >>
    fs[integerTheory.NUM_OF_INT] >>
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
Theorem Num_int_lt[local]:
  ∀a b. 0 ≤ a ∧ a < b ⇒ Num a < Num b
Proof
  rpt strip_tac >>
  `0 ≤ b` by intLib.ARITH_TAC >>
  `&Num a = a` by simp[integerTheory.INT_OF_NUM] >>
  `&Num b = b` by simp[integerTheory.INT_OF_NUM] >>
  `&Num a < &Num b` by intLib.ARITH_TAC >>
  fs[integerTheory.INT_LT]
QED

(****************************************************************************)
(*                         Main theorems                                    *)
(****************************************************************************)

(* ========= Add / Sub / Mul ========== *)

Theorem evaluate_binop_add:
  ∀u x y.
    within_int_bound u (x + y) ⇒
    evaluate_binop Add (IntV u x) (IntV u y) =
    INL (IntV u (x + y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.bounded_int_op_def]
QED

Theorem evaluate_binop_sub:
  ∀u x y.
    within_int_bound u (x − y) ⇒
    evaluate_binop Sub (IntV u x) (IntV u y) =
    INL (IntV u (x − y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.bounded_int_op_def]
QED

Theorem evaluate_binop_mul:
  ∀u x y.
    within_int_bound u (x * y) ⇒
    evaluate_binop Mul (IntV u x) (IntV u y) =
    INL (IntV u (x * y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.bounded_int_op_def]
QED

(* ========= Mod / Div (Unsigned) ========== *)

Theorem evaluate_binop_mod_unsigned:
  ∀x y n.
    within_int_bound (Unsigned n) x ∧ within_int_bound (Unsigned n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop Mod (IntV (Unsigned n) x) (IntV (Unsigned n) y) =
    INL (IntV (Unsigned n) (x rem y))
Proof
  rpt strip_tac >>
  gvs[vyperValueTheory.within_int_bound_def] >>
  simp[vyperInterpreterTheory.evaluate_binop_def, vyperInterpreterTheory.bounded_int_op_def, vyperValueTheory.within_int_bound_def] >>
  `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[integerTheory.NUM_OF_INT] >>
  `Num y ≠ 0` by simp[] >>
  `Num x < dimword (:256)` by lt_dimword_tac >>
  `Num y < dimword (:256)` by lt_dimword_tac >>
  simp[wordsTheory.word_mod_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w] >>
  `Num x MOD Num y < Num y` by simp[] >>
  `Num x MOD Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_TRANS >> qexists_tac `Num y` >> simp[]) >>
  conj_tac >- (
    irule arithmeticTheory.LESS_TRANS >> qexists_tac `Num y` >> fs[integerTheory.NUM_OF_INT]
  ) >>
  simp[integerTheory.INT_REM] >> lt_2_256_tac
QED

Theorem evaluate_binop_div_unsigned:
  ∀x y n.
    within_int_bound (Unsigned n) x ∧ within_int_bound (Unsigned n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop Div (IntV (Unsigned n) x) (IntV (Unsigned n) y) =
    INL (IntV (Unsigned n) (x / y))
Proof
  rpt strip_tac >>
  gvs[vyperValueTheory.within_int_bound_def] >>
  simp[vyperInterpreterTheory.evaluate_binop_def, vyperInterpreterTheory.bounded_int_op_def, vyperValueTheory.within_int_bound_def] >>
  `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `y = &Num y` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
  `0 < Num y` by (CCONTR_TAC >> fs[]) >>
  pop_assum mp_tac >>
  ntac 2 (pop_assum SUBST_ALL_TAC) >>
  strip_tac >>
  fs[integerTheory.NUM_OF_INT] >>
  `Num y ≠ 0` by simp[] >>
  `Num x < dimword (:256)` by lt_dimword_tac >>
  `Num y < dimword (:256)` by lt_dimword_tac >>
  `Num x DIV Num y ≤ Num x` by simp[arithmeticTheory.DIV_LESS_EQ] >>
  `Num x DIV Num y < 2 ** n` by (
    irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
    qexists_tac `Num x` >> simp[]) >>
  simp[wordsTheory.word_div_def, integer_wordTheory.i2w_pos,
       wordsTheory.w2n_n2w, integerTheory.INT_DIV] >>
  conj_tac >- (
    irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
    qexists_tac `Num x` >> fs[integerTheory.NUM_OF_INT]
  ) >>
  lt_2_256_tac
QED

(* ========= within_int_bound_rem ========== *)

Theorem within_int_bound_rem:
  ∀x y u.
    within_int_bound u x ∧ within_int_bound u y ∧ y ≠ 0 ⇒
    within_int_bound u (x rem y)
Proof
  rpt strip_tac >>
  Cases_on `u` >>
  gvs[vyperValueTheory.within_int_bound_def]
  >- ( (* Signed *)
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
  )
  >> ( (* Unsigned *)
    `x = &Num x` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
    `y = &Num y` by simp[Once $ GSYM integerTheory.INT_OF_NUM] >>
    `0 < Num y` by (CCONTR_TAC >> fs[]) >>
    pop_assum mp_tac >>
    ntac 2 (pop_assum SUBST_ALL_TAC) >>
    strip_tac >>
    fs[integerTheory.NUM_OF_INT, integerTheory.INT_REM] >>
    `Num x MOD Num y < Num y` by simp[] >>
    irule arithmeticTheory.LESS_TRANS >>
    qexists_tac `Num y` >> simp[]
  )
QED

(* ========= Div / Mod (Signed) ========== *)

Theorem evaluate_binop_div_signed:
  ∀x y n.
    within_int_bound (Signed n) x ∧ within_int_bound (Signed n) y ∧
    within_int_bound (Signed n) (x quot y) ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop Div (IntV (Signed n) x) (IntV (Signed n) y) =
    INL (IntV (Signed n) (x quot y))
Proof
  rpt strip_tac >>
  simp[vyperInterpreterTheory.evaluate_binop_def, vyperInterpreterTheory.bounded_int_op_def] >>
  `w2i ((i2w x):bytes32) = x` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `w2i ((i2w y):bytes32) = y` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `(i2w y):bytes32 ≠ 0w` by (
    CCONTR_TAC >> fs[] >> fs[integer_wordTheory.word_0_w2i]) >>
  drule integer_wordTheory.word_quot >>
  disch_then (qspecl_then [`(i2w x):bytes32`] mp_tac) >>
  strip_tac >> gvs[] >>
  `w2i ((i2w (x quot y)):bytes32) = x quot y` by
    (irule w2i_i2w_within_signed >> metis_tac[]) >>
  simp[]
QED

Theorem evaluate_binop_mod_signed:
  ∀x y n.
    within_int_bound (Signed n) x ∧ within_int_bound (Signed n) y ∧
    y ≠ 0 ∧ n ≤ 256 ⇒
    evaluate_binop Mod (IntV (Signed n) x) (IntV (Signed n) y) =
    INL (IntV (Signed n) (x rem y))
Proof
  rpt strip_tac >>
  simp[vyperInterpreterTheory.evaluate_binop_def, vyperInterpreterTheory.bounded_int_op_def] >>
  `w2i ((i2w x):bytes32) = x` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `w2i ((i2w y):bytes32) = y` by (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `(i2w y):bytes32 ≠ 0w` by (
    CCONTR_TAC >> fs[] >> fs[integer_wordTheory.word_0_w2i]) >>
  drule integer_wordTheory.word_rem >>
  disch_then (qspecl_then [`(i2w x):bytes32`] mp_tac) >>
  strip_tac >> gvs[] >>
  `within_int_bound (Signed n) (x rem y)` by
    (irule within_int_bound_rem >> metis_tac[]) >>
  `w2i ((i2w (x rem y)):bytes32) = x rem y` by
    (irule w2i_i2w_within_signed >> metis_tac[]) >>
  simp[]
QED

(* ========= Exp ========== *)

Theorem evaluate_binop_exp:
  ∀u x y.
    within_int_bound u (x ** Num y) ∧ 0 ≤ y ⇒
    evaluate_binop Exp (IntV u x) (IntV u y) =
    INL (IntV u (x ** Num y))
Proof
  rpt strip_tac >>
  `¬(y < 0)` by intLib.ARITH_TAC >>
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.bounded_int_op_def]
QED

(* ========= Bitwise (IntV) ========== *)

Theorem evaluate_binop_and_int:
  ∀u x y.
    within_int_bound u (int_and x y) ⇒
    evaluate_binop And (IntV u x) (IntV u y) =
    INL (IntV u (int_and x y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.bounded_int_op_def]
QED

Theorem evaluate_binop_or_int:
  ∀u x y.
    within_int_bound u (int_or x y) ⇒
    evaluate_binop Or (IntV u x) (IntV u y) =
    INL (IntV u (int_or x y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.bounded_int_op_def]
QED

Theorem evaluate_binop_xor_int:
  ∀u x y.
    within_int_bound u (int_xor x y) ⇒
    evaluate_binop XOr (IntV u x) (IntV u y) =
    INL (IntV u (int_xor x y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.bounded_int_op_def]
QED

(* ========= Bitwise (BoolV) ========== *)

Theorem evaluate_binop_and_bool:
  ∀a b.
    evaluate_binop And (BoolV a) (BoolV b) = INL (BoolV (a ∧ b))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_or_bool:
  ∀a b.
    evaluate_binop Or (BoolV a) (BoolV b) = INL (BoolV (a ∨ b))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_xor_bool:
  ∀a b.
    evaluate_binop XOr (BoolV a) (BoolV b) = INL (BoolV (a ≠ b))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

(* ========= Wrapped arithmetic (UAdd, USub, UMul, UDiv) ========== *)

Theorem evaluate_binop_uadd:
  ∀u x y.
    evaluate_binop UAdd (IntV u x) (IntV u y) =
    INL (IntV u (if is_Unsigned u then (x + y) % &(2 ** int_bound_bits u)
                 else signed_int_mod (int_bound_bits u) (x + y)))
Proof
  Cases >> simp[vyperInterpreterTheory.evaluate_binop_def,
                vyperInterpreterTheory.wrapped_int_op_def]
QED

Theorem evaluate_binop_usub:
  ∀u x y.
    evaluate_binop USub (IntV u x) (IntV u y) =
    INL (IntV u (if is_Unsigned u then (x − y) % &(2 ** int_bound_bits u)
                 else signed_int_mod (int_bound_bits u) (x − y)))
Proof
  Cases >> simp[vyperInterpreterTheory.evaluate_binop_def,
                vyperInterpreterTheory.wrapped_int_op_def]
QED

Theorem evaluate_binop_umul:
  ∀u x y.
    evaluate_binop UMul (IntV u x) (IntV u y) =
    INL (IntV u (if is_Unsigned u then (x * y) % &(2 ** int_bound_bits u)
                 else signed_int_mod (int_bound_bits u) (x * y)))
Proof
  Cases >> simp[vyperInterpreterTheory.evaluate_binop_def,
                vyperInterpreterTheory.wrapped_int_op_def]
QED

Theorem evaluate_binop_udiv:
  ∀u x y.
    y ≠ 0 ⇒
    evaluate_binop UDiv (IntV u x) (IntV u y) =
    INL (IntV u (if is_Unsigned u then (x / y) % &(2 ** int_bound_bits u)
                 else signed_int_mod (int_bound_bits u) (x / y)))
Proof
  Cases >> simp[vyperInterpreterTheory.evaluate_binop_def,
                vyperInterpreterTheory.wrapped_int_op_def]
QED

(* ========= Shifts ========== *)

Theorem evaluate_binop_shl:
  ∀u x y.
    0 ≤ y ⇒
    evaluate_binop ShL (IntV u x) (IntV u y) =
    INL (IntV u (int_shift_left (Num y) x))
Proof
  rpt strip_tac >>
  `¬(y < 0)` by intLib.ARITH_TAC >>
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_shr:
  ∀u x y.
    0 ≤ y ⇒
    evaluate_binop ShR (IntV u x) (IntV u y) =
    INL (IntV u (int_shift_right (Num y) x))
Proof
  rpt strip_tac >>
  `¬(y < 0)` by intLib.ARITH_TAC >>
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

(* ========= ExpMod ========== *)

Theorem evaluate_binop_expmod:
  ∀x y.
    evaluate_binop ExpMod (IntV (Unsigned 256) x) (IntV (Unsigned 256) y) =
    INL (IntV (Unsigned 256) (w2i (word_exp ((i2w x):bytes32) (i2w y))))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

(* ========= Min / Max ========== *)

Theorem evaluate_binop_min:
  ∀u x y.
    evaluate_binop Min (IntV u x) (IntV u y) =
    INL (IntV u (if x < y then x else y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_max:
  ∀u x y.
    evaluate_binop Max (IntV u x) (IntV u y) =
    INL (IntV u (if x < y then y else x))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

(* ========= Comparisons ========== *)

Theorem evaluate_binop_eq_int:
  ∀u x y.
    evaluate_binop Eq (IntV u x) (IntV u y) = INL (BoolV (x = y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_lt:
  ∀u x y.
    evaluate_binop Lt (IntV u x) (IntV u y) = INL (BoolV (x < y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_lte:
  ∀u x y.
    evaluate_binop LtE (IntV u x) (IntV u y) = INL (BoolV (x ≤ y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_gt:
  ∀u x y.
    evaluate_binop Gt (IntV u x) (IntV u y) = INL (BoolV (x > y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_gte:
  ∀u x y.
    evaluate_binop GtE (IntV u x) (IntV u y) = INL (BoolV (x ≥ y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_noteq_int:
  ∀u x y.
    evaluate_binop NotEq (IntV u x) (IntV u y) = INL (BoolV (x ≠ y))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.binop_negate_def]
QED

Theorem evaluate_binop_eq_bool:
  ∀a b.
    evaluate_binop Eq (BoolV a) (BoolV b) = INL (BoolV (a = b))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def]
QED

Theorem evaluate_binop_noteq_bool:
  ∀a b.
    evaluate_binop NotEq (BoolV a) (BoolV b) = INL (BoolV (a ≠ b))
Proof
  simp[vyperInterpreterTheory.evaluate_binop_def,
       vyperInterpreterTheory.binop_negate_def]
QED
