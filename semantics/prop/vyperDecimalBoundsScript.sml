(* Arithmetic boundary for checked decimal-to-integer conversions.
   The scaled check is stronger than a check on the truncated quotient. *)
Theory vyperDecimalBounds
Ancestors
  arithmetic integer intExtension vyperValue
Libs
  intLib

Theorem decimal_div_nonnegative_bound:
  0 ≤ (i:int) ∧ i ≤ k * 10000000000 ==>
  0 ≤ i / 10000000000 ∧ i / 10000000000 ≤ k
Proof
  strip_tac >>
  `10000000000:int ≠ 0` by intLib.ARITH_TAC >>
  drule INT_DIVISION >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

(* HOL quot, unlike / on negative integers, is truncation toward zero. *)
Theorem decimal_truncate_eq_quot:
  SGN i * (ABS i / 10000000000) = i quot 10000000000
Proof
  Cases_on `i` >>
  simp[SGN_def, INT_ABS, INT_QUOT, INT_QUOT_NEG, INT_DIV] >>
  rw[] >> intLib.ARITH_TAC
QED

Theorem decimal_truncate_signed_bound:
  0 < n ∧
  -&(2 ** (n - 1)) * 10000000000 ≤ i ∧
  i ≤ (&(2 ** (n - 1)) - 1) * 10000000000 ==>
  within_int_bound (Signed n) (SGN i * (ABS i / 10000000000))
Proof
  rpt strip_tac >>
  Cases_on `i = 0` >- simp[SGN_def, within_int_bound_def] >>
  Cases_on `i < 0`
  >- (
    `0 ≤ -i ∧ -i ≤ &(2 ** (n - 1)) * 10000000000`
      by intLib.ARITH_TAC >>
    drule_all decimal_div_nonnegative_bound >> strip_tac >>
    simp[SGN_def, INT_ABS, within_int_bound_def] >>
    intLib.ARITH_TAC) >>
  `0 ≤ i` by intLib.ARITH_TAC >>
  drule_all decimal_div_nonnegative_bound >> strip_tac >>
  simp[SGN_def, INT_ABS, within_int_bound_def] >>
  intLib.ARITH_TAC
QED

Theorem decimal_div_unsigned_bound:
  0 ≤ i ∧ i ≤ (&(2 ** n) - 1) * 10000000000 ==>
  within_int_bound (Unsigned n) (i / 10000000000)
Proof
  strip_tac >>
  drule_all decimal_div_nonnegative_bound >> strip_tac >>
  simp[within_int_bound_def] >> intLib.ARITH_TAC
QED
