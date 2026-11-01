(* Exact scaled-bound checks, before division, and signed truncation toward
   zero. Expected results are independent literals, not truncated-bound tests.
   The same matrix is checked by kernel EVAL and the translated CV evaluator. *)
Theory vyperDecimalConvertTest
Ancestors
  vyperValueOperation vyperContext vyperDecimalBounds
Libs
  cv_transLib

Theorem decimal_convert_signed_scaled_boundary:
  evaluate_convert tenv (DecimalV i) (BaseT (IntT n)) =
    if -&(2 ** (n - 1)) * 10000000000 ≤ i ∧
       i ≤ (&(2 ** (n - 1)) - 1) * 10000000000
    then INL (IntV (i quot 10000000000))
    else INR (RuntimeError "convert decimal int")
Proof
  simp[evaluate_convert_def, decimal_truncate_eq_quot]
QED

Theorem decimal_convert_unsigned_scaled_boundary:
  evaluate_convert tenv (DecimalV i) (BaseT (UintT n)) =
    if 0 ≤ i ∧ i ≤ (&(2 ** n) - 1) * 10000000000
    then INL (IntV (i / 10000000000))
    else INR (RuntimeError "convert decimal uint")
Proof
  simp[evaluate_convert_def]
QED

(* Both scaled extrema succeed; one decimal quantum beyond either fails.
   These cover arbitrary widths, even widths wider than decimal itself. *)
Theorem decimal_convert_signed_extrema:
  0 < n ==>
  evaluate_convert tenv (DecimalV (-&(2 ** (n - 1)) * 10000000000))
    (BaseT (IntT n)) = INL (IntV (-&(2 ** (n - 1)))) ∧
  evaluate_convert tenv (DecimalV ((&(2 ** (n - 1)) - 1) * 10000000000))
    (BaseT (IntT n)) = INL (IntV (&(2 ** (n - 1)) - 1))
Proof
  strip_tac >>
  simp[evaluate_convert_def] >>
  qabbrev_tac `k = 2 ** (n - 1)` >>
  `1 ≤ k` by simp[Abbr `k`, arithmeticTheory.ONE_LE_EXP] >>
  rw[intExtensionTheory.SGN_def, integerTheory.INT_ABS] >>
  gvs[integerTheory.INT_NEG_RMUL, integerTheory.INT_DIV_RMUL] >>
  intLib.ARITH_TAC
QED

Theorem decimal_convert_outside_scaled_bounds:
  evaluate_convert tenv (DecimalV (-&(2 ** (n - 1)) * 10000000000 - 1))
    (BaseT (IntT n)) = INR (RuntimeError "convert decimal int") ∧
  evaluate_convert tenv (DecimalV ((&(2 ** (n - 1)) - 1) * 10000000000 + 1))
    (BaseT (IntT n)) = INR (RuntimeError "convert decimal int") ∧
  evaluate_convert tenv (DecimalV (-1)) (BaseT (UintT n)) =
    INR (RuntimeError "convert decimal uint") ∧
  evaluate_convert tenv (DecimalV ((&(2 ** n) - 1) * 10000000000 + 1))
    (BaseT (UintT n)) = INR (RuntimeError "convert decimal uint")
Proof
  simp[evaluate_convert_def] >> intLib.ARITH_TAC
QED

Definition decimal_convert_cases_def:
  decimal_convert_cases =
  [(* int8 scaled extrema and neighbouring fractional values *)
   ((1270000000000:int), IntT 8, INL (IntV 127));
   (-1280000000000, IntT 8, INL (IntV (-128)));
   (1270000000001, IntT 8, INR (RuntimeError "convert decimal int"));
   (-1280000000001, IntT 8, INR (RuntimeError "convert decimal int"));
   (1269999999999, IntT 8, INL (IntV 126));
   (-1279999999999, IntT 8, INL (IntV (-127)));
   (1279999999999, IntT 8, INR (RuntimeError "convert decimal int"));
   (-1289999999999, IntT 8, INR (RuntimeError "convert decimal int"));
   (* Fractions of both signs, including the negative floor/quot distinction *)
   (0, IntT 8, INL (IntV 0));
   (1, IntT 8, INL (IntV 0));
   (-1, IntT 8, INL (IntV 0));
   (9999999999, IntT 8, INL (IntV 0));
   (-9999999999, IntT 8, INL (IntV 0));
   (10000000001, IntT 8, INL (IntV 1));
   (-10000000001, IntT 8, INL (IntV (-1)));
   (* uint8: negative fractions must fail even if they truncate to zero *)
   (0, UintT 8, INL (IntV 0));
   (1, UintT 8, INL (IntV 0));
   (-1, UintT 8, INR (RuntimeError "convert decimal uint"));
   (-9999999999, UintT 8, INR (RuntimeError "convert decimal uint"));
   (2550000000000, UintT 8, INL (IntV 255));
   (2549999999999, UintT 8, INL (IntV 254));
   (2550000000001, UintT 8, INR (RuntimeError "convert decimal uint"));
   (2559999999999, UintT 8, INR (RuntimeError "convert decimal uint"));
   (* A second narrower width *)
   (327670000000000, IntT 16, INL (IntV 32767));
   (-327680000000000, IntT 16, INL (IntV (-32768)));
   (327670000000001, IntT 16, INR (RuntimeError "convert decimal int"));
   (-327680000000001, IntT 16, INR (RuntimeError "convert decimal int"));
   (655350000000000, UintT 16, INL (IntV 65535));
   (655350000000001, UintT 16, INR (RuntimeError "convert decimal uint"));
   (* The minimum and maximum representable decimal, to full-word integers *)
   (-187072209578355573530071658587684226515959365500928,
     IntT 256, INL (IntV (-18707220957835557353007165858768422651595)));
   (187072209578355573530071658587684226515959365500927,
     IntT 256, INL (IntV 18707220957835557353007165858768422651595));
   (187072209578355573530071658587684226515959365500927,
     UintT 256, INL (IntV 18707220957835557353007165858768422651595));
   (-187072209578355573530071658587684226515959365500928,
     UintT 256, INR (RuntimeError "convert decimal uint"))]
End
val () = cv_auto_trans decimal_convert_cases_def;

Definition decimal_convert_cases_ok_def:
  decimal_convert_cases_ok = EVERY (λ(i,bt,r).
    evaluate_convert FEMPTY (DecimalV i) (BaseT bt) = r) decimal_convert_cases
End
val () = cv_auto_trans decimal_convert_cases_ok_def;

Theorem decimal_convert_boundaries_eval:
  decimal_convert_cases_ok
Proof
  EVAL_TAC
QED

Theorem decimal_convert_boundaries_cv:
  decimal_convert_cases_ok
Proof
  CONV_TAC cv_eval
QED

(* Check actual type-builtin dispatch, not only evaluate_convert directly. *)
Theorem decimal_convert_builtin_boundaries_cv:
  evaluate_type_builtin empty_evaluation_context Convert (BaseT (IntT 8)) [BaseT DecimalT]
    [DecimalV 1270000000001] = INR (RuntimeError "convert decimal int") ∧
  evaluate_type_builtin empty_evaluation_context Convert (BaseT (UintT 8)) [BaseT DecimalT]
    [DecimalV (-1)] = INR (RuntimeError "convert decimal uint") ∧
  evaluate_type_builtin empty_evaluation_context Convert (BaseT (IntT 8)) [BaseT DecimalT]
    [DecimalV (-10000000001)] = INL (IntV (-1))
Proof
  simp[evaluate_type_builtin_def, get_tenv_def,
       empty_evaluation_context_def] >> CONV_TAC cv_eval
QED
