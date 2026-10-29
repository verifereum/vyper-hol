(* Signed decimal multiplication: minimum/maximum, overflow and truncation.
   All regression operands are representable decimals. Expected results are
   independent values, checked with both kernel EVAL and translated CV. *)
Theory vyperDecimalMulTest
Ancestors
  arithmetic integer intExtension vyperAST vyperValue vyperValueOperation
  vyperContext vyperDecimalBounds vyperTyping vyperTypeContract
  vyperTypeBuiltins evalCompilerSubsetScalars
Libs
  cv_transLib vyperCheckContractLib

Theorem decimal_mul_signed_result:
  evaluate_binop u tv Mul (DecimalV i) (DecimalV j) =
    let q = SGN (i * j) * (ABS (i * j) / 10000000000) in
    if within_int_bound (Signed 168) q then INL (DecimalV q)
    else INR (RuntimeError "Decimal Mul bound")
Proof
  simp[evaluate_binop_def]
QED

Theorem decimal_mul_success_type:
  evaluate_binop u tv Mul (DecimalV i) (DecimalV j) = INL v ==>
  value_has_type (BaseTV DecimalT) v
Proof
  simp[decimal_mul_signed_result, AllCaseEqs()] >>
  rw[] >> gvs[value_has_type_def, within_int_bound_def]
QED

(* The former absolute-quotient guard rejects precisely this valid endpoint. *)
Theorem decimal_mul_minimum:
  ~within_int_bound (Signed 168)
    (ABS ((-&(2 ** 167)) * 10000000000) / 10000000000) /\
  evaluate_binop (Signed 168) (BaseTV DecimalT) Mul
    (DecimalV (-&(2 ** 167))) (DecimalV 10000000000) =
    INL (DecimalV (-&(2 ** 167))) /\
  value_has_type (BaseTV DecimalT) (DecimalV (-&(2 ** 167)))
Proof
  EVAL_TAC
QED

Definition decimal_mul_cases_def:
  decimal_mul_cases =
  [((-187072209578355573530071658587684226515959365500928:int),
     (10000000000:int), INL (DecimalV (-187072209578355573530071658587684226515959365500928)));
   (187072209578355573530071658587684226515959365500927,
     10000000000, INL (DecimalV 187072209578355573530071658587684226515959365500927));
   (* Exactly one quantum above maximum: minimum times -1.0. *)
   (-187072209578355573530071658587684226515959365500928,
     -10000000000, INR (RuntimeError "Decimal Mul bound"));
   (* Exactly one quantum below minimum: -(2 ** 167 + 1)/3 times 3.0. *)
   (-62357403192785191176690552862561408838653121833643,
     30000000000, INR (RuntimeError "Decimal Mul bound"));
   (187072209578355573530071658587684226515959365500927,
     -10000000000, INL (DecimalV (-187072209578355573530071658587684226515959365500927)));
   (7, 3000000000, INL (DecimalV 2));
   (-7, 3000000000, INL (DecimalV (-2)));
   (7, -3000000000, INL (DecimalV (-2)));
   (-7, -3000000000, INL (DecimalV 2));
   (1, 9999999999, INL (DecimalV 0));
   (-1, 9999999999, INL (DecimalV 0));
   (0, 10000000000, INL (DecimalV 0))]
End
val () = cv_auto_trans decimal_mul_cases_def;

Definition decimal_mul_cases_ok_def:
  decimal_mul_cases_ok = EVERY (λ(i,j,r).
    evaluate_binop (Signed 168) (BaseTV DecimalT) Mul
      (DecimalV i) (DecimalV j) = r /\
    within_int_bound (Signed 168) i /\ within_int_bound (Signed 168) j /\
    (case r of INL (DecimalV k) => within_int_bound (Signed 168) k | _ => T))
    decimal_mul_cases
End
val () = cv_auto_trans decimal_mul_cases_ok_def;

Theorem decimal_mul_boundaries_eval:
  decimal_mul_cases_ok
Proof
  EVAL_TAC
QED

Theorem decimal_mul_boundaries_cv:
  decimal_mul_cases_ok
Proof
  CONV_TAC cv_eval
QED

Theorem decimal_mul_builtin_boundaries_cv:
  evaluate_builtin empty_evaluation_context accounts (BaseT DecimalT)
    (Bop Mul) tys [DecimalV (-&(2 ** 167)); DecimalV 10000000000] =
    INL (DecimalV (-&(2 ** 167))) /\
  evaluate_builtin empty_evaluation_context accounts (BaseT DecimalT)
    (Bop Mul) tys [DecimalV (-&(2 ** 167)); DecimalV (-10000000000)] =
    INR (RuntimeError "Decimal Mul bound")
Proof
  simp[evaluate_builtin_def, get_tenv_def, empty_evaluation_context_def,
       type_to_int_bound_def, evaluate_type_def, decimal_mul_signed_result] >>
  CONV_TAC cv_eval
QED

(* The unchanged compiler fixture remains well typed in both checker modes.
   This does not execute its bytecode/parity theorem. *)
Theorem decimal_mul_fixture_runtime_checked:
  IS_SOME (check_contract F [] (0w : address)
    [(NONE, scalar_arith_decimal_mul_program)])
Proof
  simp[scalar_arith_decimal_mul_program_def, scalar_binary_bop_fn_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem decimal_mul_fixture_deployment_checked:
  IS_SOME (check_contract T [] (0w : address)
    [(NONE, scalar_arith_decimal_mul_program)])
Proof
  simp[scalar_arith_decimal_mul_program_def, scalar_binary_bop_fn_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED
