(* UnsafeDiv zero is a successful wrapped integer, not a checked Div error.
   Nonzero division deliberately retains the existing word_div/word_quot path. *)
Theory vyperUnsafeDivTest
Ancestors
  arithmetic integer words vyperAST vyperValue vyperValueOperation
  vyperContext vyperTyping vyperTypeContract evalCompilerSubsetScalars
Libs
  cv_transLib vyperCheckContractLib

(* Kernel counterexample to the former claim that success of UnsafeDiv
   implies a nonzero divisor. The operand and result types are uint8. *)
Theorem unsafe_div_success_nonzero_counterexample:
  evaluate_binop (Unsigned 8) (BaseTV (UintT 8)) UnsafeDiv
    (IntV 1) (IntV 0) = INL (IntV 0) /\
  ~((?i1 i2. IntV 1 = IntV i1 /\ IntV 0 = IntV i2 /\ i2 <> 0) \/
    (?i1 i2. IntV 1 = DecimalV i1 /\ IntV 0 = DecimalV i2 /\ i2 <> 0))
Proof
  simp[] >> EVAL_TAC >> simp[]
QED

Theorem unsafe_div_zero:
  evaluate_binop u tv UnsafeDiv (IntV i) (IntV 0) = INL (IntV 0)
Proof
  Cases_on `u` >>
  simp[evaluate_binop_def, wrapped_int_op_def, signed_int_mod_def,
       int_bound_bits_def, is_Unsigned_def, int_ge]
QED

Theorem unsafe_div_unsigned_typed_zero:
  evaluate_binop (Unsigned n) (BaseTV (UintT n)) UnsafeDiv
    (IntV i) (IntV 0) = INL (IntV 0) /\
  value_has_type (BaseTV (UintT n)) (IntV 0)
Proof
  simp[unsafe_div_zero, value_has_type_def]
QED

Theorem unsafe_div_signed_typed_zero:
  evaluate_binop (Signed n) (BaseTV (IntT n)) UnsafeDiv
    (IntV i) (IntV 0) = INL (IntV 0) /\
  value_has_type (BaseTV (IntT n)) (IntV 0)
Proof
  simp[unsafe_div_zero, value_has_type_def, within_int_bound_def]
QED

(* Exact old nonzero signed/unsigned computation, with no rounding change. *)
Theorem unsafe_div_nonzero_path:
  j <> 0 ==>
  evaluate_binop u tv UnsafeDiv (IntV i) (IntV j) =
    wrapped_int_op u (if is_Unsigned u
      then &(w2n (word_div ((i2w i):bytes32) (i2w j)))
      else w2i (word_quot ((i2w i):bytes32) (i2w j)))
Proof
  simp[evaluate_binop_def]
QED

Theorem checked_div_zero_unchanged:
  evaluate_binop u tv Div (IntV i) (IntV 0) = INR (RuntimeError "Div0") /\
  evaluate_binop u tv Div (DecimalV d) (DecimalV 0) = INR (RuntimeError "Div0")
Proof
  simp[evaluate_binop_def]
QED

(* Independent expected literals: narrow and full-word extrema, both signs,
   ordinary nonzero quotients, and the checked MIN_INT/-1 overflow rule. *)
Definition unsafe_div_cases_def:
  unsafe_div_cases =
  [(Unsigned 8, UnsafeDiv, (0:int), (0:int), INL (IntV 0));
   (Unsigned 8, UnsafeDiv, 1, 0, INL (IntV 0));
   (Unsigned 8, UnsafeDiv, 255, 0, INL (IntV 0));
   (Signed 8, UnsafeDiv, -128, 0, INL (IntV 0));
   (Signed 8, UnsafeDiv, -1, 0, INL (IntV 0));
   (Signed 8, UnsafeDiv, 0, 0, INL (IntV 0));
   (Signed 8, UnsafeDiv, 127, 0, INL (IntV 0));
   (Unsigned 256, UnsafeDiv, &(2 ** 256) - 1, 0, INL (IntV 0));
   (Signed 256, UnsafeDiv, -&(2 ** 255), 0, INL (IntV 0));
   (Signed 256, UnsafeDiv, &(2 ** 255) - 1, 0, INL (IntV 0));
   (Unsigned 8, UnsafeDiv, 0, 1, INL (IntV 0));
   (Unsigned 8, UnsafeDiv, 255, 1, INL (IntV 255));
   (Unsigned 8, UnsafeDiv, 255, 2, INL (IntV 127));
   (Unsigned 8, UnsafeDiv, 255, 255, INL (IntV 1));
   (Unsigned 256, UnsafeDiv, &(2 ** 256) - 1, 2, INL (IntV (&(2 ** 255) - 1)));
   (Signed 8, UnsafeDiv, 7, 3, INL (IntV 2));
   (Signed 8, UnsafeDiv, -7, 3, INL (IntV (-2)));
   (Signed 8, UnsafeDiv, 7, -3, INL (IntV (-2)));
   (Signed 8, UnsafeDiv, -7, -3, INL (IntV 2));
   (Signed 8, UnsafeDiv, -128, -1, INL (IntV (-128)));
   (Signed 256, UnsafeDiv, -&(2 ** 255), -1, INL (IntV (-&(2 ** 255))));
   (Unsigned 8, Div, 255, 0, INR (RuntimeError "Div0"));
   (Signed 8, Div, -128, 0, INR (RuntimeError "Div0"));
   (Unsigned 256, Div, &(2 ** 256) - 1, 0, INR (RuntimeError "Div0"));
   (Signed 256, Div, -&(2 ** 255), 0, INR (RuntimeError "Div0"));
   (Unsigned 8, Div, 255, 2, INL (IntV 127));
   (Signed 8, Div, -7, 3, INL (IntV (-2)));
   (Signed 8, Div, -128, -1, INR (RuntimeError "Div overflow"));
   (Signed 256, Div, -&(2 ** 255), -1, INR (RuntimeError "Div overflow"))]
End
val () = cv_auto_trans unsafe_div_cases_def;

Definition unsafe_div_cases_ok_def:
  unsafe_div_cases_ok = EVERY (λ(u,bop,i,j,r).
    evaluate_binop u NoneTV bop (IntV i) (IntV j) = r /\
    (case r of INL (IntV k) => within_int_bound u k | _ => T))
    unsafe_div_cases
End
val () = cv_auto_trans unsafe_div_cases_ok_def;

Theorem unsafe_div_boundaries_eval:
  unsafe_div_cases_ok
Proof
  EVAL_TAC >> simp[]
QED

Theorem unsafe_div_boundaries_cv:
  unsafe_div_cases_ok
Proof
  CONV_TAC cv_eval
QED

(* All 32 legal widths, both signednesses, both input extrema, typed zero
   and unchanged checked-zero failure. Not a fixture-width whitelist. *)
Definition unsafe_div_all_widths_ok_def:
  unsafe_div_all_widths_ok = EVERY (λn.
    evaluate_binop (Unsigned n) (BaseTV (UintT n)) UnsafeDiv
      (IntV (&(2 ** n) - 1)) (IntV 0) = INL (IntV 0) /\
    evaluate_binop (Unsigned n) (BaseTV (UintT n)) UnsafeDiv
      (IntV 0) (IntV 0) = INL (IntV 0) /\
    evaluate_binop (Signed n) (BaseTV (IntT n)) UnsafeDiv
      (IntV (-&(2 ** (n - 1)))) (IntV 0) = INL (IntV 0) /\
    evaluate_binop (Signed n) (BaseTV (IntT n)) UnsafeDiv
      (IntV (&(2 ** (n - 1)) - 1)) (IntV 0) = INL (IntV 0) /\
    within_int_bound (Unsigned n) 0 /\ within_int_bound (Signed n) 0 /\
    evaluate_binop (Unsigned n) (BaseTV (UintT n)) Div
      (IntV (&(2 ** n) - 1)) (IntV 0) = INR (RuntimeError "Div0") /\
    evaluate_binop (Signed n) (BaseTV (IntT n)) Div
      (IntV (-&(2 ** (n - 1)))) (IntV 0) = INR (RuntimeError "Div0"))
    (GENLIST (λk. 8 * SUC k) 32)
End
val () = cv_auto_trans unsafe_div_all_widths_ok_def;

Theorem unsafe_div_all_widths_cv:
  unsafe_div_all_widths_ok
Proof
  CONV_TAC cv_eval
QED

Theorem unsafe_div_builtin_zero_cv:
  evaluate_builtin empty_evaluation_context accounts (BaseT (UintT 8))
    (Bop UnsafeDiv) tys [IntV 255; IntV 0] = INL (IntV 0) /\
  evaluate_builtin empty_evaluation_context accounts (BaseT (IntT 256))
    (Bop UnsafeDiv) tys [IntV (-&(2 ** 255)); IntV 0] = INL (IntV 0) /\
  evaluate_builtin empty_evaluation_context accounts (BaseT (UintT 8))
    (Bop Div) tys [IntV 255; IntV 0] = INR (RuntimeError "Div0") /\
  evaluate_builtin empty_evaluation_context accounts (BaseT (IntT 256))
    (Bop Div) tys [IntV (-&(2 ** 255)); IntV 0] = INR (RuntimeError "Div0")
Proof
  simp[evaluate_builtin_def, get_tenv_def, empty_evaluation_context_def,
       type_to_int_bound_def, evaluate_type_def] >> CONV_TAC cv_eval
QED

(* Reuse the unchanged unsafe uint8 and int256 fixture families through
   the sealed checker in runtime and deployment modes. *)
Theorem unsafe_div_fixtures_runtime_checked:
  IS_SOME (check_contract F [] (0w : address)
    [(NONE, scalar_arith_unsafe_uint_program)]) /\
  IS_SOME (check_contract F [] (0w : address)
    [(NONE, scalar_arith_unsafe_int_program)])
Proof
  simp[scalar_arith_unsafe_uint_program_def, scalar_arith_unsafe_int_program_def,
       scalar_binary_bop_fn_def] >> conj_tac >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem unsafe_div_fixtures_deployment_checked:
  IS_SOME (check_contract T [] (0w : address)
    [(NONE, scalar_arith_unsafe_uint_program)]) /\
  IS_SOME (check_contract T [] (0w : address)
    [(NONE, scalar_arith_unsafe_int_program)])
Proof
  simp[scalar_arith_unsafe_uint_program_def, scalar_arith_unsafe_int_program_def,
       scalar_binary_bop_fn_def] >> conj_tac >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED
