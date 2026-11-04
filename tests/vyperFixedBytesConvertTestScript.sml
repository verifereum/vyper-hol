(* Fixed bytes: preserve equal/widen right padding, and narrow only an
   entirely zero suffix. Independent literal expectations use EVAL and CV. *)
Theory vyperFixedBytesConvertTest
Ancestors
  list rich_list arithmetic words vyperAST vyperValue vyperValueOperation
  vyperContext vyperTypeConversions vyperTypeSystem vyperTypeContract
Libs
  cv_transLib vyperCheckContractLib

Definition scalar_convert_bytes32_to_bytes4_program_def:
  scalar_convert_bytes32_to_bytes4_program =
    [FunctionDecl External Pure F F "bytes32_to_bytes4"
       [("x", BaseT (BytesT (Fixed 32)))] ([] : expr list)
       (BaseT (BytesT (Fixed 4)))
       [Return (SOME (TypeBuiltin (BaseT (BytesT (Fixed 4))) Convert
         (BaseT (BytesT (Fixed 4)))
         [Name (BaseT (BytesT (Fixed 32))) "x"]))]]
End

Theorem fixed_bytes_conversion_boundary:
  evaluate_convert tenv (BytesV bs) (BaseT (BytesT (Fixed n))) =
    if LENGTH bs <= n then INL (BytesV (PAD_RIGHT 0w n bs))
    else if EVERY (λb. b = 0w) (DROP n bs)
         then INL (BytesV (TAKE n bs))
         else INR (RuntimeError "convert BytesV bound")
Proof
  simp[evaluate_convert_def]
QED

(* No input typing or legal-type-bound precondition is needed: every success
   has exactly the requested length, including zero and bounds above 32. *)
Theorem fixed_bytes_success_length:
  evaluate_convert tenv (BytesV bs) (BaseT (BytesT (Fixed n))) = INL v ==>
  ?out. v = BytesV out /\ LENGTH out = n
Proof
  rw[evaluate_convert_def, AllCaseEqs()] >>
  simp[LENGTH_TAKE, listTheory.PAD_RIGHT]
QED

Theorem fixed_bytes_narrow_success_iff:
  n < LENGTH bs ==>
  (evaluate_convert tenv (BytesV bs) (BaseT (BytesT (Fixed n))) = INL v <=>
   EVERY (λb. b = 0w) (DROP n bs) /\ v = BytesV (TAKE n bs))
Proof
  rw[evaluate_convert_def] >> eq_tac >> strip_tac >> gvs[]
QED

Theorem fixed_bytes_conversion_valid:
  (!k. bd = Dynamic k ==> k <= n) ==>
  valid_conversion (BaseT (BytesT bd)) (BaseT (BytesT (Fixed n)))
Proof
  Cases_on `bd` >> simp[valid_conversion_def]
QED

Definition fixed_bytes_cases_def:
  fixed_bytes_cases =
  [((([] : word8 list), 0), INL (BytesV []));
   (([], 4), INL (BytesV [0w; 0w; 0w; 0w]));
   (([1w; 2w; 128w; 255w], 4), INL (BytesV [1w; 2w; 128w; 255w]));
   (([1w; 2w], 4), INL (BytesV [1w; 2w; 0w; 0w]));
   (([128w], 4), INL (BytesV [128w; 0w; 0w; 0w]));
   (([1w; 2w; 0w; 0w], 2), INL (BytesV [1w; 2w]));
   (([255w; 128w; 0w; 0w], 2), INL (BytesV [255w; 128w]));
   (([0w; 0w], 0), INL (BytesV []));
   (([0w; 1w], 0), INR (RuntimeError "convert BytesV bound"));
   (* Nonzero first, middle, and last dropped byte: EVERY is required. *)
   (([1w; 2w; 1w; 0w; 0w], 2), INR (RuntimeError "convert BytesV bound"));
   (([1w; 2w; 0w; 1w; 0w], 2), INR (RuntimeError "convert BytesV bound"));
   (([1w; 2w; 0w; 0w; 1w], 2), INR (RuntimeError "convert BytesV bound"));
   (([1w; 2w; 3w; 4w] ++ REPLICATE 28 0w, 4),
      INL (BytesV [1w; 2w; 3w; 4w]));
   (([1w; 2w; 3w; 4w; 1w] ++ REPLICATE 27 0w, 4),
      INR (RuntimeError "convert BytesV bound"));
   (([1w; 2w; 3w; 4w] ++ REPLICATE 27 0w ++ [1w], 4),
      INR (RuntimeError "convert BytesV bound"));
   ((REPLICATE 32 255w, 32), INL (BytesV (REPLICATE 32 255w)))]
End
val () = cv_auto_trans fixed_bytes_cases_def;

Definition fixed_bytes_cases_ok_def:
  fixed_bytes_cases_ok = EVERY (λ((bs,n),r).
    evaluate_convert FEMPTY (BytesV bs) (BaseT (BytesT (Fixed n))) = r /\
    (case r of INL (BytesV out) => LENGTH out = n | _ => T))
    fixed_bytes_cases
End
val () = cv_auto_trans fixed_bytes_cases_ok_def;

Theorem fixed_bytes_boundaries_eval:
  fixed_bytes_cases_ok
Proof
  EVAL_TAC
QED

Theorem fixed_bytes_boundaries_cv:
  fixed_bytes_cases_ok
Proof
  CONV_TAC cv_eval
QED

(* All 32 x 32 legal source/target sizes, not a bytes32 fixture whitelist.
   Zero inputs must succeed at exact target length. Nonzero tails must fail. *)
Definition fixed_bytes_length_pairs_ok_def:
  fixed_bytes_length_pairs_ok = EVERY (λm. EVERY (λn.
    evaluate_convert FEMPTY (BytesV (REPLICATE m 0w))
      (BaseT (BytesT (Fixed n))) = INL (BytesV (REPLICATE n 0w)) /\
    evaluate_convert FEMPTY (BytesV (REPLICATE m 1w))
      (BaseT (BytesT (Fixed n))) =
      (if m <= n then INL (BytesV (REPLICATE m 1w ++ REPLICATE (n - m) 0w))
       else INR (RuntimeError "convert BytesV bound")))
    (GENLIST SUC 32)) (GENLIST SUC 32)
End
val () = cv_auto_trans fixed_bytes_length_pairs_ok_def;

Theorem fixed_bytes_all_length_pairs_cv:
  fixed_bytes_length_pairs_ok
Proof
  CONV_TAC cv_eval
QED

Theorem fixed_bytes_builtin_boundaries_cv:
  evaluate_type_builtin empty_evaluation_context Convert
    (BaseT (BytesT (Fixed 4))) [BaseT (BytesT (Dynamic 32))]
    [BytesV [1w; 2w; 3w; 4w]] =
      INL (BytesV [1w; 2w; 3w; 4w]) /\
  evaluate_type_builtin empty_evaluation_context Convert
    (BaseT (BytesT (Fixed 4))) [BaseT (BytesT (Dynamic 32))]
    [BytesV [1w; 2w]] =
      INL (BytesV [1w; 2w; 0w; 0w]) /\
  evaluate_type_builtin empty_evaluation_context Convert
    (BaseT (BytesT (Fixed 4))) [BaseT (BytesT (Dynamic 32))]
    [BytesV ([1w; 2w; 3w; 4w] ++ REPLICATE 28 0w)] =
      INL (BytesV [1w; 2w; 3w; 4w]) /\
  evaluate_type_builtin empty_evaluation_context Convert
    (BaseT (BytesT (Fixed 4))) [BaseT (BytesT (Dynamic 32))]
    [BytesV ([1w; 2w; 3w; 4w] ++ REPLICATE 27 0w ++ [1w])] =
      INR (RuntimeError "convert BytesV bound")
Proof
  simp[evaluate_type_builtin_def, get_tenv_def,
       empty_evaluation_context_def] >> CONV_TAC cv_eval
QED

(* Actual unchanged fixture through the sealed checker, in both modes. *)
Theorem fixed_bytes_fixture_runtime_checked:
  IS_SOME (check_contract F [] (0w : address)
    [(NONE, scalar_convert_bytes32_to_bytes4_program)])
Proof
  simp[scalar_convert_bytes32_to_bytes4_program_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem fixed_bytes_fixture_deployment_checked:
  IS_SOME (check_contract T [] (0w : address)
    [(NONE, scalar_convert_bytes32_to_bytes4_program)])
Proof
  simp[scalar_convert_bytes32_to_bytes4_program_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

(* Integer encodings select the low bytes; strings pad on the right. *)
Theorem convert_alignment_regressions:
  evaluate_convert FEMPTY (IntV 5) (BaseT (BytesT (Fixed 1))) =
    INL (BytesV [5w]) /\
  evaluate_convert FEMPTY (IntV 0x1234) (BaseT (BytesT (Fixed 20))) =
    INL (BytesV (REPLICATE 18 0w ++ [0x12w; 0x34w])) /\
  evaluate_convert FEMPTY (StringV "ab") (BaseT (BytesT (Fixed 4))) =
    INL (BytesV [97w; 98w; 0w; 0w])
Proof
  EVAL_TAC
QED

(* Sign extension uses the runtime input width, not the target width. *)
Theorem convert_signed_bytes_regressions:
  evaluate_convert FEMPTY (BytesV [255w]) (BaseT (IntT 8)) =
    INL (IntV (-1)) /\
  evaluate_convert FEMPTY (BytesV [255w; 255w; 255w; 255w])
    (BaseT (IntT 256)) = INL (IntV (-1)) /\
  evaluate_convert FEMPTY (BytesV (REPLICATE 16 255w)) (BaseT (IntT 64)) =
    INL (IntV (-1)) /\
  evaluate_convert FEMPTY (BytesV [128w]) (BaseT (IntT 256)) =
    INL (IntV (-128)) /\
  evaluate_convert FEMPTY (BytesV (REPLICATE 32 255w)) (BaseT (IntT 256)) =
    INL (IntV (-1)) /\
  evaluate_convert FEMPTY (BytesV [255w]) (BaseT DecimalT) =
    INL (DecimalV (-1))
Proof
  EVAL_TAC
QED

Theorem convert_empty_bytes_regressions:
  evaluate_convert FEMPTY (BytesV []) (BaseT (IntT 8)) =
    INR (RuntimeError "convert empty bytes to signed") /\
  evaluate_convert FEMPTY (BytesV []) (BaseT DecimalT) =
    INR (RuntimeError "convert empty bytes to signed") /\
  evaluate_convert FEMPTY (BytesV []) (BaseT (UintT 8)) = INL (IntV 0)
Proof
  EVAL_TAC
QED
