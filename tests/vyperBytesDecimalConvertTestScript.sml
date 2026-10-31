(* Bytes-to-decimal: right-pad32, arithmetic shift, signed interpretation,
   then the decimal representation bound. Literal expectations are checked
   independently by kernel EVAL and CV; no fixture whitelist is used. *)
Theory vyperBytesDecimalConvertTest
Ancestors
  vyperValue vyperValueOperation vyperContext vyperTypeConversions vyperTypeSystem
  vyperTypeContract
Libs
  cv_transLib vyperCheckContractLib

Definition scalar_convert_bytes32_to_decimal_program_def:
  scalar_convert_bytes32_to_decimal_program =
    [FunctionDecl External Pure F F "bytes32_to_decimal"
       [("x", BaseT (BytesT (Fixed 32)))] ([] : expr list) (BaseT DecimalT)
       [Return (SOME (TypeBuiltin (BaseT DecimalT) Convert (BaseT DecimalT)
         [Name (BaseT (BytesT (Fixed 32))) "x"]))]]
End

Theorem bytes_decimal_conversion_boundary:
  evaluate_convert tenv (BytesV bs) (BaseT DecimalT) =
    (if bs = [] then INR (RuntimeError "convert empty bytes to signed")
     else bounded_decimal_op (w2i
      ((word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32) >>
       (8 * (32 - LENGTH bs)))))
Proof
  simp[evaluate_convert_def]
QED

Theorem bytes_decimal_conversion_valid:
  (!k. bd = Dynamic k ==> k <= 32) ==>
  valid_conversion (BaseT (BytesT bd)) (BaseT DecimalT)
Proof
  Cases_on `bd` >> simp[valid_conversion_def]
QED

(* The signed decoding and bound are separate interfaces: no assumption about
   the input type or byte length is needed for successful-result typing. *)
Theorem bytes_decimal_success_iff:
  evaluate_convert tenv (BytesV bs) (BaseT DecimalT) = INL (DecimalV i) <=>
  bs <> [] /\ i = w2i ((word_of_bytes_be (PAD_RIGHT 0w 32 bs) : bytes32) >>
           (8 * (32 - LENGTH bs))) /\ within_int_bound (Signed 168) i
Proof
  rw[evaluate_convert_def, bounded_decimal_op_def] >>
  eq_tac >> strip_tac >> gvs[]
QED

Definition bytes_decimal_cases_def:
  bytes_decimal_cases =
  [(([] : word8 list), INR (RuntimeError "convert empty bytes to signed"));
   ([0w], INL (DecimalV 0));
   ([1w], INL (DecimalV 1));
   ([127w], INL (DecimalV 127));
   ([128w], INL (DecimalV (-128)));
   ([255w], INL (DecimalV (-1)));
   ([1w; 2w], INL (DecimalV 258));
   ([0w; 255w], INL (DecimalV 255));
   ([128w; 0w], INL (DecimalV (-32768)));
   ([255w; 0w], INL (DecimalV (-256)));
   ([255w; 254w], INL (DecimalV (-2)));
   ([2w; 84w; 11w; 228w; 0w], INL (DecimalV 10000000000));
   (REPLICATE 20 255w, INL (DecimalV (-1)));
   (* Signed 168-bit extrema, minimal encoding and sign-extended bytes32. *)
   (127w :: REPLICATE 20 255w,
      INL (DecimalV 187072209578355573530071658587684226515959365500927));
   (128w :: REPLICATE 20 0w,
      INL (DecimalV (-187072209578355573530071658587684226515959365500928)));
   (REPLICATE 11 0w ++ [127w] ++ REPLICATE 20 255w,
      INL (DecimalV 187072209578355573530071658587684226515959365500927));
   (REPLICATE 11 255w ++ [128w] ++ REPLICATE 20 0w,
      INL (DecimalV (-187072209578355573530071658587684226515959365500928)));
   (* One unit outside each bound, without and with sign extension. *)
   ([0w; 128w] ++ REPLICATE 20 0w, INR (RuntimeError "bounded_decimal_op"));
   ([255w; 127w] ++ REPLICATE 20 255w, INR (RuntimeError "bounded_decimal_op"));
   (REPLICATE 11 0w ++ [128w] ++ REPLICATE 20 0w,
      INR (RuntimeError "bounded_decimal_op"));
   (REPLICATE 11 255w ++ [127w] ++ REPLICATE 20 255w,
      INR (RuntimeError "bounded_decimal_op"));
   (128w :: REPLICATE 21 0w, INR (RuntimeError "bounded_decimal_op"));
   (REPLICATE 31 0w, INL (DecimalV 0));
   (REPLICATE 32 0w, INL (DecimalV 0));
   (REPLICATE 32 255w, INL (DecimalV (-1)));
   (REPLICATE 31 0w ++ [255w], INL (DecimalV 255));
   (127w :: REPLICATE 31 255w, INR (RuntimeError "bounded_decimal_op"));
   (128w :: REPLICATE 31 0w, INR (RuntimeError "bounded_decimal_op"))]
End
val () = cv_auto_trans bytes_decimal_cases_def;

Definition bytes_decimal_cases_ok_def:
  bytes_decimal_cases_ok = EVERY (λ(bs,r).
    evaluate_convert FEMPTY (BytesV bs) (BaseT DecimalT) = r)
    bytes_decimal_cases
End
val () = cv_auto_trans bytes_decimal_cases_ok_def;

Theorem bytes_decimal_boundaries_eval:
  bytes_decimal_cases_ok
Proof
  simp[bytes_decimal_cases_ok_def, bytes_decimal_cases_def,
       evaluate_convert_def, cv_stdTheory.word_of_bytes_be_eq_num_of_bytes,
       dividesTheory.compute_divides] >> EVAL_TAC
QED

Theorem bytes_decimal_boundaries_cv:
  bytes_decimal_cases_ok
Proof
  CONV_TAC cv_eval
QED

(* Every legal fixed-byte length, not just bytes32; also nonzero positive
   and negative inputs at each length, with the required sign extension. *)
Theorem bytes_decimal_all_fixed_lengths_cv:
  EVERY (λm.
    evaluate_type FEMPTY (BaseT (BytesT (Fixed m))) =
      SOME (BaseTV (BytesT (Fixed m))) ∧
    valid_conversion (BaseT (BytesT (Fixed m))) (BaseT DecimalT) ∧
    evaluate_convert FEMPTY (BytesV (REPLICATE m 0w)) (BaseT DecimalT) =
      INL (DecimalV 0) ∧
    evaluate_convert FEMPTY (BytesV (REPLICATE (m - 1) 0w ++ [1w]))
      (BaseT DecimalT) = INL (DecimalV 1) ∧
    evaluate_convert FEMPTY (BytesV (REPLICATE m 255w)) (BaseT DecimalT) =
      INL (DecimalV (-1))) (GENLIST SUC 32)
Proof
  simp[evaluate_type_def, valid_conversion_def] >> CONV_TAC cv_eval
QED

Theorem bytes_decimal_builtin_boundaries_cv:
  evaluate_type_builtin empty_evaluation_context Convert (BaseT DecimalT)
    [BaseT (BytesT (Dynamic 32))] [BytesV [128w]] = INL (DecimalV (-128)) ∧
  evaluate_type_builtin empty_evaluation_context Convert (BaseT DecimalT)
    [BaseT (BytesT (Dynamic 32))] [BytesV (REPLICATE 11 0w ++ [127w] ++ REPLICATE 20 255w)] =
      INL (DecimalV 187072209578355573530071658587684226515959365500927) ∧
  evaluate_type_builtin empty_evaluation_context Convert (BaseT DecimalT)
    [BaseT (BytesT (Dynamic 32))] [BytesV (REPLICATE 11 255w ++ [128w] ++ REPLICATE 20 0w)] =
      INL (DecimalV (-187072209578355573530071658587684226515959365500928)) ∧
  evaluate_type_builtin empty_evaluation_context Convert (BaseT DecimalT)
    [BaseT (BytesT (Dynamic 32))] [BytesV (REPLICATE 11 0w ++ [128w] ++ REPLICATE 20 0w)] =
      INR (RuntimeError "bounded_decimal_op")
Proof
  simp[evaluate_type_builtin_def, get_tenv_def,
       empty_evaluation_context_def] >> CONV_TAC cv_eval
QED

(* The actual formerly rejected fixture, through the sealed success-only
   checker in both runtime and deployment modes. Its AST is unchanged. *)
val fixture_modules = rhs (concl (SIMP_CONV (srw_ss())
  [scalar_convert_bytes32_to_decimal_program_def]
  ``([(NONE, scalar_convert_bytes32_to_decimal_program)]
      : (num option # toplevel list) list)``));
val fixture_layouts =
  ``([] : (address # (storage_layout # storage_layout)) list)``;
val runtime_checked = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = fixture_layouts,
   address = ``(0w : address)``, modules = fixture_modules};
val deployment_checked = vyperCheckContractLib.check_contract
  {in_deploy = true, layouts = fixture_layouts,
   address = ``(0w : address)``, modules = fixture_modules};
val () = print "BYTES_DECIMAL_FIXTURE_CHECKER_ACCEPTED runtime+deployment hyp=0\n";

Theorem bytes_decimal_fixture_runtime_checked:
  IS_SOME (check_contract F [] (0w : address)
    [(NONE, scalar_convert_bytes32_to_decimal_program)])
Proof
  simp[scalar_convert_bytes32_to_decimal_program_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem bytes_decimal_fixture_deployment_checked:
  IS_SOME (check_contract T [] (0w : address)
    [(NONE, scalar_convert_bytes32_to_decimal_program)])
Proof
  simp[scalar_convert_bytes32_to_decimal_program_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED
