(* Bytes-to-address conversion: left padding, big-endian decoding, and the
   strict 160-bit bound. Literal expectations are shared by kernel EVAL and CV.
   No restriction to the compiler fixture subset is added to type soundness. *)
Theory vyperBytesAddressConvertTest
Ancestors
  vyperValue vyperValueOperation vyperContext vyperTypeConversions vyperTypeSystem
  vyperTypeContract evalCompilerSubsetScalars
Libs
  cv_transLib vyperCheckContractLib

Theorem bytes_address_conversion_boundary:
  evaluate_convert tenv (BytesV bs) (BaseT AddressT) =
    let n = w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs) : bytes32) in
    if n < 2 ** 160 then INL (AddressV (n2w n))
    else INR (RuntimeError "convert bytes address")
Proof
  simp[evaluate_convert_def]
QED

Theorem bytes_address_conversion_valid:
  valid_conversion (BaseT (BytesT bd)) (BaseT AddressT)
Proof
  Cases_on `bd` >> simp[valid_conversion_def]
QED

Definition bytes_address_cases_def:
  bytes_address_cases =
  [(([] : word8 list), INL (AddressV 0w));
   ([0w], INL (AddressV 0w));
   ([1w], INL (AddressV 1w));
   ([1w; 2w], INL (AddressV 258w));
   ([1w; 2w; 3w; 4w], INL (AddressV 16909060w));
   (REPLICATE 19 0w ++ [1w], INL (AddressV 1w));
   (REPLICATE 20 0w, INL (AddressV 0w));
   (REPLICATE 21 0w, INL (AddressV 0w));
   (REPLICATE 31 0w, INL (AddressV 0w));
   (REPLICATE 32 0w, INL (AddressV 0w));
   (* The maximum address, both minimally encoded and zero-extended bytes32. *)
   (REPLICATE 20 255w,
      INL (AddressV 1461501637330902918203684832716283019655932542975w));
   (REPLICATE 12 0w ++ REPLICATE 20 255w,
      INL (AddressV 1461501637330902918203684832716283019655932542975w));
   (* 2**160 must fail, not wrap to the zero address. *)
   (1w :: REPLICATE 20 0w, INR (RuntimeError "convert bytes address"));
   (REPLICATE 11 0w ++ [1w] ++ REPLICATE 20 0w,
      INR (RuntimeError "convert bytes address"));
   (REPLICATE 32 255w, INR (RuntimeError "convert bytes address"));
   (* Each byte position distinguishes big-endian from little-endian. *)
   (REPLICATE 30 0w ++ [1w; 2w], INL (AddressV 258w));
   (REPLICATE 31 0w ++ [255w], INL (AddressV 255w))]
End
val () = cv_auto_trans bytes_address_cases_def;

Definition bytes_address_cases_ok_def:
  bytes_address_cases_ok = EVERY (λ(bs,r).
    evaluate_convert FEMPTY (BytesV bs) (BaseT AddressT) = r)
    bytes_address_cases
End
val () = cv_auto_trans bytes_address_cases_ok_def;

Theorem bytes_address_boundaries_eval:
  bytes_address_cases_ok
Proof
  simp[bytes_address_cases_ok_def, bytes_address_cases_def,
       evaluate_convert_def, cv_stdTheory.word_of_bytes_be_eq_num_of_bytes,
       dividesTheory.compute_divides] >> EVAL_TAC
QED

Theorem bytes_address_boundaries_cv:
  bytes_address_cases_ok
Proof
  CONV_TAC cv_eval
QED

(* Every legal fixed-byte length, not only bytes32, is accepted by typing
   and converts its zero encoding to the zero address. *)
Theorem bytes_address_all_fixed_lengths_cv:
  EVERY (λm.
    evaluate_type FEMPTY (BaseT (BytesT (Fixed m))) =
      SOME (BaseTV (BytesT (Fixed m))) ∧
    valid_conversion (BaseT (BytesT (Fixed m))) (BaseT AddressT) ∧
    evaluate_convert FEMPTY (BytesV (REPLICATE m 0w)) (BaseT AddressT) =
      INL (AddressV 0w)) (GENLIST SUC 32)
Proof
  simp[evaluate_type_def, valid_conversion_def] >> CONV_TAC cv_eval
QED

Theorem bytes_address_builtin_boundaries_cv:
  evaluate_type_builtin empty_evaluation_context Convert (BaseT AddressT)
    [BaseT (BytesT (Fixed 32))] [BytesV (REPLICATE 32 0w)] = INL (AddressV 0w) ∧
  evaluate_type_builtin empty_evaluation_context Convert (BaseT AddressT)
    [BaseT (BytesT (Fixed 32))] [BytesV (REPLICATE 12 0w ++ REPLICATE 20 255w)] =
      INL (AddressV 1461501637330902918203684832716283019655932542975w) ∧
  evaluate_type_builtin empty_evaluation_context Convert (BaseT AddressT)
    [BaseT (BytesT (Fixed 32))] [BytesV (REPLICATE 11 0w ++ [1w] ++ REPLICATE 20 0w)] =
      INR (RuntimeError "convert bytes address")
Proof
  simp[evaluate_type_builtin_def, get_tenv_def,
       empty_evaluation_context_def] >> CONV_TAC cv_eval
QED

(* Extract32 retains its independent zero-prefix clamp and error message;
   the two address boundaries agree with Convert on success versus failure. *)
Theorem extract32_address_boundaries_eval:
  evaluate_extract32 (REPLICATE 12 0w ++ REPLICATE 20 255w) 0 AddressT =
    INL (AddressV 1461501637330902918203684832716283019655932542975w) ∧
  evaluate_extract32 (REPLICATE 11 0w ++ [1w] ++ REPLICATE 20 0w)
    0 AddressT = INR (RuntimeError "evaluate_extract32 address clamp")
Proof
  simp[evaluate_extract32_def, evaluate_convert_def,
       cv_stdTheory.word_of_bytes_be_eq_num_of_bytes,
       dividesTheory.compute_divides] >> EVAL_TAC
QED

(* Exercise the repository's success-only checker against the ACTUAL unchanged
   formerly rejected fixture, in runtime and deployment modes. Unfolding only
   its two fixture definitions keeps the core checker's compset sealed. *)
val fixture_modules = rhs (concl (SIMP_CONV (srw_ss())
  [scalar_convert_bytes32_to_address_program_def, scalar_convert_fn_def]
  ``([(NONE, scalar_convert_bytes32_to_address_program)]
      : (num option # toplevel list) list)``));
val fixture_layouts =
  ``([] : (address # (storage_layout # storage_layout)) list)``;
val runtime_checked = vyperCheckContractLib.check_contract
  {in_deploy = false, layouts = fixture_layouts,
   address = ``(0w : address)``, modules = fixture_modules};
val deployment_checked = vyperCheckContractLib.check_contract
  {in_deploy = true, layouts = fixture_layouts,
   address = ``(0w : address)``, modules = fixture_modules};
val () = print "BYTES_ADDRESS_FIXTURE_CHECKER_ACCEPTED runtime+deployment hyp=0\n";

Theorem bytes_address_fixture_runtime_checked:
  IS_SOME (check_contract F [] (0w : address)
    [(NONE, scalar_convert_bytes32_to_address_program)])
Proof
  simp[scalar_convert_bytes32_to_address_program_def, scalar_convert_fn_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem bytes_address_fixture_deployment_checked:
  IS_SOME (check_contract T [] (0w : address)
    [(NONE, scalar_convert_bytes32_to_address_program)])
Proof
  simp[scalar_convert_bytes32_to_address_program_def, scalar_convert_fn_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED
