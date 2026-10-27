(* Opt-in rollup of all 101 exact pinned-Python bytecode comparisons.
   Each public parity theorem is proved by plain EVAL_TAC. *)
Theory evalCompilerBytecodeParity
Ancestors
  evalCompilerRange
  evalCompilerAllocationBudget
  evalCompilerAllocationBudgetCost
  evalCompilerBytecode
  evalCompilerBytecodeControl
  evalCompilerBytecodeState
  evalCompilerBytecodeAbiExternalStatic
  evalCompilerBytecodeAbiExternalArrays
  evalCompilerBytecodeAbiExternalDynamic
  evalCompilerBytecodeAbiEvents
  evalCompilerBytecodeAbiInternalCalls
  evalCompilerBytecodeAbiExternalCalls
  evalCompilerBytecodeAbiStatic
  evalCompilerBytecodeAbiDynamic
  evalCompilerBytecodeFunctionModes
  evalCompilerBytecodeAssertRaise
  evalCompilerBytecodeAssertReason
  evalCompilerBytecodeRaiseBare
  evalCompilerBytecodeRaiseReason
  evalCompilerBytecodeLoops
  evalCompilerBytecodeScalarWidths
  evalCompilerBytecodeScalarLiterals
  evalCompilerBytecodeScalarLiteralsBytes
  evalCompilerBytecodeScalarArithmetic
  evalCompilerBytecodeScalarIntegerMin
  evalCompilerBytecodeScalarDecimalMinPipeline
  evalCompilerBytecodeScalarConvertDecimal
  evalCompilerBytecodeScalarConvertIntToDecimal
  evalCompilerBytecodeScalarConvertBytes32ToDecimal
  evalCompilerBytecodeScalarOperators
  evalCompilerBytecodeScalarTypeBuiltins
  evalCompilerBytecodeScalarWeiModular
  evalCompilerBytecodeBuiltinsEnvCore
  evalCompilerBytecodeBuiltinsEnvBlock
  evalCompilerBytecodeBuiltinsAccountHash
  evalCompilerBytecodeBuiltinsEc

(* Pin the qualified public identities: a count alone could accept a missing
   fixture replaced by an unrelated equality. This is an audit manifest, not
   an evaluation rewrite set; compiler expressions, oracle bytes and proofs
   remain in their independent fixture theories. *)
val expected_parity_names = List.concat (map (fn (thy, fixtures) =>
  map (fn fixture => thy ^ "." ^ fixture ^ "_matches_python_oracle") fixtures)
  [
   ("evalCompilerBytecode", [
      "add_arg", "deploy_storage", "empty", "event_log",
      "indexed_event_log", "local_uint", "noop", "return_arg",
      "return_uint", "storage_read", "storage_write", "two_external"]),
   ("evalCompilerBytecodeAbiDynamic", ["abi_dynamic"]),
   ("evalCompilerBytecodeAbiEvents", ["mixed_event_types"]),
   ("evalCompilerBytecodeAbiExternalArrays", ["external_arrays"]),
   ("evalCompilerBytecodeAbiExternalCalls", ["interface_calls", "send_value"]),
   ("evalCompilerBytecodeAbiExternalDynamic", ["external_dynamic"]),
   ("evalCompilerBytecodeAbiExternalStatic", ["external_scalars", "external_struct"]),
   ("evalCompilerBytecodeAbiInternalCalls", [
      "internal_bytes_call", "internal_struct_call", "internal_tuple_call"]),
   ("evalCompilerBytecodeAbiStatic", ["abi_static"]),
   ("evalCompilerBytecodeAssertRaise", ["assert_bare"]),
   ("evalCompilerBytecodeAssertReason", ["assert_reason"]),
   ("evalCompilerBytecodeBuiltinsAccountHash", ["account_items", "hash_builtins"]),
   ("evalCompilerBytecodeBuiltinsEc", ["ec_builtins"]),
   ("evalCompilerBytecodeBuiltinsEnvBlock", ["env_block"]),
   ("evalCompilerBytecodeBuiltinsEnvCore", ["env_message_core", "env_tx_chain"]),
   ("evalCompilerBytecodeControl", [
      "for_accum", "for_break", "for_continue", "for_pass",
      "hashmap_read", "hashmap_write", "if_bool", "if_join",
      "internal_call_arg", "internal_call", "mixed_event_log"]),
   ("evalCompilerBytecodeFunctionModes", ["function_modes"]),
   ("evalCompilerBytecodeLoops", ["loops"]),
   ("evalCompilerBytecodeRaiseBare", ["raise_bare"]),
   ("evalCompilerBytecodeRaiseReason", ["raise_reason"]),
   ("evalCompilerBytecodeScalarArithmetic", [
      "scalar_arith_decimal_div", "scalar_arith_decimal",
      "scalar_arith_decimal_mul", "scalar_arith_decimal_sub",
      "scalar_arith_int", "scalar_arith_pow_base", "scalar_arith_pow",
      "scalar_arith_uint", "scalar_arith_unsafe_int", "scalar_arith_unsafe_uint"]),
   ("evalCompilerBytecodeScalarConvertBytes32ToDecimal", ["scalar_convert_bytes32_to_decimal"]),
   ("evalCompilerBytecodeScalarConvertDecimal", ["scalar_convert_decimal"]),
   ("evalCompilerBytecodeScalarConvertIntToDecimal", ["scalar_convert_int_to_decimal"]),
   ("evalCompilerBytecodeScalarDecimalMinPipeline", ["scalar_decimal_min"]),
   ("evalCompilerBytecodeScalarIntegerMin", ["scalar_integer_min_int256"]),
   ("evalCompilerBytecodeScalarLiterals", [
      "scalar_literal_decimal", "scalar_literals_bool",
      "scalar_literals_int_small", "scalar_literals_int_wide"]),
   ("evalCompilerBytecodeScalarLiteralsBytes", ["scalar_literals_bytes"]),
   ("evalCompilerBytecodeScalarOperators", [
      "scalar_bits", "scalar_compare_eq", "scalar_compare_order_int",
      "scalar_compare_order_uint", "scalar_minmax_int", "scalar_minmax_uint",
      "scalar_shifts", "scalar_unary"]),
   ("evalCompilerBytecodeScalarTypeBuiltins", [
      "scalar_convert_address", "scalar_convert_bytes32_to_address",
      "scalar_convert_bytes32_to_bytes4", "scalar_convert_bytes_dynamic",
      "scalar_convert_bytes_fixed", "scalar_convert_integer",
      "scalar_convert_uint_to_bytes32", "scalar_decimal_bounds",
      "scalar_decimal_max", "scalar_empty", "scalar_integer_bounds",
      "scalar_integer_max_int256", "scalar_integer_min_uint8"]),
   ("evalCompilerBytecodeScalarWeiModular", [
      "scalar_modular", "scalar_wei_large", "scalar_wei_small"]),
   ("evalCompilerBytecodeScalarWidths", [
      "scalar_widths_int_high", "scalar_widths_int_low",
      "scalar_widths_uint_high", "scalar_widths_uint_low"]),
   ("evalCompilerBytecodeState", [
      "storage_array", "storage_dynarray", "storage_mapping",
      "storage_scalar_loop", "storage_struct", "transient_scalar"])
  ]);

(* Inspect actual saved objects, including cached/checkpointed theorems.
   No E, C, or replacement hypothesis is permitted. DISK_THM is an ordinary
   storage marker; all other oracles and all axioms are forbidden. *)
val parity_theorems = List.filter
  (fn (name, th) =>
    String.isSuffix "_matches_python_oracle" name andalso
    boolSyntax.is_eq (Thm.concl th) andalso
    same_const (#1 (strip_comb (lhs (Thm.concl th)))) ``compile_vyper``)
  (List.concat (map (fn thy =>
    map (fn (name, th) => (thy ^ "." ^ name, th)) (DB.theorems thy))
    (Theory.ancestry "-")));
val () = if length expected_parity_names = 101 andalso
            length parity_theorems = 101 andalso
            List.all (fn name =>
              length (List.filter (fn expected => expected = name)
                expected_parity_names) = 1 andalso
              length (List.filter (fn (saved, _) => saved = name)
                parity_theorems) = 1) expected_parity_names then ()
         else raise Fail "expected exactly the 101 public bytecode parity identities";
fun permissible_parity_tag th =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in null axioms andalso List.all (fn s => s = "DISK_THM") oracles end;
val () = List.app
  (fn (name, th) =>
    if not (permissible_parity_tag th) then
      raise Fail ("admitted parity theorem: " ^ name)
    else if not (null (Thm.hyp th)) then
      raise Fail ("kernel hypotheses in parity theorem: " ^ name)
    else print ("PARITY_KERNEL_CLOSED " ^ name ^ " hyp=0\n"))
  parity_theorems;
