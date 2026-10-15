(* Exact Python-oracle bytecode checks for evaluator-small scalar type-builtin fixtures. *)

Theory evalCompilerBytecodeScalarTypeBuiltins
Ancestors evalCompilerBytecodeScalarWordEval evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``type_bounds``)
    |> computeLib.add_thms
         [scalar_decimal_type_bounds_eval,
          w2n_scalar_decimal_lo_word_eval,
          w2n_scalar_decimal_hi_word_eval,
          w2i_scalar_decimal_lo_word_eval,
          w2i_scalar_decimal_hi_word_eval,
          scalar_decimal_lo_word_eq_word,
          word_eq_scalar_decimal_lo_word,
          scalar_decimal_hi_word_eq_word,
          word_eq_scalar_decimal_hi_word])

Theorem scalar_empty_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities) scalar_empty_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_empty.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_decimal_bounds_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_decimal_bounds_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_decimal_bounds.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_decimal_max_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_decimal_max_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_decimal_max.hex")
Proof
  EVAL_TAC
QED

val () = computeLib.upd_compset
  (computeLib.add_thms [compileEnvTheory.type_bounds_def])

Theorem scalar_integer_bounds_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_integer_bounds_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_integer_bounds.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_integer_min_uint8_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_integer_min_uint8_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_integer_min_uint8.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_integer_max_int256_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_integer_max_int256_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_integer_max_int256.hex")
Proof
  EVAL_TAC
QED

val () = computeLib.upd_compset
  (computeLib.add_thms [compileEnvTheory.type_bounds_def])

Theorem scalar_convert_integer_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_integer_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_integer.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_convert_address_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_address_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_address.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_convert_bytes_fixed_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_bytes_fixed_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_bytes_fixed.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_convert_uint_to_bytes32_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_uint_to_bytes32_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_uint_to_bytes32.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_convert_bytes32_to_address_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_bytes32_to_address_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_bytes32_to_address.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_convert_bytes32_to_bytes4_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_bytes32_to_bytes4_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_bytes32_to_bytes4.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_convert_bytes_dynamic_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_bytes_dynamic_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_bytes_dynamic.hex")
Proof
  EVAL_TAC
QED
