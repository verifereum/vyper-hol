(* Exact Python-oracle bytecode checks for evaluator-small scalar type-builtin fixtures. *)

Theory evalCompilerBytecodeScalarTypeBuiltins
Ancestors evalCompilerBytecodeScalarWordEval evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerClosedFixtureEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/scalar_convert_address.hex",
   "../python-o1-no-asm-opt/scalar_convert_bytes32_to_address.hex",
   "../python-o1-no-asm-opt/scalar_convert_bytes32_to_bytes4.hex",
   "../python-o1-no-asm-opt/scalar_convert_bytes_dynamic.hex",
   "../python-o1-no-asm-opt/scalar_convert_bytes_fixed.hex",
   "../python-o1-no-asm-opt/scalar_convert_integer.hex",
   "../python-o1-no-asm-opt/scalar_convert_uint_to_bytes32.hex",
   "../python-o1-no-asm-opt/scalar_decimal_bounds.hex",
   "../python-o1-no-asm-opt/scalar_decimal_max.hex",
   "../python-o1-no-asm-opt/scalar_empty.hex",
   "../python-o1-no-asm-opt/scalar_integer_bounds.hex",
   "../python-o1-no-asm-opt/scalar_integer_max_int256.hex",
   "../python-o1-no-asm-opt/scalar_integer_min_uint8.hex"]
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

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_empty" ``scalar_empty_program``

Theorem scalar_empty_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities) scalar_empty_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_empty.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_decimal_bounds" ``scalar_decimal_bounds_program``

Theorem scalar_decimal_bounds_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_decimal_bounds_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_decimal_bounds.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_decimal_max" ``scalar_decimal_max_program``

Theorem scalar_decimal_max_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_decimal_max_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_decimal_max.hex")
Proof
  EVAL_TAC
QED

val () = computeLib.upd_compset
  (computeLib.add_thms [compileEnvTheory.type_bounds_def])

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_integer_bounds" ``scalar_integer_bounds_program``

Theorem scalar_integer_bounds_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_integer_bounds_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_integer_bounds.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_integer_min_uint8" ``scalar_integer_min_uint8_program``

Theorem scalar_integer_min_uint8_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_integer_min_uint8_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_integer_min_uint8.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_integer_max_int256" ``scalar_integer_max_int256_program``

Theorem scalar_integer_max_int256_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_integer_max_int256_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_integer_max_int256.hex")
Proof
  EVAL_TAC
QED

val () = computeLib.upd_compset
  (computeLib.add_thms [compileEnvTheory.type_bounds_def])

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_convert_integer" ``scalar_convert_integer_program``

Theorem scalar_convert_integer_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_integer_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_integer.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_convert_address" ``scalar_convert_address_program``

Theorem scalar_convert_address_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_address_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_address.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_convert_bytes_fixed" ``scalar_convert_bytes_fixed_program``

Theorem scalar_convert_bytes_fixed_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_bytes_fixed_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_bytes_fixed.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_convert_uint_to_bytes32" ``scalar_convert_uint_to_bytes32_program``

Theorem scalar_convert_uint_to_bytes32_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_uint_to_bytes32_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_uint_to_bytes32.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_convert_bytes32_to_address" ``scalar_convert_bytes32_to_address_program``

Theorem scalar_convert_bytes32_to_address_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_bytes32_to_address_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_bytes32_to_address.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_convert_bytes32_to_bytes4" ``scalar_convert_bytes32_to_bytes4_program``

Theorem scalar_convert_bytes32_to_bytes4_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_bytes32_to_bytes4_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_bytes32_to_bytes4.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "scalar_convert_bytes_dynamic" ``scalar_convert_bytes_dynamic_program``

Theorem scalar_convert_bytes_dynamic_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_bytes_dynamic_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_bytes_dynamic.hex")
Proof
  EVAL_TAC
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("SCALAR_TYPE_BUILTINS_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "type-builtin parity has kernel assumptions or admission tags"
end) [("scalar_empty_matches_python_oracle",scalar_empty_matches_python_oracle),
       ("scalar_decimal_bounds_matches_python_oracle",scalar_decimal_bounds_matches_python_oracle),
       ("scalar_decimal_max_matches_python_oracle",scalar_decimal_max_matches_python_oracle),
       ("scalar_integer_bounds_matches_python_oracle",scalar_integer_bounds_matches_python_oracle),
       ("scalar_integer_min_uint8_matches_python_oracle",scalar_integer_min_uint8_matches_python_oracle),
       ("scalar_integer_max_int256_matches_python_oracle",scalar_integer_max_int256_matches_python_oracle),
       ("scalar_convert_integer_matches_python_oracle",scalar_convert_integer_matches_python_oracle),
       ("scalar_convert_address_matches_python_oracle",scalar_convert_address_matches_python_oracle),
       ("scalar_convert_bytes_fixed_matches_python_oracle",scalar_convert_bytes_fixed_matches_python_oracle),
       ("scalar_convert_uint_to_bytes32_matches_python_oracle",scalar_convert_uint_to_bytes32_matches_python_oracle),
       ("scalar_convert_bytes32_to_address_matches_python_oracle",scalar_convert_bytes32_to_address_matches_python_oracle),
       ("scalar_convert_bytes32_to_bytes4_matches_python_oracle",scalar_convert_bytes32_to_bytes4_matches_python_oracle),
       ("scalar_convert_bytes_dynamic_matches_python_oracle",scalar_convert_bytes_dynamic_matches_python_oracle)]
