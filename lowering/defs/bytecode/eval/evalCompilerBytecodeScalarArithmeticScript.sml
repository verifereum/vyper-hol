(* Exact Python-oracle bytecode checks for evaluator-small scalar arithmetic fixtures. *)

Theory evalCompilerBytecodeScalarArithmetic
Ancestors evalCompilerBytecodeScalarWordEval evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

Theorem scalar_arith_pow_base_bound_eval:
  largest_pow_exponent 3 8 F = 5
Proof
  EVAL_TAC
QED

Theorem compile_safe_pow_u8_base3_eval:
  ∀x y.
    compile_safe_pow x y (BaseT (UintT 8)) (SOME 3) NONE =
      do too_high <- emit_op GT [y; Lit 5w];
         ok <- emit_op ISZERO [too_high];
         emit_void ASSERT [ok];
         emit_op Exp [x; y]
      od
Proof
  simp[exprLoweringTheory.compile_safe_pow_def,
       scalar_arith_pow_base_bound_eval,
       compileEnvTheory.type_bits_def, compileEnvTheory.is_signed_type_def]
QED

val () = computeLib.upd_compset
  (computeLib.add_thms
    [scalar_arith_pow_base_bound_eval, compile_safe_pow_u8_base3_eval])

val () = computeLib.upd_compset
  (computeLib.add_thms
    [scalar_decimal_type_bounds_eval,
     w2n_scalar_decimal_lo_word_eval,
     w2n_scalar_decimal_hi_word_eval])

Theorem scalar_arith_uint_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_uint.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_pow_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_pow_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_pow.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_pow_base_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_pow_base_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_pow_base.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_int_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_int_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_int.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_decimal_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_decimal_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_decimal.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_decimal_sub_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_decimal_sub_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_decimal_sub.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_decimal_mul_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_decimal_mul_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_decimal_mul.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_decimal_div_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_decimal_div_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_decimal_div.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_unsafe_uint_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_unsafe_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_unsafe_uint.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_arith_unsafe_int_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_arith_unsafe_int_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_arith_unsafe_int.hex")
Proof
  EVAL_TAC
QED
