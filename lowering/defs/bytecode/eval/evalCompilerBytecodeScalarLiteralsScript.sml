(* Exact Python-oracle bytecode checks for evaluator-small scalar literal fixtures. *)

Theory evalCompilerBytecodeScalarLiterals
Ancestors evalCompilerBytecodeScalarLiteralDecimalStages evalCompilerBytecodeScalarLiteralsIntWideStages evalCompilerBytecodeScalarLiteralsIntSmallStages evalCompilerBytecodeScalarLiteralsBoolStages evalCompilerBytecodeScalarLiteralsBytes evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/scalar_literal_decimal.hex",
   "../python-o1-no-asm-opt/scalar_literals_bool.hex",
   "../python-o1-no-asm-opt/scalar_literals_int_small.hex",
   "../python-o1-no-asm-opt/scalar_literals_int_wide.hex"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

Theorem i2w_neg_num:
  ∀n. i2w (-&n) = -n2w n
Proof
  Cases_on `n` >> simp[i2w_def]
QED

val () = computeLib.upd_compset (computeLib.add_thms [i2w_neg_num])

val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarLiteralsBoolStages"

Theorem scalar_literals_bool_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literals_bool_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_bool.hex")
Proof
  EVAL_TAC
QED

val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarLiteralsIntSmallStages"

Theorem scalar_literals_int_small_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literals_int_small_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_int_small.hex")
Proof
  EVAL_TAC
QED

val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarLiteralsIntWideStages"

Theorem scalar_literals_int_wide_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literals_int_wide_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_int_wide.hex")
Proof
  EVAL_TAC
QED

val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeScalarLiteralDecimalStages"

Theorem scalar_literal_decimal_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literal_decimal_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literal_decimal.hex")
Proof
  EVAL_TAC
QED
