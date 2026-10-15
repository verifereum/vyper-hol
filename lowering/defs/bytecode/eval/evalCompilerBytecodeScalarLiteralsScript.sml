(* Exact Python-oracle bytecode checks for evaluator-small scalar literal fixtures. *)

Theory evalCompilerBytecodeScalarLiterals
Ancestors evalCompilerBytecodeScalarLiteralsBytes evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
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

Theorem word_of_bytes_be_bytes32:
  (word_of_bytes_be bs : bytes32) =
    n2w (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  irule word_of_bytes_be_eq_num_of_bytes >> EVAL_TAC
QED

val () = computeLib.upd_compset
  (computeLib.add_thms [word_of_bytes_be_bytes32])

Theorem scalar_literals_bool_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literals_bool_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_bool.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_literals_int_small_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literals_int_small_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_int_small.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_literals_int_wide_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literals_int_wide_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literals_int_wide.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_literal_decimal_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_literal_decimal_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_literal_decimal.hex")
Proof
  EVAL_TAC
QED
