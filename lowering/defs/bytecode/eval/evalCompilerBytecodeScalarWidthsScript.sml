(* Exact Python-oracle bytecode checks for evaluator-small scalar width fixtures. *)

Theory evalCompilerBytecodeScalarWidths
Ancestors evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

Theorem scalar_widths_uint_low_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_widths_uint_low_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_widths_uint_low.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_widths_uint_high_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_widths_uint_high_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_widths_uint_high.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_widths_int_low_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_widths_int_low_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_widths_int_low.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_widths_int_high_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_widths_int_high_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_widths_int_high.hex")
Proof
  EVAL_TAC
QED
