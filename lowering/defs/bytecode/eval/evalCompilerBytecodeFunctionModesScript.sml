(* Exact pinned-Python bytecode parity for the function-modes/deployment fixture. *)

Theory evalCompilerBytecodeFunctionModes
Ancestors evalCompilerBytecodeFunctionModesStages evalCompilerSubsetControlDeploy compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/function_modes.hex"]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20
val () = evalCompilerBytecodeLib.restore_stage_values "evalCompilerBytecodeFunctionModesStages"

Theorem function_modes_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    function_modes_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "function_modes.hex")
Proof
  EVAL_TAC
QED
