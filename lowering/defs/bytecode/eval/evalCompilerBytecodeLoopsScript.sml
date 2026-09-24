(* Exact pinned-Python bytecode parity for the fixed/dynamic loops fixture. *)

Theory evalCompilerBytecodeLoops
Ancestors evalCompilerSubsetControlDeploy compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Theorem loops_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    loops_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "loops.hex")
Proof
  EVAL_TAC
QED
