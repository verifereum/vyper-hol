(* Exact pinned-Python bytecode parity for the bare-raise fixture. *)

Theory evalCompilerBytecodeRaiseBare
Ancestors evalCompilerSubsetControlDeploy compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

Theorem raise_bare_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    raise_bare_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "raise_bare.hex")
Proof
  EVAL_TAC
QED
