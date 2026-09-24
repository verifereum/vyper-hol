(* Exact pinned-Python bytecode checks for the small environment fixtures. *)

Theory evalCompilerBytecodeBuiltinsEnvCore
Ancestors evalCompilerSubsetBuiltins compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Theorem env_message_core_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    env_message_core_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "env_message_core.hex")
Proof
  EVAL_TAC
QED

Theorem env_tx_chain_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    env_tx_chain_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "env_tx_chain.hex")
Proof
  EVAL_TAC
QED
