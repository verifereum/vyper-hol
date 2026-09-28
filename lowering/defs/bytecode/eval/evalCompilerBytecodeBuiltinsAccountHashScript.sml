(* Exact pinned-Python bytecode checks for account and block/blob hash builtins. *)

Theory evalCompilerBytecodeBuiltinsAccountHash
Ancestors evalCompilerSubsetBuiltins compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Theorem account_items_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    account_items_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "account_items.hex")
Proof
  EVAL_TAC
QED

Theorem hash_builtins_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    hash_builtins_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hash_builtins.hex")
Proof
  EVAL_TAC
QED
