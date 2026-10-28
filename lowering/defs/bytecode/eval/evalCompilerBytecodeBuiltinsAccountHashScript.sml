(* Exact pinned-Python bytecode checks for account and block/blob hash builtins. *)

Theory evalCompilerBytecodeBuiltinsAccountHash
Ancestors evalCompilerBytecodeHashBuiltinsStages evalCompilerBytecodeAccountItemsStages evalCompilerSubsetBuiltins compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/account_items.hex",
   "../python-o1-no-asm-opt/hash_builtins.hex"]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20
val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeAccountItemsStages"
val () = evalCompilerBytecodeLib.restore_stage_values
  "evalCompilerBytecodeHashBuiltinsStages"

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
