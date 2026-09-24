(* Exact Python-oracle bytecode checks for interface calls and value sending. *)

Theory evalCompilerBytecodeAbiExternalCalls
Ancestors evalCompilerSubsetAbiExternalCalls compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Theorem interface_calls_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    task090_interface_calls_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "interface_calls.hex")
Proof
  EVAL_TAC
QED

Theorem send_value_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    task090_send_value_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "send_value.hex")
Proof
  EVAL_TAC
QED
