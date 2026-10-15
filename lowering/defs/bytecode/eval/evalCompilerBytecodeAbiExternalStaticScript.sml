(* Exact Python-oracle bytecode checks for static external ABI fixtures. *)

Theory evalCompilerBytecodeAbiExternalStatic
Ancestors evalCompilerSubsetAbiExternal compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Theorem external_scalars_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_external_scalars_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "external_scalars.hex")
Proof
  EVAL_TAC
QED

Theorem external_struct_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_external_struct_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "external_struct.hex")
Proof
  EVAL_TAC
QED
