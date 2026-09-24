(*
 * Exact Python-oracle bytecode checks for state-access subset fixtures.
 *)

Theory evalCompilerBytecodeState
Ancestors evalCompilerSubsetState compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Theorem storage_scalar_loop_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    storage_scalar_loop_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_scalar_loop.hex")
Proof
  EVAL_TAC
QED

Theorem storage_array_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    storage_array_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_array.hex")
Proof
  EVAL_TAC
QED

Theorem storage_dynarray_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    storage_dynarray_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_dynarray.hex")
Proof
  EVAL_TAC
QED

Theorem storage_mapping_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    storage_mapping_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_mapping.hex")
Proof
  EVAL_TAC
QED

Theorem storage_struct_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    storage_struct_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_struct.hex")
Proof
  EVAL_TAC
QED

Theorem transient_scalar_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    transient_scalar_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "transient_scalar.hex")
Proof
  EVAL_TAC
QED
