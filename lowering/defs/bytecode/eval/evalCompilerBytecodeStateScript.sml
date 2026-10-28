(*
 * Exact Python-oracle bytecode checks for state-access subset fixtures.
 *)

Theory evalCompilerBytecodeState
Ancestors evalCompilerSubsetState compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerClosedFixtureEvalLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../python-o1-no-asm-opt/storage_array.hex",
   "../python-o1-no-asm-opt/storage_dynarray.hex",
   "../python-o1-no-asm-opt/storage_mapping.hex",
   "../python-o1-no-asm-opt/storage_scalar_loop.hex",
   "../python-o1-no-asm-opt/storage_struct.hex",
   "../python-o1-no-asm-opt/transient_scalar.hex"]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

val () = compilerClosedFixtureEvalLib.cache_compile
  "storage_scalar_loop" ``storage_scalar_loop_program``

Theorem storage_scalar_loop_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_scalar_loop_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_scalar_loop.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "storage_array" ``storage_array_program``

Theorem storage_array_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_array_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_array.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "storage_dynarray" ``storage_dynarray_program``

Theorem storage_dynarray_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_dynarray_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_dynarray.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "storage_mapping" ``storage_mapping_program``

Theorem storage_mapping_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_mapping_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_mapping.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "storage_struct" ``storage_struct_program``

Theorem storage_struct_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    storage_struct_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_struct.hex")
Proof
  EVAL_TAC
QED

val () = compilerClosedFixtureEvalLib.cache_compile
  "transient_scalar" ``transient_scalar_program``

Theorem transient_scalar_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    transient_scalar_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "transient_scalar.hex")
Proof
  EVAL_TAC
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("STATE_PUBLIC_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "state-access parity has kernel assumptions or admission tags"
end) [("storage_scalar_loop_matches_python_oracle",storage_scalar_loop_matches_python_oracle),
       ("storage_array_matches_python_oracle",storage_array_matches_python_oracle),
       ("storage_dynarray_matches_python_oracle",storage_dynarray_matches_python_oracle),
       ("storage_mapping_matches_python_oracle",storage_mapping_matches_python_oracle),
       ("storage_struct_matches_python_oracle",storage_struct_matches_python_oracle),
       ("transient_scalar_matches_python_oracle",transient_scalar_matches_python_oracle)]
