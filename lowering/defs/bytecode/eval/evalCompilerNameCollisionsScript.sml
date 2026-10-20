(* Independent checked-frontend bytecode witnesses for user identifiers that
   used to collide with compiler-internal compile_env entries (#557).
   TOP-LEVEL: nm_arg_return_pc_matches_python_oracle,
              nm_ext_arg_return_pc_matches_python_oracle. *)
Theory evalCompilerNameCollisions
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../name-collisions"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../name-collisions/oracle"

(* a04-04: an internal argument named __return_pc__ is the user's value, not
   the return address. *)
val nm_arg_return_pc = memoryStoreWitnessLib.evaluate fixture_root "nm_arg_return_pc"
Theorem nm_arg_return_pc_matches_python_oracle:
  ^(#term nm_arg_return_pc) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_arg_return_pc")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_arg_return_pc))) >> EVAL_TAC
QED

(* a04-04: an external argument named __return_pc__ does not make the
   function's `return` take the internal RET path. *)
val nm_ext_arg_return_pc = memoryStoreWitnessLib.evaluate fixture_root "nm_ext_arg_return_pc"
Theorem nm_ext_arg_return_pc_matches_python_oracle:
  ^(#term nm_ext_arg_return_pc) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_ext_arg_return_pc")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_ext_arg_return_pc))) >> EVAL_TAC
QED
