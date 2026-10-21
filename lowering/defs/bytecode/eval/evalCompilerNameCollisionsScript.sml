(* Independent checked-frontend bytecode witnesses for user identifiers that
   used to collide with compiler-internal compile_env entries (#557).
   TOP-LEVEL: nm_arg_return_pc_matches_python_oracle,
              nm_ext_arg_return_pc_matches_python_oracle,
              nm_arg_storage_matches_python_oracle,
              nm_local_storage_types_matches_python_oracle,
              nm_transient_local_matches_python_oracle. *)
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

(* a04-03: an external argument named like a storage variable does not
   replace the storage slot of self.stored. *)
val nm_arg_storage = memoryStoreWitnessLib.evaluate fixture_root "nm_arg_storage"
Theorem nm_arg_storage_matches_python_oracle:
  ^(#term nm_arg_storage) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_arg_storage")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_arg_storage))) >> EVAL_TAC
QED

(* a04-03: a uint256 local named like a DynArray storage variable keeps
   its own location, type and capacity. *)
val nm_local_storage_types = memoryStoreWitnessLib.evaluate fixture_root "nm_local_storage_types"
Theorem nm_local_storage_types_matches_python_oracle:
  ^(#term nm_local_storage_types) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_local_storage_types")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_local_storage_types))) >> EVAL_TAC
QED

(* a04-03: a local named like a transient variable does not replace its
   transient slot. *)
val nm_transient_local = memoryStoreWitnessLib.evaluate fixture_root "nm_transient_local"
Theorem nm_transient_local_matches_python_oracle:
  ^(#term nm_transient_local) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_transient_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_transient_local))) >> EVAL_TAC
QED
