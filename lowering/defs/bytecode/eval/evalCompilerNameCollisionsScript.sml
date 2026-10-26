(* Independent checked-frontend bytecode witnesses for user identifiers that
   used to collide with compiler-internal compile_env entries (#557).
   TOP-LEVEL: nm_arg_return_pc_matches_python_oracle,
              nm_ext_arg_return_pc_matches_python_oracle,
              nm_arg_storage_matches_python_oracle,
              nm_local_storage_types_matches_python_oracle,
              nm_transient_local_matches_python_oracle,
              nm_redeclared_local_matches_python_oracle,
              nm_redeclared_loop_var_matches_python_oracle. *)
Theory evalCompilerNameCollisions
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../name-collisions/oracle/nm_arg_return_pc.json",
   "../name-collisions/oracle/nm_arg_return_pc.hex",
   "../name-collisions/oracle/nm_ext_arg_return_pc.json",
   "../name-collisions/oracle/nm_ext_arg_return_pc.hex",
   "../name-collisions/oracle/nm_arg_storage.json",
   "../name-collisions/oracle/nm_arg_storage.hex",
   "../name-collisions/oracle/nm_local_storage_types.json",
   "../name-collisions/oracle/nm_local_storage_types.hex",
   "../name-collisions/oracle/nm_transient_local.json",
   "../name-collisions/oracle/nm_transient_local.hex",
   "../name-collisions/oracle/nm_redeclared_local.json",
   "../name-collisions/oracle/nm_redeclared_local.hex",
   "../name-collisions/oracle/nm_redeclared_loop_var.json",
   "../name-collisions/oracle/nm_redeclared_loop_var.hex",
   "../name-collisions/oracle/ctl_local_internal.json",
   "../name-collisions/oracle/ctl_local_internal.hex",
   "../name-collisions/oracle/nm_local_return_buf.json",
   "../name-collisions/oracle/nm_local_return_buf.hex"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
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

(* #644: a local re-declared with another type in a disjoint block gets its
   own ALLOCA of its own size in each block (160 bytes for Bytes[100], 32 for
   uint256), not one shared allocation sized for the last declaration. *)
val nm_redeclared_local = memoryStoreWitnessLib.evaluate fixture_root "nm_redeclared_local"
Theorem nm_redeclared_local_matches_python_oracle:
  ^(#term nm_redeclared_local) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_redeclared_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_redeclared_local))) >> EVAL_TAC
QED

(* #644: a loop variable declared again with another type in a later loop gets
   its own ALLOCA, emitted after the range bound and the iterated array are
   evaluated, as in Python. *)
val nm_redeclared_loop_var = memoryStoreWitnessLib.evaluate fixture_root "nm_redeclared_loop_var"
Theorem nm_redeclared_loop_var_matches_python_oracle:
  ^(#term nm_redeclared_loop_var) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_redeclared_loop_var")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_redeclared_loop_var))) >> EVAL_TAC
QED

(* #545: declaration-site ALLOCAs apply inside internal functions, including
   user locals named like compiler bookkeeping. *)
val ctl_local_internal = memoryStoreWitnessLib.evaluate fixture_root "ctl_local_internal"
Theorem ctl_local_internal_matches_python_oracle:
  ^(#term ctl_local_internal) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctl_local_internal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctl_local_internal))) >> EVAL_TAC
QED

val nm_local_return_buf = memoryStoreWitnessLib.evaluate fixture_root "nm_local_return_buf"
Theorem nm_local_return_buf_matches_python_oracle:
  ^(#term nm_local_return_buf) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nm_local_return_buf")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nm_local_return_buf))) >> EVAL_TAC
QED
