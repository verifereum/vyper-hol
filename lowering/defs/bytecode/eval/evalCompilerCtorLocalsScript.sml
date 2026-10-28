(* Independent checked-frontend bytecode witnesses for locals declared in a
   constructor body: each gets its own ALLOCA, as in Python Vyper, rather
   than a fixed MemLoc address.
   TOP-LEVEL: ctor_local_word_matches_python_oracle,
              ctor_arg_local_array_matches_python_oracle,
              ctor_local_across_call_matches_python_oracle,
              ctor_for_range_matches_python_oracle,
              ctor_arg_ifelse_local_matches_python_oracle. *)
Theory evalCompilerCtorLocals
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../ctor-locals"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../ctor-locals/oracle"

(* A constructor without arguments: its first local used to sit at address
   0. *)
val ctor_local_word = memoryStoreWitnessLib.evaluate fixture_root "ctor_local_word"
Theorem ctor_local_word_matches_python_oracle:
  ^(#term ctor_local_word) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctor_local_word")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctor_local_word))) >> EVAL_TAC
QED

(* A local array next to a constructor argument. *)
val ctor_arg_local_array =
  memoryStoreWitnessLib.evaluate fixture_root "ctor_arg_local_array"
Theorem ctor_arg_local_array_matches_python_oracle:
  ^(#term ctor_arg_local_array) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctor_arg_local_array")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctor_arg_local_array))) >> EVAL_TAC
QED

(* A local live across an internal call from the constructor. *)
val ctor_local_across_call =
  memoryStoreWitnessLib.evaluate fixture_root "ctor_local_across_call"
Theorem ctor_local_across_call_matches_python_oracle:
  ^(#term ctor_local_across_call) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctor_local_across_call")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctor_local_across_call))) >> EVAL_TAC
QED

(* A range-loop variable in the constructor. *)
val ctor_for_range = memoryStoreWitnessLib.evaluate fixture_root "ctor_for_range"
Theorem ctor_for_range_matches_python_oracle:
  ^(#term ctor_for_range) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctor_for_range")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctor_for_range))) >> EVAL_TAC
QED

(* A local computed from a constructor argument and read in both branches of
   an if/else. *)
val ctor_arg_ifelse_local =
  memoryStoreWitnessLib.evaluate fixture_root "ctor_arg_ifelse_local"
Theorem ctor_arg_ifelse_local_matches_python_oracle:
  ^(#term ctor_arg_ifelse_local) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctor_arg_ifelse_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctor_arg_ifelse_local))) >> EVAL_TAC
QED
