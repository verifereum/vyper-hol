(* Independent checked-frontend bytecode witnesses for memory pointers merged
   by a PHI: uint2str and ternaries (IfExp) of non-word type (#561).
   Half 1 of evalCompilerPhiPointers: uint2str_arg, ifexp_dynarray,
   ifexp_bytes20, ifexp_flag, ifexp_decimal, ctl_sarray_assign.
   TOP-LEVEL: uint2str_arg_matches_python_oracle,
              ifexp_dynarray_matches_python_oracle,
              ifexp_bytes20_matches_python_oracle,
              ifexp_flag_matches_python_oracle,
              ifexp_decimal_matches_python_oracle,
              ctl_sarray_assign_matches_python_oracle. *)
Theory evalCompilerPhiPointers1
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../phi-pointers"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../phi-pointers/oracle"

(* uint2str(x): the digit buffer reached only through the result PHI stays live (a14-01, a14-02, a07-06). *)
val uint2str_arg = memoryStoreWitnessLib.evaluate fixture_root "uint2str_arg"
Theorem uint2str_arg_matches_python_oracle:
  ^(#term uint2str_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "uint2str_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation uint2str_arg))) >> EVAL_TAC
QED

(* DynArray ternary (a14-01). *)
val ifexp_dynarray = memoryStoreWitnessLib.evaluate fixture_root "ifexp_dynarray"
Theorem ifexp_dynarray_matches_python_oracle:
  ^(#term ifexp_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_dynarray))) >> EVAL_TAC
QED

(* control: bytes20 ternary stays a stack value. *)
val ifexp_bytes20 = memoryStoreWitnessLib.evaluate fixture_root "ifexp_bytes20"
Theorem ifexp_bytes20_matches_python_oracle:
  ^(#term ifexp_bytes20) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_bytes20")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_bytes20))) >> EVAL_TAC
QED

(* control: flag ternary stays a stack value. *)
val ifexp_flag = memoryStoreWitnessLib.evaluate fixture_root "ifexp_flag"
Theorem ifexp_flag_matches_python_oracle:
  ^(#term ifexp_flag) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_flag")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_flag))) >> EVAL_TAC
QED

(* control: decimal ternary stays a stack value. *)
val ifexp_decimal = memoryStoreWitnessLib.evaluate fixture_root "ifexp_decimal"
Theorem ifexp_decimal_matches_python_oracle:
  ^(#term ifexp_decimal) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ifexp_decimal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ifexp_decimal))) >> EVAL_TAC
QED

(* control: static-array local assigned from a parameter, no ternary. *)
val ctl_sarray_assign = memoryStoreWitnessLib.evaluate fixture_root "ctl_sarray_assign"
Theorem ctl_sarray_assign_matches_python_oracle:
  ^(#term ctl_sarray_assign) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctl_sarray_assign")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctl_sarray_assign))) >> EVAL_TAC
QED
