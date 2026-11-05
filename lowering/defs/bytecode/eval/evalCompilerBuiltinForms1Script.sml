(* Independent checked-frontend bytecode witnesses for builtin forms (#566):
   ceil (a07-11) and floor, with a bytes32 slice (a07-07).
   Part 1 of evalCompilerBuiltinForms.
   TOP-LEVEL: ceil_dec_matches_python_oracle,
              floor_dec_matches_python_oracle,
              slice_bytes32_matches_python_oracle. *)
Theory evalCompilerBuiltinForms1
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../builtin-forms"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../builtin-forms/oracle"

(* ceil(x): slt(x, 0) selects x or x + 10**10 - 1. *)
val ceil_dec = memoryStoreWitnessLib.evaluate fixture_root "ceil_dec"
Theorem ceil_dec_matches_python_oracle:
  ^(#term ceil_dec) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ceil_dec")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ceil_dec))) >> EVAL_TAC
QED

(* control: floor(x). *)
val floor_dec = memoryStoreWitnessLib.evaluate fixture_root "floor_dec"
Theorem floor_dec_matches_python_oracle:
  ^(#term floor_dec) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "floor_dec")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation floor_dec))) >> EVAL_TAC
QED

(* slice of a bytes32: a 32-byte scratch and the literal length 32. *)
val slice_bytes32 = memoryStoreWitnessLib.evaluate fixture_root "slice_bytes32"
Theorem slice_bytes32_matches_python_oracle:
  ^(#term slice_bytes32) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "slice_bytes32")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation slice_bytes32))) >> EVAL_TAC
QED
