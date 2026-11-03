(* A widened Concat destination must not enlarge its intermediate buffer. *)
Theory evalCompilerConcatWidened
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../concat-widened/sources", "../concat-widened/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])

val fixture_root = "../concat-widened/oracle"
val concat_wide_local_program =
  memoryStoreWitnessLib.program fixture_root "concat_wide_local"
val concat_wide_local_term =
  memoryStoreWitnessLib.compile_term concat_wide_local_program
val concat_wide_local_evaluation = EVAL concat_wide_local_term

Theorem concat_wide_local_matches_python_oracle:
  ^concat_wide_local_term =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "concat_wide_local")
Proof
  CONV_TAC (LAND_CONV (K concat_wide_local_evaluation)) >> EVAL_TAC
QED
