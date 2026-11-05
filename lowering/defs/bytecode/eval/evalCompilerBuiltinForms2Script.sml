(* Independent checked-frontend bytecode witnesses for builtin forms (#566):
   concat (a07-05): the running offset kept in a 64-byte memory temporary.
   Part 2 of evalCompilerBuiltinForms.
   TOP-LEVEL: uint2str_local_matches_python_oracle. *)
Theory evalCompilerBuiltinForms2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../builtin-forms"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../builtin-forms/oracle"

(* concat of a literal and uint2str. *)
val uint2str_local = memoryStoreWitnessLib.evaluate fixture_root "uint2str_local"
Theorem uint2str_local_matches_python_oracle:
  ^(#term uint2str_local) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "uint2str_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation uint2str_local))) >> EVAL_TAC
QED
