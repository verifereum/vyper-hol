(* Independent checked-frontend bytecode witnesses for builtin forms, part 2
   of evalCompilerBuiltinForms.  Its one fixture, uint2str_local, is out of
   parity: see ../pending-uint2str-buffer.md. *)
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
