(* Independent checked-frontend bytecode witnesses for builtin forms (#566):
   .code slices (a07-08): struct members named code or data.
   Part 3 of evalCompilerBuiltinForms.
   TOP-LEVEL: struct_code_slice_matches_python_oracle,
              struct_data_slice_matches_python_oracle. *)
Theory evalCompilerBuiltinForms3
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../builtin-forms"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../builtin-forms/oracle"

(* a struct member named code is an ordinary memory slice. *)
val struct_code_slice = memoryStoreWitnessLib.evaluate fixture_root "struct_code_slice"
Theorem struct_code_slice_matches_python_oracle:
  ^(#term struct_code_slice) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "struct_code_slice")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation struct_code_slice))) >> EVAL_TAC
QED

(* control: the same with a member named data. *)
val struct_data_slice = memoryStoreWitnessLib.evaluate fixture_root "struct_data_slice"
Theorem struct_data_slice_matches_python_oracle:
  ^(#term struct_data_slice) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "struct_data_slice")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation struct_data_slice))) >> EVAL_TAC
QED
