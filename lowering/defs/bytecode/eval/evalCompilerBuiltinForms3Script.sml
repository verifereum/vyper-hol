(* Independent checked-frontend bytecode witnesses for builtin forms (#566):
   .code slices (a07-08): self.code and <addr>.code, and struct members named code or data.
   Part 3 of evalCompilerBuiltinForms.
   TOP-LEVEL: self_code_slice_matches_python_oracle,
              ext_code_slice_matches_python_oracle,
              struct_code_slice_matches_python_oracle,
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

(* slice(self.code, 0, 10): CODESIZE/CODECOPY. *)
val self_code_slice = memoryStoreWitnessLib.evaluate fixture_root "self_code_slice"
Theorem self_code_slice_matches_python_oracle:
  ^(#term self_code_slice) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "self_code_slice")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation self_code_slice))) >> EVAL_TAC
QED

(* slice(a.code, s, 10): start and length, then the address, EXTCODESIZE and
   the bounds check before the output buffer. *)
val ext_code_slice = memoryStoreWitnessLib.evaluate fixture_root "ext_code_slice"
Theorem ext_code_slice_matches_python_oracle:
  ^(#term ext_code_slice) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ext_code_slice")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ext_code_slice))) >> EVAL_TAC
QED

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
