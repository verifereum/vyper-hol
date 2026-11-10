(* Independent checked-frontend bytecode witnesses for builtin forms (#566):
   concat results passed to and returned from internal functions (a07-05).
   Part 4 of evalCompilerBuiltinForms.
   TOP-LEVEL: p102_rbuf_bytes_ret_word_arg_matches_python_oracle. *)
Theory evalCompilerBuiltinForms4
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../builtin-forms"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../builtin-forms/oracle"

(* concat of two bytes32 in the callee. *)
val p102_rbuf_bytes_ret_word_arg = memoryStoreWitnessLib.evaluate fixture_root "p102_rbuf_bytes_ret_word_arg"
Theorem p102_rbuf_bytes_ret_word_arg_matches_python_oracle:
  ^(#term p102_rbuf_bytes_ret_word_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p102_rbuf_bytes_ret_word_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p102_rbuf_bytes_ret_word_arg))) >> EVAL_TAC
QED
