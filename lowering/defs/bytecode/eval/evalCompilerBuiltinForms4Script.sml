(* Independent checked-frontend bytecode witnesses for builtin forms (#566):
   concat results passed to and returned from internal functions (a07-05).
   Part 4 of evalCompilerBuiltinForms.
   TOP-LEVEL: p94_rbuf_bytes_ret_concat_arg_matches_python_oracle,
              p97_rbuf_stack_tuple_ret_concat_arg_matches_python_oracle,
              p98_rbuf_mem_tuple_ret_concat_arg_matches_python_oracle,
              p99_rbuf_string_ret_concat_arg_matches_python_oracle,
              p102_rbuf_bytes_ret_word_arg_matches_python_oracle,
              p103_rbuf_control_word_ret_concat_arg_matches_python_oracle,
              p58_int_bytes_local_matches_python_oracle. *)
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

(* Bytes return, concat argument. *)
val p94_rbuf_bytes_ret_concat_arg = memoryStoreWitnessLib.evaluate fixture_root "p94_rbuf_bytes_ret_concat_arg"
Theorem p94_rbuf_bytes_ret_concat_arg_matches_python_oracle:
  ^(#term p94_rbuf_bytes_ret_concat_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p94_rbuf_bytes_ret_concat_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p94_rbuf_bytes_ret_concat_arg))) >> EVAL_TAC
QED

(* stack tuple return, concat argument. *)
val p97_rbuf_stack_tuple_ret_concat_arg = memoryStoreWitnessLib.evaluate fixture_root "p97_rbuf_stack_tuple_ret_concat_arg"
Theorem p97_rbuf_stack_tuple_ret_concat_arg_matches_python_oracle:
  ^(#term p97_rbuf_stack_tuple_ret_concat_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p97_rbuf_stack_tuple_ret_concat_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p97_rbuf_stack_tuple_ret_concat_arg))) >> EVAL_TAC
QED

(* memory tuple return, concat argument. *)
val p98_rbuf_mem_tuple_ret_concat_arg = memoryStoreWitnessLib.evaluate fixture_root "p98_rbuf_mem_tuple_ret_concat_arg"
Theorem p98_rbuf_mem_tuple_ret_concat_arg_matches_python_oracle:
  ^(#term p98_rbuf_mem_tuple_ret_concat_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p98_rbuf_mem_tuple_ret_concat_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p98_rbuf_mem_tuple_ret_concat_arg))) >> EVAL_TAC
QED

(* String return, concat argument. *)
val p99_rbuf_string_ret_concat_arg = memoryStoreWitnessLib.evaluate fixture_root "p99_rbuf_string_ret_concat_arg"
Theorem p99_rbuf_string_ret_concat_arg_matches_python_oracle:
  ^(#term p99_rbuf_string_ret_concat_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p99_rbuf_string_ret_concat_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p99_rbuf_string_ret_concat_arg))) >> EVAL_TAC
QED

(* concat of two bytes32 in the callee. *)
val p102_rbuf_bytes_ret_word_arg = memoryStoreWitnessLib.evaluate fixture_root "p102_rbuf_bytes_ret_word_arg"
Theorem p102_rbuf_bytes_ret_word_arg_matches_python_oracle:
  ^(#term p102_rbuf_bytes_ret_word_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p102_rbuf_bytes_ret_word_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p102_rbuf_bytes_ret_word_arg))) >> EVAL_TAC
QED

(* word return, concat argument. *)
val p103_rbuf_control_word_ret_concat_arg = memoryStoreWitnessLib.evaluate fixture_root "p103_rbuf_control_word_ret_concat_arg"
Theorem p103_rbuf_control_word_ret_concat_arg_matches_python_oracle:
  ^(#term p103_rbuf_control_word_ret_concat_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p103_rbuf_control_word_ret_concat_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p103_rbuf_control_word_ret_concat_arg))) >> EVAL_TAC
QED

(* concat into a local in the callee. *)
val p58_int_bytes_local = memoryStoreWitnessLib.evaluate fixture_root "p58_int_bytes_local"
Theorem p58_int_bytes_local_matches_python_oracle:
  ^(#term p58_int_bytes_local) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p58_int_bytes_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p58_int_bytes_local))) >> EVAL_TAC
QED
