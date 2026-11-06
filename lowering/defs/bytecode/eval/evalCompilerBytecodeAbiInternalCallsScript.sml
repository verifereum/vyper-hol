(* Exact Python-oracle bytecode checks for supported internal-call returns. *)

Theory evalCompilerBytecodeAbiInternalCalls
Ancestors evalCompilerBytecodeAbiInternalTuplePipeline compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

Theorem internal_bytes_i2w_neg_num:
  ∀n. i2w (-&n) = -n2w n
Proof
  Cases_on `n` >> simp[i2w_def]
QED

val () = computeLib.upd_compset
  (computeLib.add_thms [internal_bytes_i2w_neg_num])

val () = Globals.max_print_depth := 20

val internal_tuple_call_compile_term =
  ``compile_vyper (K SOME) (o1_policy all_capabilities)
      task090_internal_tuple_call_program``
val internal_tuple_call_compile_step0 = SIMP_CONV pure_ss
  [compileVyperTheory.compile_vyper_def,
   compileVyperTheory.compile_vyper_with_def,
   compileVyperTheory.checked_unit_pipeline_def,
   optionTheory.option_case_def,
   boolTheory.COND_CLAUSES,
   evalCompilerBytecodeAbiInternalTupleLoweringTheory.internal_tuple_call_policy_eval,
   evalCompilerBytecodeAbiInternalTupleLoweringTheory.internal_tuple_call_lower_runtime_eval,
   evalCompilerBytecodeAbiInternalTuplePipelineTheory.internal_tuple_call_run_pipeline_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  internal_tuple_call_compile_term
val internal_tuple_call_compile_step1 =
  EVAL (rhs (concl internal_tuple_call_compile_step0))
val internal_tuple_call_compile_eval =
  TRANS internal_tuple_call_compile_step0
    internal_tuple_call_compile_step1
val () = evalCompilerBytecodeLib.add_compile_eval internal_tuple_call_compile_eval

Theorem internal_tuple_call_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_internal_tuple_call_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_tuple_call.hex")
Proof
  EVAL_TAC
QED

Theorem internal_struct_call_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_internal_struct_call_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_struct_call.hex")
Proof
  EVAL_TAC
QED
