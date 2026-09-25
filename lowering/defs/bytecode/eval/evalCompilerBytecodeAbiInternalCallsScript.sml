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
val internal_tuple_call_oracle_eq = EQT_ELIM (EVAL (mk_eq
  (rhs (concl internal_tuple_call_compile_eval),
   ``SOME ^(evalCompilerBytecodeLib.read_hex_bytes
       "internal_tuple_call.hex")``)))
val internal_tuple_call_matches_python_oracle = save_thm
  ("internal_tuple_call_matches_python_oracle",
   TRANS internal_tuple_call_compile_eval
     internal_tuple_call_oracle_eq)

Theorem internal_struct_call_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    task090_internal_struct_call_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_struct_call.hex")
Proof
  EVAL_TAC
QED

val internal_bytes_call_rpolicy = optionSyntax.dest_some
  (rhs (concl
    evalCompilerBytecodeAbiInternalTupleLoweringTheory.internal_tuple_call_policy_eval))
val internal_bytes_call_lower_runtime_eval = save_thm
  ("internal_bytes_call_lower_runtime_eval",
   EVAL ``lower_vyper_runtime_unit task090_internal_bytes_call_program
       ^internal_bytes_call_rpolicy``)
val internal_bytes_call_runtime_unit = optionSyntax.dest_some
  (rhs (concl internal_bytes_call_lower_runtime_eval))
val internal_bytes_call_run_pipeline_eval = save_thm
  ("internal_bytes_call_run_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
       ^internal_bytes_call_rpolicy o1_pipeline_spec
       ^internal_bytes_call_runtime_unit``)
val internal_bytes_call_pipeline_out = optionSyntax.dest_some
  (rhs (concl internal_bytes_call_run_pipeline_eval))
val internal_bytes_call_final_unit_eval = EVAL
  ``(^internal_bytes_call_pipeline_out).po_unit``
val internal_bytes_call_final_unit =
  rhs (concl internal_bytes_call_final_unit_eval)
val internal_bytes_call_context_plan_eval = save_thm
  ("internal_bytes_call_context_plan_eval",
   EVAL ``generate_context_plan
       (^internal_bytes_call_final_unit).cu_context``)
val internal_bytes_call_context_plan = optionSyntax.dest_some
  (rhs (concl internal_bytes_call_context_plan_eval))
val internal_bytes_call_plan_ops_eval = EVAL
  ``context_plan_ops ^internal_bytes_call_context_plan``
val internal_bytes_call_initial_fmp_eval = EVAL
  ``(^internal_bytes_call_context_plan).cp_initial_fmp``
val internal_bytes_call_execute_plan_eval = save_thm
  ("internal_bytes_call_execute_plan_eval",
   EVAL ``execute_plan
       ^(rhs (concl internal_bytes_call_initial_fmp_eval))
       ^(rhs (concl internal_bytes_call_plan_ops_eval))``)
val internal_bytes_call_data_asm_eval = EVAL
  ``data_segment_asm (^internal_bytes_call_final_unit).cu_data_segment``
val internal_bytes_call_raw_asm_eval = EVAL
  ``^(rhs (concl internal_bytes_call_execute_plan_eval)) ++
    ^(rhs (concl internal_bytes_call_data_asm_eval)) ++
    [AsmDataHeader "code_end"]``
val internal_bytes_call_raw_asm = rhs (concl internal_bytes_call_raw_asm_eval)
val internal_bytes_call_target_wf_eval = EVAL
  ``target_capabilities_wf (^internal_bytes_call_rpolicy).rpol_target``
val internal_bytes_call_context_safe_eval = EVAL
  ``context_target_safe (^internal_bytes_call_rpolicy).rpol_target
      (^internal_bytes_call_final_unit).cu_context``
val internal_bytes_call_assembly_safe_eval = EVAL
  ``assembly_target_safe (^internal_bytes_call_rpolicy).rpol_target
      ^internal_bytes_call_raw_asm``
val internal_bytes_call_codegen_step0 = SIMP_CONV pure_ss
  [codegenTheory.codegen_assembly_def,
   internal_bytes_call_target_wf_eval,
   internal_bytes_call_context_safe_eval,
   internal_bytes_call_context_plan_eval,
   optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^internal_bytes_call_rpolicy
      ^internal_bytes_call_final_unit``
val internal_bytes_call_codegen_step1 = SIMP_CONV pure_ss
  [internal_bytes_call_plan_ops_eval,
   internal_bytes_call_initial_fmp_eval,
   internal_bytes_call_execute_plan_eval,
   internal_bytes_call_data_asm_eval,
   internal_bytes_call_raw_asm_eval,
   internal_bytes_call_assembly_safe_eval]
  (rhs (concl internal_bytes_call_codegen_step0))
val internal_bytes_call_codegen_step2 =
  EVAL (rhs (concl internal_bytes_call_codegen_step1))
val internal_bytes_call_codegen_eval = save_thm
  ("internal_bytes_call_codegen_eval",
   TRANS internal_bytes_call_codegen_step0
     (TRANS internal_bytes_call_codegen_step1
       internal_bytes_call_codegen_step2))
val internal_bytes_call_finalize_step0 =
  REWR_CONV codegenTheory.finalize_codegen_identity
    ``finalize_codegen (K SOME) ^internal_bytes_call_rpolicy
        ^internal_bytes_call_final_unit``
val internal_bytes_call_finalize_step1 = PURE_REWRITE_CONV
  [internal_bytes_call_codegen_eval]
  (rhs (concl internal_bytes_call_finalize_step0))
val internal_bytes_call_finalize_step2 =
  EVAL (rhs (concl internal_bytes_call_finalize_step1))
val internal_bytes_call_finalize_eval = save_thm
  ("internal_bytes_call_finalize_eval",
   TRANS internal_bytes_call_finalize_step0
     (TRANS internal_bytes_call_finalize_step1
       internal_bytes_call_finalize_step2))
val internal_bytes_call_runtime_bytes = optionSyntax.dest_some
  (rhs (concl internal_bytes_call_finalize_eval))
val internal_bytes_call_lower_deploy_eval = save_thm
  ("internal_bytes_call_lower_deploy_eval",
   EVAL ``lower_vyper_deploy_unit task090_internal_bytes_call_program
       ^internal_bytes_call_rpolicy ^internal_bytes_call_runtime_bytes``)
val internal_bytes_call_deploy_unit = optionSyntax.dest_some
  (rhs (concl internal_bytes_call_lower_deploy_eval))
val internal_bytes_call_deploy_pipeline_eval = save_thm
  ("internal_bytes_call_deploy_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
       ^internal_bytes_call_rpolicy o1_pipeline_spec
       ^internal_bytes_call_deploy_unit``)
val internal_bytes_call_deploy_out = optionSyntax.dest_some
  (rhs (concl internal_bytes_call_deploy_pipeline_eval))
val internal_bytes_call_final_deploy_unit_eval = EVAL
  ``(^internal_bytes_call_deploy_out).po_unit``
val internal_bytes_call_final_deploy_unit =
  rhs (concl internal_bytes_call_final_deploy_unit_eval)
val internal_bytes_call_finalize_deploy_eval = save_thm
  ("internal_bytes_call_finalize_deploy_eval",
   EVAL ``finalize_codegen (K SOME) ^internal_bytes_call_rpolicy
       ^internal_bytes_call_final_deploy_unit``)
val internal_bytes_call_compile_term =
  ``compile_vyper (K SOME) (o1_policy all_capabilities)
      task090_internal_bytes_call_program``
val internal_bytes_call_compile_step0 = SIMP_CONV pure_ss
  [compileVyperTheory.compile_vyper_def,
   compileVyperTheory.compile_vyper_with_def,
   compileVyperTheory.checked_unit_pipeline_def,
   optionTheory.option_case_def,
   boolTheory.COND_CLAUSES,
   evalCompilerBytecodeAbiInternalTupleLoweringTheory.internal_tuple_call_policy_eval,
   internal_bytes_call_lower_runtime_eval,
   internal_bytes_call_run_pipeline_eval,
   internal_bytes_call_finalize_eval,
   internal_bytes_call_lower_deploy_eval,
   internal_bytes_call_deploy_pipeline_eval,
   internal_bytes_call_finalize_deploy_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  internal_bytes_call_compile_term
val internal_bytes_call_compile_step1 =
  EVAL (rhs (concl internal_bytes_call_compile_step0))
val internal_bytes_call_compile_eval =
  TRANS internal_bytes_call_compile_step0
    internal_bytes_call_compile_step1
val internal_bytes_call_oracle_eq = EQT_ELIM (EVAL (mk_eq
  (rhs (concl internal_bytes_call_compile_eval),
   ``SOME ^(evalCompilerBytecodeLib.read_hex_bytes
       "internal_bytes_call.hex")``)))
val internal_bytes_call_matches_python_oracle = save_thm
  ("internal_bytes_call_matches_python_oracle",
   TRANS internal_bytes_call_compile_eval
     internal_bytes_call_oracle_eq)
