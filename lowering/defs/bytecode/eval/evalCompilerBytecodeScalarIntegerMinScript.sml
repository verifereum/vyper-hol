(* Checked runtime-pipeline staging for the scalar_integer_min_int256 fixture. *)

Theory evalCompilerBytecodeScalarIntegerMin
Ancestors evalCompilerBytecodeScalarWordEval evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``type_bounds``)
    |> computeLib.add_thms
         [scalar_int256_type_bounds_eval,
          w2n_scalar_int256_min_word_eval,
          w2i_scalar_int256_min_word_eval,
          scalar_int256_min_word_eq_word,
          word_eq_scalar_int256_min_word])
val () = Globals.max_print_depth := 20

Definition scalar_integer_min_int256_runtime_pipeline_def:
  scalar_integer_min_int256_runtime_pipeline tops =
    case resolve_o1_policy (o1_policy prague_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            OPTION_MAP (λout. (rpolicy,out))
              (run_venom_pipeline (K T) (K T) (K T)
                 rpolicy o1_pipeline_spec unit)
End

val scalar_integer_min_int256_runtime_pipeline_eval =
  save_thm ("scalar_integer_min_int256_runtime_pipeline_eval",
    EVAL ``scalar_integer_min_int256_runtime_pipeline scalar_integer_min_int256_program``)

Definition scalar_integer_min_int256_runtime_compile_def:
  scalar_integer_min_int256_runtime_compile tops =
    case scalar_integer_min_int256_runtime_pipeline tops of
      NONE => NONE
    | SOME (rpolicy,out) =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen (K SOME) rpolicy out.po_unit
End

(* Cache the concrete analyses and stack plan before asking the evaluator to
   finish code generation.  This keeps the minimum signed 256-bit literal
   opaque through the branch-heavy generic planner. *)
val scalar_integer_min_int256_pipeline_value =
  rhs (concl scalar_integer_min_int256_runtime_pipeline_eval)
val scalar_integer_min_int256_rp_out =
  optionSyntax.dest_some scalar_integer_min_int256_pipeline_value
val scalar_integer_min_int256_rpolicy =
  #1 (pairSyntax.dest_pair scalar_integer_min_int256_rp_out)
val scalar_integer_min_int256_out =
  #2 (pairSyntax.dest_pair scalar_integer_min_int256_rp_out)
val scalar_integer_min_int256_unit_eval =
  EVAL ``(^scalar_integer_min_int256_out).po_unit``
val scalar_integer_min_int256_unit =
  rhs (concl scalar_integer_min_int256_unit_eval)
val scalar_integer_min_int256_fn = rhs (concl (EVAL
  ``HD (^scalar_integer_min_int256_unit).cu_context.ctx_functions``))
val scalar_integer_min_int256_liveness_eval = save_thm
  ("scalar_integer_min_int256_liveness_eval",
   EVAL ``liveness_analyze ^scalar_integer_min_int256_fn``)
val scalar_integer_min_int256_dfg_eval = save_thm
  ("scalar_integer_min_int256_dfg_eval",
   EVAL ``dfg_build_function ^scalar_integer_min_int256_fn``)
val scalar_integer_min_int256_cfg_eval = save_thm
  ("scalar_integer_min_int256_cfg_eval",
   EVAL ``cfg_analyze ^scalar_integer_min_int256_fn``)
val scalar_integer_min_int256_liveness =
  rhs (concl scalar_integer_min_int256_liveness_eval)
val scalar_integer_min_int256_dfg =
  rhs (concl scalar_integer_min_int256_dfg_eval)
val scalar_integer_min_int256_cfg =
  rhs (concl scalar_integer_min_int256_cfg_eval)
val scalar_integer_min_int256_max_eom_eval = EVAL
  ``max_live_eom (^scalar_integer_min_int256_unit).cu_context``
val scalar_integer_min_int256_max_eom = optionSyntax.dest_some
  (rhs (concl scalar_integer_min_int256_max_eom_eval))
val scalar_integer_min_int256_generate_fn_plan = save_thm
  ("scalar_integer_min_int256_generate_fn_plan", prove
    (``∀spill labels.
        generate_fn_plan ^scalar_integer_min_int256_fn spill labels =
        generate_fn_plan_analyzed ^scalar_integer_min_int256_liveness
          ^scalar_integer_min_int256_dfg ^scalar_integer_min_int256_cfg
          ^scalar_integer_min_int256_fn spill labels``,
     simp[stackPlanGenTheory.generate_fn_plan_def,
          scalar_integer_min_int256_liveness_eval,
          scalar_integer_min_int256_dfg_eval,
          scalar_integer_min_int256_cfg_eval]))
val () = computeLib.upd_compset (computeLib.add_thms
  [scalar_integer_min_int256_liveness_eval,
   scalar_integer_min_int256_dfg_eval,
   scalar_integer_min_int256_cfg_eval,
   scalar_integer_min_int256_generate_fn_plan])
val scalar_integer_min_int256_plan_eval = save_thm
  ("scalar_integer_min_int256_plan_eval", EVAL
    ``generate_fn_plan_analyzed ^scalar_integer_min_int256_liveness
       ^scalar_integer_min_int256_dfg ^scalar_integer_min_int256_cfg
       ^scalar_integer_min_int256_fn ^scalar_integer_min_int256_max_eom 0``)
val scalar_integer_min_int256_plan =
  rhs (concl scalar_integer_min_int256_plan_eval)
val scalar_integer_min_int256_concrete_fn_plan = save_thm
  ("scalar_integer_min_int256_concrete_fn_plan", prove
    (``generate_fn_plan ^scalar_integer_min_int256_fn
          ^scalar_integer_min_int256_max_eom 0 =
        ^scalar_integer_min_int256_plan``,
     simp[scalar_integer_min_int256_generate_fn_plan,
          scalar_integer_min_int256_plan_eval]))
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``generate_fn_plan``)
    |> computeLib.add_thms [scalar_integer_min_int256_concrete_fn_plan])
val scalar_integer_min_int256_context_plan_step1 = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.generate_context_plan_def,
   stackPlanGenTheory.generate_context_plan_with_def,
   scalar_integer_min_int256_max_eom_eval,
   stackPlanGenTheory.generate_context_regions_def,
   stackPlanGenTheory.finish_context_plan_def]
  ``generate_context_plan (^scalar_integer_min_int256_unit).cu_context``
val scalar_integer_min_int256_context_plan_step2 =
  EVAL (rhs (concl scalar_integer_min_int256_context_plan_step1))
val scalar_integer_min_int256_actual_plan_call = find_term
  (can (match_term ``generate_fn_plan f spill labels``))
  (rhs (concl scalar_integer_min_int256_context_plan_step2))
val scalar_integer_min_int256_actual_plan_args =
  #2 (strip_comb scalar_integer_min_int256_actual_plan_call)
val scalar_integer_min_int256_actual_fn =
  hd scalar_integer_min_int256_actual_plan_args
val scalar_integer_min_int256_actual_liveness_eval =
  EVAL ``liveness_analyze ^scalar_integer_min_int256_actual_fn``
val scalar_integer_min_int256_actual_dfg_eval =
  EVAL ``dfg_build_function ^scalar_integer_min_int256_actual_fn``
val scalar_integer_min_int256_actual_cfg_eval =
  EVAL ``cfg_analyze ^scalar_integer_min_int256_actual_fn``
val scalar_integer_min_int256_actual_liveness =
  rhs (concl scalar_integer_min_int256_actual_liveness_eval)
val scalar_integer_min_int256_actual_dfg =
  rhs (concl scalar_integer_min_int256_actual_dfg_eval)
val scalar_integer_min_int256_actual_cfg =
  rhs (concl scalar_integer_min_int256_actual_cfg_eval)
val scalar_integer_min_int256_actual_plan_eval = EVAL
  ``generate_fn_plan_analyzed ^scalar_integer_min_int256_actual_liveness
      ^scalar_integer_min_int256_actual_dfg
      ^scalar_integer_min_int256_actual_cfg
      ^scalar_integer_min_int256_actual_fn
      ^scalar_integer_min_int256_max_eom 0``
val scalar_integer_min_int256_actual_generate_step1 =
  REWR_CONV stackPlanGenTheory.generate_fn_plan_def
    ``generate_fn_plan ^scalar_integer_min_int256_actual_fn
        ^scalar_integer_min_int256_max_eom 0``
val scalar_integer_min_int256_actual_generate_step2 = PURE_REWRITE_CONV
  [scalar_integer_min_int256_actual_liveness_eval,
   scalar_integer_min_int256_actual_dfg_eval,
   scalar_integer_min_int256_actual_cfg_eval]
  (rhs (concl scalar_integer_min_int256_actual_generate_step1))
val scalar_integer_min_int256_actual_generate_step3 =
  REWR_CONV scalar_integer_min_int256_actual_plan_eval
    (rhs (concl scalar_integer_min_int256_actual_generate_step2))
val scalar_integer_min_int256_actual_generate_fn_plan =
  TRANS scalar_integer_min_int256_actual_generate_step1
    (TRANS scalar_integer_min_int256_actual_generate_step2
      scalar_integer_min_int256_actual_generate_step3)
val scalar_integer_min_int256_context_plan_step3 = PURE_REWRITE_CONV
  [scalar_integer_min_int256_actual_generate_fn_plan]
  (rhs (concl scalar_integer_min_int256_context_plan_step2))
val scalar_integer_min_int256_context_plan_eval = save_thm
  ("scalar_integer_min_int256_context_plan_eval",
   TRANS scalar_integer_min_int256_context_plan_step1
    (TRANS scalar_integer_min_int256_context_plan_step2
      (TRANS scalar_integer_min_int256_context_plan_step3
        (EVAL (rhs (concl scalar_integer_min_int256_context_plan_step3))))))
val scalar_integer_min_int256_context_plan = optionSyntax.dest_some
  (rhs (concl scalar_integer_min_int256_context_plan_eval))
val scalar_integer_min_int256_target_wf_eval = EVAL
  ``target_capabilities_wf
      (^scalar_integer_min_int256_rpolicy).rpol_target``
val scalar_integer_min_int256_context_safe_eval = EVAL
  ``context_target_safe
      (^scalar_integer_min_int256_rpolicy).rpol_target
      (^scalar_integer_min_int256_unit).cu_context``
val scalar_integer_min_int256_codegen_step1 = SIMP_CONV (srw_ss())
  [codegenTheory.codegen_assembly_def,
   scalar_integer_min_int256_target_wf_eval,
   scalar_integer_min_int256_context_safe_eval,
   scalar_integer_min_int256_context_plan_eval,
   optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^scalar_integer_min_int256_rpolicy
      ^scalar_integer_min_int256_unit``
val scalar_integer_min_int256_codegen_step2 =
  EVAL (rhs (concl scalar_integer_min_int256_codegen_step1))
val scalar_integer_min_int256_codegen_assembly_eval = save_thm
  ("scalar_integer_min_int256_codegen_assembly_eval",
   TRANS scalar_integer_min_int256_codegen_step1
     scalar_integer_min_int256_codegen_step2)
val scalar_integer_min_int256_out_final_assembly_eval =
  EVAL ``(^scalar_integer_min_int256_out).po_final_assembly``
val scalar_integer_min_int256_rpolicy_final_assembly_eval =
  EVAL ``(^scalar_integer_min_int256_rpolicy).rpol_final_assembly``
val scalar_integer_min_int256_runtime_accessors =
  CONJUNCTS venomCompilerTypesTheory.pipeline_output_accessors @
  CONJUNCTS venomCompilerTypesTheory.resolved_compiler_policy_accessors

Theorem scalar_integer_min_int256_runtime_matches_python_oracle:
  scalar_integer_min_int256_runtime_compile
      scalar_integer_min_int256_program =
    SOME (SND ^(evalCompilerBytecodeLib.read_hex_bytes
      "scalar_integer_min_int256.hex"))
Proof
  simp_tac pure_ss
    ([scalar_integer_min_int256_runtime_compile_def,
      scalar_integer_min_int256_runtime_pipeline_eval,
      optionTheory.option_case_compute,
      optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
      pairTheory.pair_case_thm, LET_THM, COND_CLAUSES,
      REFL_CLAUSE, NOT_CLAUSES,
      scalar_integer_min_int256_unit_eval,
      scalar_integer_min_int256_out_final_assembly_eval,
      scalar_integer_min_int256_rpolicy_final_assembly_eval] @
     scalar_integer_min_int256_runtime_accessors) >>
  PURE_REWRITE_TAC [codegenTheory.finalize_codegen_identity] >>
  PURE_REWRITE_TAC [scalar_integer_min_int256_codegen_assembly_eval] >>
  EVAL_TAC
QED

Definition scalar_integer_min_int256_deploy_compile_def:
  scalar_integer_min_int256_deploy_compile tops runtime =
    case resolve_o1_policy (o1_policy prague_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_deploy_unit tops rpolicy runtime of
          NONE => NONE
        | SOME unit =>
            checked_unit_pipeline
              (λrp u. run_venom_pipeline (K T) (K T) (K T)
                 rp o1_pipeline_spec u)
              (K SOME) rpolicy unit
End

Theorem scalar_integer_min_int256_deploy_matches_python_oracle:
  scalar_integer_min_int256_deploy_compile
      scalar_integer_min_int256_program
      (SND ^(evalCompilerBytecodeLib.read_hex_bytes
        "scalar_integer_min_int256.hex")) =
    SOME (FST ^(evalCompilerBytecodeLib.read_hex_bytes
      "scalar_integer_min_int256.hex"))
Proof
  EVAL_TAC
QED

Theorem scalar_integer_min_int256_compile_staged:
  compile_vyper (K SOME) (o1_policy prague_capabilities) tops =
    case scalar_integer_min_int256_runtime_compile tops of
      NONE => NONE
    | SOME runtime =>
        OPTION_MAP (λdeploy. (deploy,runtime))
          (scalar_integer_min_int256_deploy_compile tops runtime)
Proof
  simp[compile_vyper_def, compile_vyper_with_def,
       scalar_integer_min_int256_runtime_compile_def,
       scalar_integer_min_int256_runtime_pipeline_def,
       scalar_integer_min_int256_deploy_compile_def,
       checked_unit_pipeline_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem scalar_integer_min_int256_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_integer_min_int256_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes
      "scalar_integer_min_int256.hex")
Proof
  PURE_REWRITE_TAC [scalar_integer_min_int256_compile_staged] >>
  PURE_REWRITE_TAC
    [scalar_integer_min_int256_runtime_matches_python_oracle] >>
  simp_tac pure_ss
    [optionTheory.option_case_compute,
     optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
     optionTheory.OPTION_MAP_DEF, LET_THM, COND_CLAUSES,
     scalar_integer_min_int256_deploy_matches_python_oracle] >>
  EVAL_TAC
QED
