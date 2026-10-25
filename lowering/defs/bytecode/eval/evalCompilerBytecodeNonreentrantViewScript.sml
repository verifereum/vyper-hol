(* Exact parity for the pinned nonreentrant external-entry fixture. *)
Theory evalCompilerBytecodeNonreentrantView
Ancestors
  compileVyper concretizeMemLocDefs alist byte integer_word option
Libs
  evalCompilerBytecodeLib evalCompilerEntryLib evalCompilerEntryFixtureLib
  vyperCheckContractFrontendLib vyperCheckContractLib jsonASTLib JSONDecode
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-entries"]
Theorem entry_selector:
  compute_selector FEMPTY "f" [] = (0x26121ff0,"fn_f",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [entry_selector])
Definition nr_ext_view_program_def:
  nr_ext_view_program = ^(checked_entry_fixture "nr_ext_view")
End
Theorem nr_ext_view_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    nr_ext_view_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes
      "../external-entries/oracle/nr_ext_view.hex")
Proof
  simp_tac pure_ss [compile_vyper_def, compile_vyper_with_def] >> entry_stage "resolve_o1_policy" >>
  simp_tac pure_ss [optionTheory.option_case_def] >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >>
  entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >>
  simp_tac pure_ss [LET_THM, pairTheory.pair_case_thm,
    listTheory.MAP, combinTheory.o_DEF, external_has_defaults_def,
    listTheory.EXISTS_DEF, listTheory.NULL_DEF, NOT_CLAUSES,
    OR_CLAUSES, COND_CLAUSES] >> BETA_TAC >> entry_stage "package_external_fn" >> entry_stage "run_lowering" >>
  simp_tac pure_ss [NOT_CLAUSES, OR_CLAUSES, COND_CLAUSES,
    optionTheory.option_case_def, checked_unit_pipeline_def] >>
  simp_tac pure_ss [venomPipelineDriverTheory.run_venom_pipeline_def] >> entry_stage "pipeline_spec_wf" >>
  entry_stage "unit_wf" >> entry_stage "raw_static_inputs_wf" >>
  simp_tac pure_ss [NOT_CLAUSES, COND_CLAUSES, combinTheory.K_THM] >> entry_stage "init_ir_supply" >>
  simp[venomPassScheduleTheory.o1_pipeline_spec_def] >>
  entry_begin_mapped_stage >> entry_pass_emit >> entry_pass_check >> entry_install_function >>
  entry_begin_mapped_stage >> entry_pass_emit >> entry_pass_check >> entry_install_function >>
  entry_stage "run_pipeline_stages" >> entry_admin >> entry_stage "fcg_analyze" >> simp[] >>
  entry_stage "prune_unit_fcg_unreachable" >> entry_stage "reachable_fcg_acyclic" >> simp[] >> entry_stage "fcg_postorder" >>
  simp_tac pure_ss [venomPipelineRunnerTheory.run_callee_first_def,
    venomPipelineRunnerTheory.run_named_fn_schedules_def,
    venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >> entry_stage "ir_supply_covers_unit" >>
  entry_stage "lookup_unique_function" >> simp[venomPassScheduleTheory.o1_fn_passes_def] >> entry_pass_emit >> entry_pass_check >>
  entry_pass_emit >> entry_pass_check >> entry_pass_emit >> entry_pass_check >> entry_pass_emit >> entry_pass_check >>
  entry_pass_emit >> entry_pass_check >> entry_pass_emit >> entry_pass_check >> entry_pass_emit >> entry_pass_check >>
  entry_pass_emit >> entry_pass_check >> entry_pass_emit >> entry_pass_check >>
  entry_stage "run_configured_fn_pass_fold" >> entry_admin >> entry_stage "replace_unique_function" >> entry_admin >>
  entry_stage "apply_unit_label_map" >> entry_admin >> entry_guard "unit_labels_wf" >> entry_guard "list_subset" >>
  entry_guard "ir_supply_covers_unit" >> entry_guard "unit_global_inst_ids_distinct" >> entry_admin >>
  entry_stage "run_pipeline_stages" >> entry_admin >> entry_guard "unit_wf" >> entry_guard "unit_labels_wf" >>
   entry_guard "context_target_safe" >> entry_guard "concretized_static_layouts_wf" >> entry_guard "fmp_lowered_context_wf" >>
   entry_stage "fcg_analyze" >> entry_guard "reachable_fcg_acyclic" >> entry_guard "codegen_ready" >> entry_admin >>
   simp_tac pure_ss [codegenTheory.finalize_codegen_identity,
     codegenTheory.codegen_assembly_def] >> entry_guard "target_capabilities_wf" >>
   entry_guard "context_target_safe" >> entry_admin >>
   simp_tac pure_ss [stackPlanGenTheory.generate_context_plan_def,
     stackPlanGenTheory.generate_context_plan_with_def] >> entry_stage "max_live_eom" >> entry_plan_admin >>
   simp_tac pure_ss [Once stackPlanGenTheory.generate_context_regions_def,
     stackPlanGenTheory.generate_fn_plan_def] >> entry_plan_admin >> entry_analysis_stage "liveness_analyze" >>
   entry_analysis_stage "dfg_build_function" >> entry_analysis_stage "cfg_analyze" >>
   entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >> entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >>
   entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >> entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >>
   entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >> entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >>
   entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >> entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >>
   entry_plan_next_control >> entry_plan_next_block >> entry_plan_spine_admin >> entry_plan_finish >>
  CONV_TAC (LAND_CONV computeLib.EVAL_CONV) >> entry_report_result >> EVAL_TAC
QED
val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.null (hyp th) andalso List.null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("nonreentrant parity has oracle dependencies: " ^ name)
  end) (DB.thms "evalCompilerBytecodeNonreentrantView");
