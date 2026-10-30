(* Exact parity for the shared-body external default-argument entry path. *)
Theory evalCompilerBytecodeDefaultEntries
Ancestors
  compileVyper concretizeMemLocDefs alist byte integer_word option
Libs
  proofAuditLib
  evalCompilerBytecodeLib evalCompilerEntryLib evalCompilerEntryFixtureLib
  vyperCheckContractFrontendLib vyperCheckContractLib jsonASTLib JSONDecode
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-entries"]
Theorem default_uint_selector:
  compute_selector FEMPTY "f" [BaseT (UintT 256)] = (3017696395,"fn_f",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [default_uint_selector])
Theorem default_two_uints_selector:
  compute_selector FEMPTY "f" [BaseT (UintT 256);BaseT (UintT 256)] =
    (0x13d1aa2e,"fn_f",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [default_two_uints_selector])
Definition dflt_one_lit_program_def:
  dflt_one_lit_program = ^(checked_entry_fixture "dflt_one_lit")
End
Theorem dflt_one_lit_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    dflt_one_lit_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes
      "../external-entries/oracle/dflt_one_lit.hex")
Proof
  simp_tac pure_ss [compile_vyper_def, compile_vyper_with_def] >> entry_stage "resolve_o1_policy" >>
  simp_tac pure_ss [optionTheory.option_case_def] >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >>
  entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >>
  entry_choose_grouped_path >> entry_guard "EVERY" >> entry_admin >> entry_stage "package_external_group" >> entry_stage "run_grouped_lowering" >>
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
  entry_open_schedule >> entry_stage "ir_supply_covers_unit" >>
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
   entry_open_codegen >> entry_guard "target_capabilities_wf" >>
   entry_guard "context_target_safe" >> entry_admin >>
   simp_tac pure_ss [stackPlanGenTheory.generate_context_plan_def,
     LET_THM, stackPlanGenTheory.generate_context_plan_with_def] >>
   entry_stage "fcg_analyze" >> entry_stage "cleanup_growth_table" >> entry_stage "max_live_eom" >> entry_plan_admin >>
   simp_tac pure_ss [Once stackPlanGenTheory.generate_context_regions_def,
     stackPlanGenTheory.generate_fn_plan_with_cleanup_def] >>
   entry_stage "cleanup_caller_height" >> entry_plan_admin >> entry_analysis_stage "liveness_analyze" >>
   entry_analysis_stage "dfg_build_function" >> entry_analysis_stage "cfg_analyze" >>
   entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >> entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >>
   entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >> entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >>
   entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >> entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >>
   entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >> entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >>
   entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >> entry_plan_finish >>
  CONV_TAC (LAND_CONV computeLib.EVAL_CONV) >> entry_report_result >> EVAL_TAC
QED
val () = proofAuditLib.check_theory "evalCompilerBytecodeDefaultEntries";
