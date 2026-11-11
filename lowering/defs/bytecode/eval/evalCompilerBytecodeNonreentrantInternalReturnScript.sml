(* Exact upstream DFT bytes for a nonreentrant internal callee. *)
Theory evalCompilerBytecodeNonreentrantInternalReturn
Ancestors
  compileVyper concretizeMemLocDefs alist byte integer_word option
Libs
  evalCompilerBytecodeLib evalCompilerEntryLib evalCompilerEntryFixtureLib evalCompilerBoundedLib evalCompilerBaseLib
  vyperCheckContractFrontendLib vyperCheckContractLib jsonASTLib JSONDecode

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-entries"]

Theorem internal_entry_selector:
  compute_selector FEMPTY "f" [BaseT (UintT 256)] = (3017696395,"fn_f",F)
Proof
  simp_tac pure_ss [compute_selector_def, LET_THM] >>
  entry_stage "function_selector" >> EVAL_TAC
QED
val () = computeLib.upd_compset (computeLib.add_thms [internal_entry_selector])

Definition nr_internal_return_program_def:
  nr_internal_return_program = ^(checked_entry_fixture "nr_internal_return")
End

(* DFT abort-run ordering follows https://github.com/vyperlang/vyper/pull/5336.
   Expected bytes: VYPER_PIN 577d2534 with upstream 56e7bc32's dft.py patch,
   using the external-entry corpus settings. The pinned oracle stays intact. *)
val nr_internal_return_upstream_dft_bytes = pairSyntax.mk_pair
  (evalCompilerBytecodeLib.hex_bytes_tm
    ("5b60b15f9081610013903960b190f35b5f80fd5b60043610156100175761000e" ^
     "565b610013565b5f5ffd5b5f3560e01c63b3de648b146100305761002b565b61" ^
     "0013565b3415156100ad576024361015156100ad575f60040135606090815280" ^
     "5161005561008b565b604090815f015251604090815251905161006d61008b56" ^
     "5b81905f90815f01525191910190811015156100ad575f908152602090f35b90" ^
     "6020505f5c60011415156100ad575f90815280515f5560015f5d5f5f5d519056" ^
     "5b5f80fd"),
   evalCompilerBytecodeLib.hex_bytes_tm
    ("5b60043610156100175761000e565b610013565b5f5ffd5b5f3560e01c63b3de" ^
     "648b146100305761002b565b610013565b3415156100ad576024361015156100" ^
     "ad575f600401356060908152805161005561008b565b604090815f0152516040" ^
     "90815251905161006d61008b565b81905f90815f015251919101908110151561" ^
     "00ad575f908152602090f35b906020505f5c60011415156100ad575f90815280" ^
     "515f5560015f5d5f5f5d5190565b5f80fd"));

Theorem nr_internal_return_matches_upstream_dft:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    nr_internal_return_program =
    SOME ^nr_internal_return_upstream_dft_bytes
Proof
  simp_tac pure_ss [compile_vyper_def, compile_vyper_with_def] >> entry_stage "resolve_o1_policy" >> simp_tac pure_ss [optionTheory.option_case_def] >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >>
  entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >> entry_chunk 50 >>
  entry_choose_grouped_path >>
  entry_stage "package_external_fn" >> entry_guard "EVERY" >> entry_immutables_guard >> entry_admin >> entry_stage "run_lowering" >> simp_tac pure_ss [NOT_CLAUSES, OR_CLAUSES, COND_CLAUSES, optionTheory.option_case_def, checked_unit_pipeline_def] >>
  simp_tac pure_ss [venomPipelineDriverTheory.run_venom_pipeline_def] >> entry_stage "pipeline_spec_wf" >> entry_stage "unit_wf" >> entry_stage "raw_static_inputs_wf" >>
  simp_tac pure_ss [NOT_CLAUSES, COND_CLAUSES, combinTheory.K_THM] >> entry_stage "init_ir_supply" >> simp[venomPassScheduleTheory.o1_pipeline_spec_def] >> entry_begin_mapped_stage >> entry_pass_begin >>
  entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_install_function >> entry_guard "ir_supply_covers_unit" >> entry_stage "lookup_unique_function" >> entry_admin >> entry_pass_begin >>
  entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_install_function >> entry_begin_mapped_stage >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >>
  entry_install_function >> entry_guard "ir_supply_covers_unit" >> entry_stage "lookup_unique_function" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >>
  entry_install_function >> entry_stage "run_pipeline_stages" >> entry_admin >> entry_stage "fcg_analyze" >> simp[] >> entry_stage "prune_unit_fcg_unreachable" >> entry_stage "reachable_fcg_acyclic" >> simp[] >>
  entry_stage "fcg_postorder" >> entry_open_schedule >>
  entry_stage "ir_supply_covers_unit" >> entry_stage "lookup_unique_function" >> simp[venomPassScheduleTheory.o1_fn_passes_def] >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >>
  entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >>
  entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >>
  entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >>
  entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_stage "run_configured_fn_pass_fold" >>
  entry_admin >> entry_stage "replace_unique_function" >> entry_admin >> entry_stage "apply_unit_label_map" >> entry_admin >> entry_guard "unit_labels_wf" >> entry_guard "list_subset" >> entry_guard "ir_supply_covers_unit" >>
  entry_guard "unit_global_inst_ids_distinct" >> entry_admin >> entry_guard "ir_supply_covers_unit" >> entry_stage "lookup_unique_function" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >>
  entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >>
  entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >>
  entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >>
  entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >>
  entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_dft_start >> entry_dft_cfg >> entry_dft_live >> simp_tac pure_ss [LET_THM] >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  base_dft_open >> base_dft_state >> base_dft_part "so_analyze_block" >> base_dft_state >>
  base_dft_part "so_get_stack" >> base_dft_state >> base_dft_part "dft_block" >> base_dft_state >>
  entry_dft_finish >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_pass_begin >> entry_stage "execute_configured_fn_pass" >> entry_admin >> entry_guard "fn_pass_effects_hold" >> entry_guard "introduces_no_invoke_edges" >>
  entry_guard "ir_supply_extends" >> entry_guard "ir_supply_covers_fn" >>
  entry_guard "ir_supply_covers_unit" >> entry_admin >> entry_stage "run_configured_fn_pass_fold" >>
  entry_admin >> entry_stage "replace_unique_function" >> entry_admin >> entry_stage "apply_unit_label_map" >> entry_admin >> entry_guard "unit_labels_wf" >> entry_guard "list_subset" >> entry_guard "ir_supply_covers_unit" >>
  entry_guard "unit_global_inst_ids_distinct" >> entry_admin >> entry_stage "run_pipeline_stages" >> entry_admin >> entry_guard "unit_wf" >> entry_guard "unit_labels_wf" >> entry_guard "context_target_safe" >>
  entry_guard "concretized_static_layouts_wf" >> entry_guard "fmp_lowered_context_wf" >> entry_stage "fcg_analyze" >> entry_guard "reachable_fcg_acyclic" >>
  entry_open_codegen_ready >> entry_guard "canonical_param_prefix" >>
  entry_guard "wf_function" >> entry_guard "fn_inst_wf" >>
  entry_guard "ssa_form" >> entry_guard "def_dominates_uses" >>
  entry_guard "single_use_form" >> entry_guard "cfg_is_normalized" >> entry_codegen_ready_guards >>
  entry_guard "EVERY" >> entry_immutables_guard >> entry_admin >>
  entry_open_codegen >> entry_guard "target_capabilities_wf" >> entry_guard "context_target_safe" >> entry_admin >>
  simp_tac pure_ss [stackPlanGenTheory.generate_context_plan_def, LET_THM, stackPlanGenTheory.generate_context_plan_with_def] >>
  entry_stage "fcg_analyze" >> entry_stage "cleanup_growth_table" >> entry_stage "max_live_eom" >> entry_plan_admin >>
  simp_tac pure_ss [Once stackPlanGenTheory.generate_context_regions_def, stackPlanGenTheory.generate_fn_plan_with_cleanup_def] >>
  entry_stage "cleanup_caller_height" >> entry_plan_admin >> entry_analysis_stage "liveness_analyze" >> entry_analysis_stage "dfg_build_function" >>
  entry_analysis_stage "cfg_analyze" >> entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >> entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >> entry_plan_control >> entry_plan_block >>
  entry_plan_spine_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  plan_control >> plan_admin >> plan_setup >> plan_admin >>
  entry_plan_block >> entry_plan_spine_admin >> entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >> entry_plan_control >> entry_plan_block >> entry_plan_spine_admin >>
  entry_plan_finish >> entry_stage "generate_context_regions" >> entry_admin >>
  entry_guard "spill_plan_in_region" >> entry_plan_admin >>
  entry_stage "OPTION_MAP" >> entry_admin >>
  CONV_TAC (LAND_CONV computeLib.EVAL_CONV) >> entry_report_result >> EVAL_TAC
QED

Theorem nr_internal_return_compiles:
  IS_SOME (compile_vyper (K SOME) (o1_policy all_capabilities)
    nr_internal_return_program)
Proof
  PURE_REWRITE_TAC [nr_internal_return_matches_upstream_dft] >> EVAL_TAC
QED

Theorem nr_internal_return_differs_from_pinned_dft:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    nr_internal_return_program <>
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes
      "../external-entries/oracle/nr_internal_return.hex")
Proof
  PURE_REWRITE_TAC [nr_internal_return_matches_upstream_dft] >> EVAL_TAC
QED
