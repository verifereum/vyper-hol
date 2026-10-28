(* Actual O1 compiler stages for bounded checks of the independent corpus.
   These are conservative names for the calls made by compile_vyper. *)
Theory evalCompilerBytecodeStages
Ancestors compileVyper stackPlanObservations

Definition parity_policy_def:
  parity_policy = THE (resolve_o1_policy (o1_policy all_capabilities))
End
Definition parity_runtime_unit_def:
  parity_runtime_unit tops = THE (lower_vyper_runtime_unit tops parity_policy)
End
Definition parity_pre0_def:
  parity_pre0 tops = THE (run_pipeline_stage parity_policy
    (PS_MapFunctions (CFP_Simple VP_SimplifyCFG)) (parity_runtime_unit tops)
    (init_ir_supply (parity_runtime_unit tops)))
End
Definition parity_pre1_def:
  parity_pre1 tops = THE (run_pipeline_stage parity_policy
    (PS_MapFunctions (CFP_Simple VP_DretDesugar))
    (FST (parity_pre0 tops)) (SND (parity_pre0 tops)))
End
Definition parity_walk_unit_def:
  parity_walk_unit tops = prune_unit_fcg_unreachable (FST (parity_pre1 tops))
    (fcg_analyze (FST (parity_pre1 tops)).cu_context)
End
Definition parity_initial_function_def:
  parity_initial_function tops = THE (lookup_unique_function
    (HD (fcg_postorder (fcg_analyze (FST (parity_pre1 tops)).cu_context)
      (THE (FST (parity_pre1 tops)).cu_context.ctx_entry)))
    (parity_walk_unit tops).cu_context.ctx_functions)
End
Definition parity_pass_def:
  parity_pass tops 0 = THE (run_configured_fn_pass_fold execute_configured_fn_pass
    parity_policy [EL 0 o1_fn_passes] (parity_walk_unit tops)
    (SND (parity_pre1 tops)) (parity_initial_function tops) []) /\
  parity_pass tops (SUC n) = THE (run_configured_fn_pass_fold execute_configured_fn_pass
    parity_policy [EL (SUC n) o1_fn_passes] (parity_walk_unit tops)
    (SND (SND (parity_pass tops n))) (FST (parity_pass tops n))
    (FST (SND (parity_pass tops n))))
End
Definition parity_pass_call_def:
  parity_pass_call tops n = run_configured_fn_pass_fold execute_configured_fn_pass
    parity_policy [EL n o1_fn_passes] (parity_walk_unit tops)
    (if n = 0 then SND (parity_pre1 tops) else SND (SND (parity_pass tops (n-1))))
    (if n = 0 then parity_initial_function tops else FST (parity_pass tops (n-1)))
    (if n = 0 then [] else FST (SND (parity_pass tops (n-1))))
End

Theorem parity_pass_call_value:
  !tops n. parity_pass tops n = THE (parity_pass_call tops n)
Proof
  rpt gen_tac >> Cases_on `n` >> simp[parity_pass_def, parity_pass_call_def]
QED
Definition parity_walk_result_def:
  parity_walk_result tops = THE (run_callee_first parity_policy o1_fn_passes
    (fcg_postorder (fcg_analyze (FST (parity_pre1 tops)).cu_context)
      (THE (FST (parity_pre1 tops)).cu_context.ctx_entry))
    (parity_walk_unit tops) (SND (parity_pre1 tops)))
End
Definition parity_codegen_ready_def:
  parity_codegen_ready tops = codegen_ready (FST (parity_walk_result tops)).cu_context
End
Definition parity_runtime_pipeline_def:
  parity_runtime_pipeline tops = THE (run_venom_pipeline (K T) (K T) (K T)
    parity_policy o1_pipeline_spec (parity_runtime_unit tops))
End
Definition parity_plan_liveness_def:
  parity_plan_liveness tops = liveness_analyze
    (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)
End
Definition parity_plan_dfg_def:
  parity_plan_dfg tops = dfg_build_function
    (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)
End
Definition parity_plan_cfg_def:
  parity_plan_cfg tops = cfg_analyze
    (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)
End
Definition parity_entry_plan_def:
  parity_entry_plan tops = THE (generate_block_plan (parity_plan_liveness tops)
    (parity_plan_dfg tops) (parity_plan_cfg tops)
    (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)
    (THE (entry_block (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)))
    ((init_plan_state (THE (max_live_eom
      (parity_runtime_pipeline tops).po_unit.cu_context))) with ps_label_counter := 0))
End
Definition parity_entry_successors_def:
  parity_entry_successors tops = cfg_succs_of (parity_plan_cfg tops)
    (THE (entry_block
      (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions))).bb_label
End
Definition parity_entry_successor_prefix_def:
  parity_entry_successor_prefix tops = THE (generate_succs_plan
    (parity_plan_liveness tops) (parity_plan_dfg tops) (parity_plan_cfg tops)
    (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)
    (SND (parity_entry_plan tops)).ps_stack (SND (parity_entry_plan tops)).ps_spilled
    (TAKE 1 (parity_entry_successors tops))
    [(THE (entry_block
      (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions))).bb_label]
    (SND (parity_entry_plan tops)))
End
Definition parity_runtime_bytes_def:
  parity_runtime_bytes tops = THE (finalize_codegen (K SOME) parity_policy
    (parity_runtime_pipeline tops).po_unit)
End
Definition parity_deploy_unit_def:
  parity_deploy_unit tops = THE (lower_vyper_deploy_unit tops parity_policy
    (parity_runtime_bytes tops))
End
Definition parity_deploy_pipeline_def:
  parity_deploy_pipeline tops = THE (run_venom_pipeline (K T) (K T) (K T)
    parity_policy o1_pipeline_spec (parity_deploy_unit tops))
End

Definition parity_stages_def:
  parity_stages tops <=>
    IS_SOME (resolve_o1_policy (o1_policy all_capabilities)) /\
    IS_SOME (lower_vyper_runtime_unit tops parity_policy) /\
    IS_SOME (run_pipeline_stage parity_policy
      (PS_MapFunctions (CFP_Simple VP_SimplifyCFG)) (parity_runtime_unit tops)
      (init_ir_supply (parity_runtime_unit tops))) /\
    IS_SOME (run_pipeline_stage parity_policy
      (PS_MapFunctions (CFP_Simple VP_DretDesugar))
      (FST (parity_pre0 tops)) (SND (parity_pre0 tops))) /\
    IS_SOME (parity_pass_call tops 0) /\
    IS_SOME (parity_pass_call tops 1) /\
    IS_SOME (parity_pass_call tops 2) /\
    IS_SOME (parity_pass_call tops 3) /\
    IS_SOME (parity_pass_call tops 4) /\
    IS_SOME (parity_pass_call tops 5) /\
    IS_SOME (parity_pass_call tops 6) /\
    IS_SOME (execute_configured_fn_pass parity_policy (CFP_Simple VP_DFT)
      (THE (unit_with_current_fn (parity_walk_unit tops) (FST (parity_pass tops 6))))
      (SND (SND (parity_pass tops 6))) (FST (parity_pass tops 6))) /\
    IS_SOME (parity_pass_call tops 7) /\
    IS_SOME (parity_pass_call tops 8) /\
    IS_SOME (run_configured_fn_passes execute_configured_fn_pass parity_policy
      o1_fn_passes
      (HD (fcg_postorder (fcg_analyze (FST (parity_pre1 tops)).cu_context)
        (THE (FST (parity_pre1 tops)).cu_context.ctx_entry)))
      (parity_walk_unit tops) (SND (parity_pre1 tops))) /\
    IS_SOME (run_callee_first parity_policy o1_fn_passes
      (fcg_postorder (fcg_analyze (FST (parity_pre1 tops)).cu_context)
        (THE (FST (parity_pre1 tops)).cu_context.ctx_entry))
      (parity_walk_unit tops) (SND (parity_pre1 tops))) /\
    codegen_ready (FST (parity_walk_result tops)).cu_context = parity_codegen_ready tops /\
    IS_SOME (run_venom_pipeline (K T) (K T) (K T) parity_policy
      o1_pipeline_spec (parity_runtime_unit tops)) /\
    liveness_analyze (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions) =
      parity_plan_liveness tops /\
    dfg_build_function (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions) =
      parity_plan_dfg tops /\
    cfg_analyze (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions) =
      parity_plan_cfg tops /\
    IS_SOME (generate_block_plan (parity_plan_liveness tops)
      (parity_plan_dfg tops) (parity_plan_cfg tops)
      (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)
      (THE (entry_block (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)))
      ((init_plan_state (THE (max_live_eom
        (parity_runtime_pipeline tops).po_unit.cu_context))) with ps_label_counter := 0)) /\
    IS_SOME (generate_succs_plan (parity_plan_liveness tops) (parity_plan_dfg tops)
      (parity_plan_cfg tops)
      (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions)
      (SND (parity_entry_plan tops)).ps_stack (SND (parity_entry_plan tops)).ps_spilled
      (TAKE 1 (parity_entry_successors tops))
      [(THE (entry_block
        (HD (parity_runtime_pipeline tops).po_unit.cu_context.ctx_functions))).bb_label]
      (SND (parity_entry_plan tops))) /\
    IS_SOME (generate_context_plan (parity_runtime_pipeline tops).po_unit.cu_context) /\
    IS_SOME (codegen_assembly parity_policy (parity_runtime_pipeline tops).po_unit) /\
    IS_SOME (finalize_codegen (K SOME) parity_policy (parity_runtime_pipeline tops).po_unit) /\
    IS_SOME (lower_vyper_deploy_unit tops parity_policy (parity_runtime_bytes tops)) /\
    IS_SOME (run_venom_pipeline (K T) (K T) (K T) parity_policy
      o1_pipeline_spec (parity_deploy_unit tops)) /\
    IS_SOME (generate_context_plan (parity_deploy_pipeline tops).po_unit.cu_context) /\
    IS_SOME (codegen_assembly parity_policy (parity_deploy_pipeline tops).po_unit) /\
    IS_SOME (finalize_codegen (K SOME) parity_policy (parity_deploy_pipeline tops).po_unit)
End
