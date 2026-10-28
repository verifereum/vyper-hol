(*
 * Exact Python-oracle bytecode checks split from evalCompilerBytecode to keep
 * checked EVAL proof terms within the 12 GB heap boundary.
 *)

Theory evalCompilerBytecodeMixedEventStages
Ancestors evalCompiler compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Definition control_log_policy_def:
  control_log_policy = THE (resolve_o1_policy (o1_policy all_capabilities))
End
Theorem control_log_policy_some:
  resolve_o1_policy (o1_policy all_capabilities) = SOME control_log_policy
Proof
  evalCompilerBytecodeLib.cache_stage control_log_policy_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_runtime_unit_def:
  control_log_runtime_unit =
    THE (lower_vyper_runtime_unit mixed_event_log_program control_log_policy)
End
Theorem control_log_runtime_unit_some:
  lower_vyper_runtime_unit mixed_event_log_program control_log_policy =
    SOME control_log_runtime_unit
Proof
  evalCompilerBytecodeLib.cache_stage control_log_runtime_unit_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()


(* Cache the actual pre-walk and guarded function-pass boundaries. *)
val () = evalCompilerBytecodeLib.configure_pass_stages ();

Definition control_log_pre0_def:
  control_log_pre0 = THE (run_pipeline_stage control_log_policy
    (PS_MapFunctions (CFP_Simple VP_SimplifyCFG))
    control_log_runtime_unit (init_ir_supply control_log_runtime_unit))
End
Theorem control_log_pre0_some:
  run_pipeline_stage control_log_policy (PS_MapFunctions (CFP_Simple VP_SimplifyCFG))
    control_log_runtime_unit (init_ir_supply control_log_runtime_unit) =
    SOME control_log_pre0
Proof
  evalCompilerBytecodeLib.cache_stage control_log_pre0_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_pre1_def:
  control_log_pre1 = THE (run_pipeline_stage control_log_policy
    (PS_MapFunctions (CFP_Simple VP_DretDesugar)) (FST control_log_pre0) (SND control_log_pre0))
End
Theorem control_log_pre1_some:
  run_pipeline_stage control_log_policy (PS_MapFunctions (CFP_Simple VP_DretDesugar))
    (FST control_log_pre0) (SND control_log_pre0) = SOME control_log_pre1
Proof
  evalCompilerBytecodeLib.cache_stage control_log_pre1_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk_unit_def:
  control_log_walk_unit = prune_unit_fcg_unreachable (FST control_log_pre1)
    (fcg_analyze (FST control_log_pre1).cu_context)
End
Definition control_log_function_name_def:
  control_log_function_name = HD (fcg_postorder
    (fcg_analyze (FST control_log_pre1).cu_context)
    (THE (FST control_log_pre1).cu_context.ctx_entry))
End
Definition control_log_initial_function_def:
  control_log_initial_function = THE (lookup_unique_function control_log_function_name
    control_log_walk_unit.cu_context.ctx_functions)
End
Theorem control_log_initial_function_some:
  lookup_unique_function control_log_function_name
    control_log_walk_unit.cu_context.ctx_functions = SOME control_log_initial_function
Proof
  evalCompilerBytecodeLib.cache_stage control_log_initial_function_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk0_def:
  control_log_walk0 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_MakeSSA] control_log_walk_unit (SND control_log_pre1)
    control_log_initial_function [])
End
Theorem control_log_walk0_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_MakeSSA] control_log_walk_unit (SND control_log_pre1)
    control_log_initial_function [] = SOME control_log_walk0
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk0_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk1_def:
  control_log_walk1 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_LowerDload] control_log_walk_unit (SND (SND control_log_walk0))
    (FST control_log_walk0) (FST (SND control_log_walk0)))
End
Theorem control_log_walk1_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_LowerDload] control_log_walk_unit (SND (SND control_log_walk0))
    (FST control_log_walk0) (FST (SND control_log_walk0)) = SOME control_log_walk1
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk1_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk2_def:
  control_log_walk2 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_ConcretizeMemLoc] control_log_walk_unit (SND (SND control_log_walk1))
    (FST control_log_walk1) (FST (SND control_log_walk1)))
End
Theorem control_log_walk2_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_ConcretizeMemLoc] control_log_walk_unit (SND (SND control_log_walk1))
    (FST control_log_walk1) (FST (SND control_log_walk1)) = SOME control_log_walk2
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk2_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk3_def:
  control_log_walk3 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_FmpLowering] control_log_walk_unit (SND (SND control_log_walk2))
    (FST control_log_walk2) (FST (SND control_log_walk2)))
End
Theorem control_log_walk3_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_FmpLowering] control_log_walk_unit (SND (SND control_log_walk2))
    (FST control_log_walk2) (FST (SND control_log_walk2)) = SOME control_log_walk3
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk3_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk4_def:
  control_log_walk4 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_MakeSSA] control_log_walk_unit (SND (SND control_log_walk3))
    (FST control_log_walk3) (FST (SND control_log_walk3)))
End
Theorem control_log_walk4_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_MakeSSA] control_log_walk_unit (SND (SND control_log_walk3))
    (FST control_log_walk3) (FST (SND control_log_walk3)) = SOME control_log_walk4
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk4_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk5_def:
  control_log_walk5 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_SimplifyCFG] control_log_walk_unit (SND (SND control_log_walk4))
    (FST control_log_walk4) (FST (SND control_log_walk4)))
End
Theorem control_log_walk5_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_SimplifyCFG] control_log_walk_unit (SND (SND control_log_walk4))
    (FST control_log_walk4) (FST (SND control_log_walk4)) = SOME control_log_walk5
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk5_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk6_def:
  control_log_walk6 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_SingleUseExpansion] control_log_walk_unit (SND (SND control_log_walk5))
    (FST control_log_walk5) (FST (SND control_log_walk5)))
End
Theorem control_log_walk6_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_SingleUseExpansion] control_log_walk_unit (SND (SND control_log_walk5))
    (FST control_log_walk5) (FST (SND control_log_walk5)) = SOME control_log_walk6
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk6_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_dft_def:
  control_log_dft = dft_fn (FST control_log_walk6)
End
Theorem control_log_dft_eq:
  dft_fn (FST control_log_walk6) = control_log_dft
Proof
  evalCompilerBytecodeLib.cache_value control_log_dft_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk7_def:
  control_log_walk7 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_DFT] control_log_walk_unit (SND (SND control_log_walk6))
    (FST control_log_walk6) (FST (SND control_log_walk6)))
End
Theorem control_log_walk7_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_DFT] control_log_walk_unit (SND (SND control_log_walk6))
    (FST control_log_walk6) (FST (SND control_log_walk6)) = SOME control_log_walk7
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk7_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk8_def:
  control_log_walk8 = THE (run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_CFGNormalization] control_log_walk_unit (SND (SND control_log_walk7))
    (FST control_log_walk7) (FST (SND control_log_walk7)))
End
Theorem control_log_walk8_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    [CFP_Simple VP_CFGNormalization] control_log_walk_unit (SND (SND control_log_walk7))
    (FST control_log_walk7) (FST (SND control_log_walk7)) = SOME control_log_walk8
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk8_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Theorem control_log_fold_some:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    o1_pipeline_spec.ps_fn_passes control_log_walk_unit (SND control_log_pre1)
    control_log_initial_function [] = SOME control_log_walk8
Proof
  simp[venomPassScheduleTheory.o1_pipeline_spec_def,
       venomPassScheduleTheory.o1_fn_passes_def,
       venomFnScheduleEvalTheory.run_configured_fn_pass_fold_two,
       control_log_walk0_some, control_log_walk1_some, control_log_walk2_some,
       control_log_walk3_some, control_log_walk4_some, control_log_walk5_some,
       control_log_walk6_some, control_log_walk7_some, control_log_walk8_some,
       pairTheory.pair_CASE_def]
QED
val () = evalCompilerBytecodeLib.add_compile_eval control_log_fold_some

Theorem control_log_fold_compute:
  run_configured_fn_pass_fold execute_configured_fn_pass control_log_policy
    o1_pipeline_spec.ps_fn_passes control_log_walk_unit (SND control_log_pre1)
    control_log_initial_function [] = SOME control_log_walk8
Proof
  EVAL_TAC
QED

Definition control_log_scheduled_def:
  control_log_scheduled = THE (run_configured_fn_passes execute_configured_fn_pass
    control_log_policy o1_pipeline_spec.ps_fn_passes control_log_function_name
    control_log_walk_unit (SND control_log_pre1))
End
Theorem control_log_scheduled_some:
  run_configured_fn_passes execute_configured_fn_pass control_log_policy
    o1_pipeline_spec.ps_fn_passes control_log_function_name
    control_log_walk_unit (SND control_log_pre1) = SOME control_log_scheduled
Proof
  evalCompilerBytecodeLib.cache_stage control_log_scheduled_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_walk_def:
  control_log_walk = THE (run_callee_first control_log_policy
    o1_pipeline_spec.ps_fn_passes
    (fcg_postorder (fcg_analyze (FST control_log_pre1).cu_context)
      (THE (FST control_log_pre1).cu_context.ctx_entry))
    control_log_walk_unit (SND control_log_pre1))
End
Theorem control_log_walk_some:
  run_callee_first control_log_policy o1_pipeline_spec.ps_fn_passes
    (fcg_postorder (fcg_analyze (FST control_log_pre1).cu_context)
      (THE (FST control_log_pre1).cu_context.ctx_entry))
    control_log_walk_unit (SND control_log_pre1) = SOME control_log_walk
Proof
  evalCompilerBytecodeLib.cache_stage control_log_walk_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_runtime_pipeline_def:
  control_log_runtime_pipeline =
    THE (run_venom_pipeline (K T) (K T) (K T) control_log_policy
      o1_pipeline_spec control_log_runtime_unit)
End
Theorem control_log_runtime_pipeline_some:
  run_venom_pipeline (K T) (K T) (K T) control_log_policy
    o1_pipeline_spec control_log_runtime_unit = SOME control_log_runtime_pipeline
Proof
  evalCompilerBytecodeLib.cache_stage control_log_runtime_pipeline_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_runtime_plan_def:
  control_log_runtime_plan = THE (generate_context_plan
    control_log_runtime_pipeline.po_unit.cu_context)
End
Theorem control_log_runtime_plan_some:
  generate_context_plan control_log_runtime_pipeline.po_unit.cu_context =
    SOME control_log_runtime_plan
Proof
  evalCompilerBytecodeLib.cache_stage control_log_runtime_plan_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_runtime_assembly_def:
  control_log_runtime_assembly = THE (codegen_assembly control_log_policy
    control_log_runtime_pipeline.po_unit)
End
Theorem control_log_runtime_assembly_some:
  codegen_assembly control_log_policy control_log_runtime_pipeline.po_unit =
    SOME control_log_runtime_assembly
Proof
  evalCompilerBytecodeLib.cache_stage control_log_runtime_assembly_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_runtime_bytes_def:
  control_log_runtime_bytes =
    THE (finalize_codegen (K SOME) control_log_policy control_log_runtime_pipeline.po_unit)
End
Theorem control_log_runtime_bytes_some:
  finalize_codegen (K SOME) control_log_policy control_log_runtime_pipeline.po_unit =
    SOME control_log_runtime_bytes
Proof
  evalCompilerBytecodeLib.cache_stage control_log_runtime_bytes_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_deploy_unit_def:
  control_log_deploy_unit = THE (lower_vyper_deploy_unit mixed_event_log_program
    control_log_policy control_log_runtime_bytes)
End
Theorem control_log_deploy_unit_some:
  lower_vyper_deploy_unit mixed_event_log_program control_log_policy
    control_log_runtime_bytes = SOME control_log_deploy_unit
Proof
  evalCompilerBytecodeLib.cache_stage control_log_deploy_unit_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_deploy_pipeline_def:
  control_log_deploy_pipeline =
    THE (run_venom_pipeline (K T) (K T) (K T) control_log_policy
      o1_pipeline_spec control_log_deploy_unit)
End
Theorem control_log_deploy_pipeline_some:
  run_venom_pipeline (K T) (K T) (K T) control_log_policy
    o1_pipeline_spec control_log_deploy_unit = SOME control_log_deploy_pipeline
Proof
  evalCompilerBytecodeLib.cache_stage control_log_deploy_pipeline_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()

Definition control_log_deploy_bytes_def:
  control_log_deploy_bytes =
    THE (finalize_codegen (K SOME) control_log_policy control_log_deploy_pipeline.po_unit)
End
Theorem control_log_deploy_bytes_some:
  finalize_codegen (K SOME) control_log_policy control_log_deploy_pipeline.po_unit =
    SOME control_log_deploy_bytes
Proof
  evalCompilerBytecodeLib.cache_stage control_log_deploy_bytes_def
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()


