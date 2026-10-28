(*
 * Exact Python-oracle bytecode checks split from evalCompilerBytecode to keep
 * checked EVAL proof terms within the 12 GB heap boundary.
 *)

Theory evalCompilerBytecodeScalarModularPipelineStages
Ancestors evalCompilerSubsetScalars compileVyper evalCompilerBytecodeStages venomSupplyEval venomDftEval
  codegenReadyObservations concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib compilerGuardEvalLib compilerModularDftEvalLib
  compilerDftEvalLib compilerReadyEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()

val () = evalCompilerBytecodeLib.configure_pass_stages ()
val () = compilerModularDftEvalLib.configure ()
(* Install dispatch metadata before the timed computations; this performs
   no evaluation and contributes no compiler certificate. *)
val () = app (fn head => evalCompilerBytecodeLib.ensure_certificate_head head 2)
  [``parity_pass_call``, ``parity_pass``, ``sue_expand_function_supply``,
   ``make_ssa_current_fn``]
val () = evalCompilerBytecodeLib.ensure_certificate_head ``dft_fn`` 1
val () = evalCompilerBytecodeLib.ensure_certificate_head ``run_venom_pipeline`` 6
val () = evalCompilerBytecodeLib.ensure_certificate_head ``parity_runtime_pipeline`` 1

Theorem scalar_modular_lowered:
  IS_SOME (resolve_o1_policy (o1_policy all_capabilities)) /\
  IS_SOME (lower_vyper_runtime_unit scalar_modular_program parity_policy)
Proof
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_modular_pre0_some:
  IS_SOME (run_pipeline_stage parity_policy
    (PS_MapFunctions (CFP_Simple VP_SimplifyCFG))
    (parity_runtime_unit scalar_modular_program)
    (init_ir_supply (parity_runtime_unit scalar_modular_program)))
Proof
  evalCompilerBytecodeLib.prepare_closed_call
    ``simplify_cfg_fn_with_labels
      (HD (parity_runtime_unit scalar_modular_program).cu_context.ctx_functions)`` >>
  evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
  evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
  evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
  evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_modular_pre1_some:
  IS_SOME (run_pipeline_stage parity_policy
    (PS_MapFunctions (CFP_Simple VP_DretDesugar))
    (FST (parity_pre0 scalar_modular_program))
    (SND (parity_pre0 scalar_modular_program)))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_modular_first_passes:
  IS_SOME (parity_pass_call scalar_modular_program 0) /\
  IS_SOME (parity_pass_call scalar_modular_program 1) /\
  IS_SOME (parity_pass_call scalar_modular_program 2) /\
  IS_SOME (parity_pass_call scalar_modular_program 3) /\
  IS_SOME (parity_pass_call scalar_modular_program 4) /\
  IS_SOME (parity_pass_call scalar_modular_program 5)
Proof
  evalCompilerBytecodeLib.prepare_closed_call
    ``cfg_analyze (parity_initial_function scalar_modular_program)`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``dom_analyze (cfg_analyze (parity_initial_function scalar_modular_program))
      (parity_initial_function scalar_modular_program)`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``liveness_analyze (parity_initial_function scalar_modular_program)`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``make_ssa_current_fn (SND (parity_pre1 scalar_modular_program))
      (parity_initial_function scalar_modular_program)`` >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``execute_configured_fn_pass parity_policy (CFP_Simple VP_ConcretizeMemLoc)
      (THE (unit_with_current_fn (parity_walk_unit scalar_modular_program)
        (FST (parity_pass scalar_modular_program 1))))
      (SND (SND (parity_pass scalar_modular_program 1)))
      (FST (parity_pass scalar_modular_program 1))`` >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``cfg_analyze (FST (parity_pass scalar_modular_program 3))`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``dom_analyze (cfg_analyze (FST (parity_pass scalar_modular_program 3)))
      (FST (parity_pass scalar_modular_program 3))`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``liveness_analyze (FST (parity_pass scalar_modular_program 3))`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``make_ssa_current_fn (SND (SND (parity_pass scalar_modular_program 3)))
      (FST (parity_pass scalar_modular_program 3))`` >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``simplify_cfg_fn_with_labels (FST (parity_pass scalar_modular_program 4))`` >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Definition scalar_modular_sue_result_def:
  scalar_modular_sue_result = sue_expand_function_supply
    (SND (SND (parity_pass scalar_modular_program 5)))
    (FST (parity_pass scalar_modular_program 5))
End

Definition scalar_modular_sue_unit_def:
  scalar_modular_sue_unit = THE
    (unit_with_current_fn (parity_walk_unit scalar_modular_program)
      (FST (parity_pass scalar_modular_program 5)))
End

fun warm_sue_vars_subset goal = compilerGuardEvalLib.warm_subset
  ``list_subset (fn_ir_vars (FST scalar_modular_sue_result))
    (SND scalar_modular_sue_result).irs_used_vars`` goal

Theorem scalar_modular_sue_some:
  IS_SOME (parity_pass_call scalar_modular_program 6)
Proof
  evalCompilerBytecodeLib.prepare_closed_call
    ``dfg_build_function (FST (parity_pass scalar_modular_program 5))`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``sue_expand_function_supply (SND (SND (parity_pass scalar_modular_program 5)))
      (FST (parity_pass scalar_modular_program 5))`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``ir_supply_extends (SND (SND (parity_pass scalar_modular_program 5)))
      (SND scalar_modular_sue_result)`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``list_subset (fn_ir_inst_ids (FST scalar_modular_sue_result))
      (SND scalar_modular_sue_result).irs_used_inst_ids`` >>
  warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >>
  warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >>
  warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >>
  warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >>
  warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >>
  warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >>
  warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >>
  warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >> warm_sue_vars_subset >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``list_subset (fn_ir_labels (FST scalar_modular_sue_result))
      (SND scalar_modular_sue_result).irs_used_labels`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``ir_supply_covers_fn (SND scalar_modular_sue_result)
      (FST scalar_modular_sue_result)`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``list_subset (unit_ir_inst_ids scalar_modular_sue_unit)
      (SND scalar_modular_sue_result).irs_used_inst_ids`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``list_subset (unit_ir_vars scalar_modular_sue_unit)
      (SND scalar_modular_sue_result).irs_used_vars`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``list_subset (unit_ir_labels scalar_modular_sue_unit)
      (SND scalar_modular_sue_result).irs_used_labels`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``ir_supply_covers_unit (SND scalar_modular_sue_result)
      scalar_modular_sue_unit`` >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

fun warm_modular_dft goal = compilerModularDftEvalLib.warm_call
  ``dft_fn (FST (parity_pass scalar_modular_program 6))`` goal

Theorem scalar_modular_dft_call_some:
  IS_SOME (execute_configured_fn_pass parity_policy (CFP_Simple VP_DFT)
    (THE (unit_with_current_fn (parity_walk_unit scalar_modular_program)
      (FST (parity_pass scalar_modular_program 6))))
    (SND (SND (parity_pass scalar_modular_program 6)))
    (FST (parity_pass scalar_modular_program 6)))
Proof
  evalCompilerBytecodeLib.prepare_function_analysis ``liveness_analyze`` >>
  evalCompilerBytecodeLib.prepare_function_analysis ``cfg_analyze`` >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >> warm_modular_dft >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Definition scalar_modular_dft_function_def:
  scalar_modular_dft_function = dft_fn (FST (parity_pass scalar_modular_program 6))
End

Definition scalar_modular_dft_unit_def:
  scalar_modular_dft_unit = THE
    (unit_with_current_fn (parity_walk_unit scalar_modular_program)
      (FST (parity_pass scalar_modular_program 6)))
End

fun warm_dft_vars_subset goal = compilerGuardEvalLib.warm_subset
  ``list_subset (fn_ir_vars scalar_modular_dft_function)
    (SND (SND (parity_pass scalar_modular_program 6))).irs_used_vars`` goal

Theorem scalar_modular_dft_some:
  IS_SOME (parity_pass_call scalar_modular_program 7)
Proof
  evalCompilerBytecodeLib.prepare_closed_call
    ``list_subset (fn_ir_inst_ids scalar_modular_dft_function)
      (SND (SND (parity_pass scalar_modular_program 6))).irs_used_inst_ids`` >>
  warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >>
  warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >>
  warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >>
  warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >>
  warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >>
  warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >>
  warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >>
  warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >> warm_dft_vars_subset >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``list_subset (fn_ir_labels scalar_modular_dft_function)
      (SND (SND (parity_pass scalar_modular_program 6))).irs_used_labels`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``ir_supply_covers_fn (SND (SND (parity_pass scalar_modular_program 6)))
      scalar_modular_dft_function`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``ir_supply_covers_unit (SND (SND (parity_pass scalar_modular_program 6)))
      scalar_modular_dft_unit`` >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_modular_schedule_some:
  IS_SOME (parity_pass_call scalar_modular_program 8) /\
  IS_SOME (run_configured_fn_passes execute_configured_fn_pass parity_policy
    o1_fn_passes
    (HD (fcg_postorder (fcg_analyze (FST (parity_pre1 scalar_modular_program)).cu_context)
      (THE (FST (parity_pre1 scalar_modular_program)).cu_context.ctx_entry)))
    (parity_walk_unit scalar_modular_program) (SND (parity_pre1 scalar_modular_program))) /\
  IS_SOME (run_callee_first parity_policy o1_fn_passes
    (fcg_postorder (fcg_analyze (FST (parity_pre1 scalar_modular_program)).cu_context)
      (THE (FST (parity_pre1 scalar_modular_program)).cu_context.ctx_entry))
    (parity_walk_unit scalar_modular_program) (SND (parity_pre1 scalar_modular_program)))
Proof
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Definition scalar_modular_final_function_def:
  scalar_modular_final_function =
    HD (FST (parity_walk_result scalar_modular_program)).cu_context.ctx_functions
End

fun warm_modular_readiness goal = compilerReadyEvalLib.warm_blocks
  ``HD (FST (parity_walk_result scalar_modular_program)).cu_context.ctx_functions`` goal

fun warm_modular_uses goal = compilerReadyEvalLib.warm_uses
  ``scalar_modular_final_function`` goal

Theorem scalar_modular_ready:
  codegen_ready (FST (parity_walk_result scalar_modular_program)).cu_context =
    parity_codegen_ready scalar_modular_program
Proof
  evalCompilerBytecodeLib.prepare_closed_call
    ``cfg_analyze
      (HD (FST (parity_walk_result scalar_modular_program)).cu_context.ctx_functions)`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``dom_analyze (cfg_analyze
      (HD (FST (parity_walk_result scalar_modular_program)).cu_context.ctx_functions))
      (HD (FST (parity_walk_result scalar_modular_program)).cu_context.ctx_functions)`` >>
  warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >>
  warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >>
  warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >>
  warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >>
  warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >>
  warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >>
  warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >>
  warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >> warm_modular_readiness >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``def_dominates_uses
      (HD (FST (parity_walk_result scalar_modular_program)).cu_context.ctx_functions)`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``canonical_param_prefix scalar_modular_final_function`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``wf_function scalar_modular_final_function`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``fn_inst_wf scalar_modular_final_function`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``ssa_form scalar_modular_final_function`` >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >> warm_modular_uses >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``single_use_form scalar_modular_final_function`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``cfg_is_normalized (cfg_analyze scalar_modular_final_function)
      scalar_modular_final_function`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``codegen_ready_fn scalar_modular_final_function`` >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_modular_plan_inputs:
  IS_SOME (run_venom_pipeline (K T) (K T) (K T) parity_policy
      o1_pipeline_spec (parity_runtime_unit scalar_modular_program)) /\
  liveness_analyze (HD (parity_runtime_pipeline scalar_modular_program).po_unit.cu_context.ctx_functions) =
      parity_plan_liveness scalar_modular_program /\
  dfg_build_function (HD (parity_runtime_pipeline scalar_modular_program).po_unit.cu_context.ctx_functions) =
      parity_plan_dfg scalar_modular_program /\
  cfg_analyze (HD (parity_runtime_pipeline scalar_modular_program).po_unit.cu_context.ctx_functions) =
      parity_plan_cfg scalar_modular_program /\
  IS_SOME (generate_block_plan (parity_plan_liveness scalar_modular_program)
      (parity_plan_dfg scalar_modular_program) (parity_plan_cfg scalar_modular_program)
      (HD (parity_runtime_pipeline scalar_modular_program).po_unit.cu_context.ctx_functions)
      (THE (entry_block (HD (parity_runtime_pipeline scalar_modular_program).po_unit.cu_context.ctx_functions)))
      ((init_plan_state (THE (max_live_eom
        (parity_runtime_pipeline scalar_modular_program).po_unit.cu_context))) with ps_label_counter := 0))
Proof
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = evalCompilerBytecodeLib.publish_stage_values ()
