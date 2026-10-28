(*
 * Exact Python-oracle bytecode checks split from evalCompilerBytecode to keep
 * checked EVAL proof terms within the 12 GB heap boundary.
 *)

Theory evalCompilerBytecodeScalarWeiSmallStages
Ancestors evalCompilerBytecodeScalarWeiSmallRuntimeStages evalCompilerBytecodeScalarWeiSmallPipelineStages evalCompilerSubsetScalars compileVyper evalCompilerBytecodeStages venomSupplyEval venomDftEval
  codegenReadyObservations stackPlanCleanupCases concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib compilerGuardEvalLib
  compilerDftEvalLib compilerReadyEvalLib compilerPlannerEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()

val () = evalCompilerBytecodeLib.configure_pass_stages ()
val () = compilerPlannerEvalLib.configure ()
val () = app (fn (head,arity) =>
  evalCompilerBytecodeLib.ensure_certificate_head head arity)
  [(``codegen_assembly``,2), (``finalize_codegen``,3),
   (``compute_label_offsets``,1), (``assemble``,1)]
(* Install dispatch metadata before the timed computations; this performs
   no evaluation and contributes no compiler certificate. *)
val () = app (fn head => evalCompilerBytecodeLib.ensure_certificate_head head 2)
  [``parity_pass_call``, ``parity_pass``, ``sue_expand_function_supply``,
   ``make_ssa_current_fn``]
val () = evalCompilerBytecodeLib.ensure_certificate_head ``dft_fn`` 1
val () = evalCompilerBytecodeLib.ensure_certificate_head ``run_venom_pipeline`` 6
val () = evalCompilerBytecodeLib.ensure_certificate_head ``parity_runtime_pipeline`` 1

val () = evalCompilerBytecodeLib.restore_stage_values "evalCompilerBytecodeScalarWeiSmallPipelineStages"
val () = evalCompilerBytecodeLib.restore_stage_values "evalCompilerBytecodeScalarWeiSmallRuntimeStages"

Theorem scalar_wei_small_deploy_inputs:
  IS_SOME (codegen_assembly parity_policy
    (parity_runtime_pipeline scalar_wei_small_program).po_unit) /\
  IS_SOME (finalize_codegen (K SOME) parity_policy
    (parity_runtime_pipeline scalar_wei_small_program).po_unit) /\
  IS_SOME (lower_vyper_deploy_unit scalar_wei_small_program parity_policy
    (parity_runtime_bytes scalar_wei_small_program)) /\
  IS_SOME (run_venom_pipeline (K T) (K T) (K T) parity_policy
    o1_pipeline_spec (parity_deploy_unit scalar_wei_small_program))
Proof
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``compute_label_offsets (THE (codegen_assembly parity_policy
      (parity_runtime_pipeline scalar_wei_small_program).po_unit))`` >>
  evalCompilerBytecodeLib.prepare_closed_call
    ``assemble (THE (codegen_assembly parity_policy
      (parity_runtime_pipeline scalar_wei_small_program).po_unit))`` >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_wei_small_deploy_plan_some:
  IS_SOME (generate_context_plan
    (parity_deploy_pipeline scalar_wei_small_program).po_unit.cu_context)
Proof
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >> compilerPlannerEvalLib.warm_step >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_wei_small_stages:
  parity_stages scalar_wei_small_program
Proof
  rewrite_tac[parity_stages_def] >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- ACCEPT_TAC scalar_wei_small_pre0_some >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- ACCEPT_TAC scalar_wei_small_sue_some >>
  CONJ_TAC >- ACCEPT_TAC scalar_wei_small_dft_call_some >>
  CONJ_TAC >- ACCEPT_TAC scalar_wei_small_dft_some >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- (evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
    evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
    evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
    evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
    evalCompilerBytecodeLib.cache_checkpoint) >>
  CONJ_TAC >- ACCEPT_TAC scalar_wei_small_ready >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- ACCEPT_TAC scalar_wei_small_successor_some >>
  CONJ_TAC >- ACCEPT_TAC scalar_wei_small_runtime_plan_some >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  CONJ_TAC >- ACCEPT_TAC scalar_wei_small_deploy_plan_some >>
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.cache_checkpoint
QED
val () = evalCompilerBytecodeLib.publish_stage_values ()
