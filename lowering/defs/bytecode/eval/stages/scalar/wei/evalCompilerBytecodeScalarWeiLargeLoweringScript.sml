(*
 * Exact Python-oracle bytecode checks split from evalCompilerBytecode to keep
 * checked EVAL proof terms within the 12 GB heap boundary.
 *)

Theory evalCompilerBytecodeScalarWeiLargeLowering
Ancestors evalCompilerSubsetScalars compileVyper evalCompilerBytecodeStages venomSupplyEval venomDftEval
  codegenReadyObservations concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib compilerPackagingEvalLib compilerGuardEvalLib
  compilerDftEvalLib compilerReadyEvalLib finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20
val () = compilerPackagingEvalLib.configure ()

val () = evalCompilerBytecodeLib.configure_pass_stages ()
(* Install dispatch metadata before the timed computations; this performs
   no evaluation and contributes no compiler certificate. *)
val () = app (fn head => evalCompilerBytecodeLib.ensure_certificate_head head 2)
  [``parity_pass_call``, ``parity_pass``, ``sue_expand_function_supply``,
   ``make_ssa_current_fn``]
val () = evalCompilerBytecodeLib.ensure_certificate_head ``dft_fn`` 1
val () = evalCompilerBytecodeLib.ensure_certificate_head ``run_venom_pipeline`` 6
val () = evalCompilerBytecodeLib.ensure_certificate_head ``parity_runtime_pipeline`` 1

Theorem scalar_wei_large_lowered:
  IS_SOME (resolve_o1_policy (o1_policy all_capabilities)) /\
  IS_SOME (lower_vyper_runtime_unit scalar_wei_large_program parity_policy)
Proof
  CONJ_TAC >- evalCompilerBytecodeLib.cache_checkpoint >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_wei_large_pre0_some:
  IS_SOME (run_pipeline_stage parity_policy
    (PS_MapFunctions (CFP_Simple VP_SimplifyCFG))
    (parity_runtime_unit scalar_wei_large_program)
    (init_ir_supply (parity_runtime_unit scalar_wei_large_program)))
Proof
  evalCompilerBytecodeLib.prepare_closed_call
    ``simplify_cfg_fn_with_labels
      (HD (parity_runtime_unit scalar_wei_large_program).cu_context.ctx_functions)`` >>
  evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
  evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
  evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
  evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >> evalCompilerBytecodeLib.warm_schedule_step >>
  evalCompilerBytecodeLib.cache_checkpoint
QED

Theorem scalar_wei_large_pre1_some:
  IS_SOME (run_pipeline_stage parity_policy
    (PS_MapFunctions (CFP_Simple VP_DretDesugar))
    (FST (parity_pre0 scalar_wei_large_program))
    (SND (parity_pre0 scalar_wei_large_program)))
Proof
  evalCompilerBytecodeLib.cache_checkpoint
QED

val () = app (fn (name,theorem) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag theorem)
in if null (Thm.hyp theorem) andalso null axioms andalso
      List.all (fn oracle => oracle = "DISK_THM") oracles then
    print ("WEI_LARGE_PREFIX_KERNEL_CLOSED " ^ name ^ " hyp=0\n")
  else raise Fail "Wei prefix has kernel assumptions or admission tags"
end) [("scalar_wei_large_lowered",scalar_wei_large_lowered),
       ("scalar_wei_large_pre0_some",scalar_wei_large_pre0_some),
       ("scalar_wei_large_pre1_some",scalar_wei_large_pre1_some)]
val () = evalCompilerBytecodeLib.pending_stage_values :=
  List.filter (fn (named,equation) => Option.isSome named orelse
    optionSyntax.is_some (rhs (concl equation)))
    (!evalCompilerBytecodeLib.pending_stage_values)
val () = evalCompilerBytecodeLib.publish_stage_values ()
val () = evalCompilerBytecodeLib.compiler_certificates := []
