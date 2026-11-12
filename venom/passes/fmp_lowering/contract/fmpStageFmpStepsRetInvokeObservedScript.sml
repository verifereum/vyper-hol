Theory fmpStageFmpStepsRetInvokeObserved
Ancestors
  fmpStageRel fmpStepBridge concretizeStageLookup fmpLowerProps
  fmpAnalysisProps venomPassDispatcher venomPassSchedule o1PassContract
  venomInst fmpAnalysisDefs fmpLowerDefs list

Theorem fmp_return_nonfmp_step_signature:
  fn_pass_step rp pass observed s g out /\
  fn_pass_tag pass <> VP_FmpLowering ==>
  out.fpo_function.fn_fmp_signature = g.fn_fmp_signature
Proof
  strip_tac >>
  gvs[fn_pass_step_def, fn_pass_effects_hold_def, fn_abi_effect_holds_def] >>
  Cases_on `fn_pass_tag pass` >>
  gvs[fn_pass_abi_effect_def, fn_fmp_convention_eq_def]
QED

Theorem fmp_return_nonfmp_steps_signature:
  !passes g h. fn_steps rp passes g h /\
  EVERY (\p. fn_pass_tag p <> VP_FmpLowering) passes ==>
  h.fn_fmp_signature = g.fn_fmp_signature
Proof
  Induct >> simp[fn_steps_def] >> rpt strip_tac >>
  drule_all fmp_return_nonfmp_step_signature >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem fmp_return_scan_nonpublishing:
  !insts. EVERY (\i. pre_fmp_opcode i.inst_opcode) insts ==>
  ~(fmp_scan_insts insts).fi_publishes_fmp
Proof
  Induct >> simp[fmp_scan_insts_def, fmp_info_bottom_def,
    fmp_info_join_def] >> rpt strip_tac >>
  gvs[pre_fmp_opcode_def, fmp_opcode_publishes_fmp_def]
QED

Theorem fmp_return_lower_nonpublishing:
  fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  ?sig. fn'.fn_fmp_signature = SOME sig /\ ~sig.fms_publishes
Proof
  strip_tac >>
  `~(fmp_direct_info fn).fi_publishes_fmp` by
    (gvs[pre_fmp_ops_def, fmp_direct_info_def] >>
     irule fmp_return_scan_nonpublishing >> simp[]) >>
  `?infos info. analyze_fmp_context ctx = SOME infos /\
     fmp_lower_input infos ctx fn /\
     FLOOKUP infos fn.fn_name = SOME info` by
    (gvs[fmp_lower_function_def, fmp_lower_function_with_info_def,
      AllCaseEqs()] >> metis_tac[]) >>
  `MEM fn ctx.ctx_functions` by
    (gvs[fmp_lower_input_def] >> metis_tac[lookup_function_MEM]) >>
  drule_all analyze_fmp_context_unsealed_publishes_iff >> strip_tac >>
  drule_all fmp_lower_function_seals_signature_exact >> simp[]
QED

Theorem fmp_return_stage_callee_signature:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) view C C' /\
  fmp_free_ctx C /\ lookup_function name C.ctx_functions = SOME fn ==>
  ?fn' sig. lookup_function name C'.ctx_functions = SOME fn' /\
    fn'.fn_fmp_signature = SOME sig /\ ~sig.fms_publishes
Proof
  strip_tac >> drule_all ctx_pass_stage_lookup >> strip_tac >>
  `fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn` by
    (gvs[fmp_free_ctx_def, EVERY_MEM] >>
     metis_tac[lookup_function_MEM]) >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  drule_all fmp_return_lower_nonpublishing >> metis_tac[]
QED

Theorem fmp_return_observed_callee_nonpublishing:
  fmp_stage_ctx rp D C C' vs vs' fmp eom /\
  o1_walk_view rp 3 C' fn observed /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name observed.cu_context.ctx_functions = SOME g ==>
  ?sig. g.fn_fmp_signature = SOME sig /\ ~sig.fms_publishes
Proof
  strip_tac >>
  `MEM name (ctx_fn_names observed.cu_context)` by
    (drule lookup_function_MEM >> drule lookup_function_name >>
     rpt strip_tac >> pure_rewrite_tac[ctx_fn_names_def, MEM_MAP] >>
     metis_tac[]) >>
  `MEM name (ctx_fn_names C)` by metis_tac[] >>
  `?src. lookup_function name C.ctx_functions = SOME src` by
    (Cases_on `lookup_function name C.ctx_functions` >>
     gvs[ctx_fn_names_def] >> metis_tac[lookup_function_not_mem]) >>
  `fmp_free_ctx C` by
    gvs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def] >>
  `?dst sig. lookup_function name C'.ctx_functions = SOME dst /\
     dst.fn_fmp_signature = SOME sig /\ ~sig.fms_publishes` by
    (irule fmp_return_stage_callee_signature >>
     gvs[fmp_stage_ctx_def] >> metis_tac[]) >>
  qpat_x_assum `o1_walk_view rp 3 C' fn observed` mp_tac >>
  simp[o1_walk_view_def, walk_view_def] >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  drule fmp_return_nonfmp_steps_signature >>
  simp[o1_fn_passes_def, fn_pass_tag_def] >> metis_tac[]
QED
