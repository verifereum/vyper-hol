Theory fmpCoverObservedPublish
Ancestors
  fmpStageOpBaseActual fmpStageRel fmpStepBridge fmpAnalysisProps fmpAnalysisDefs fmpLowerDefs
  o1PassContract venomPassDispatcher venomPassSchedule venomInst list finite_map
  concretizeStageLookup fmpLowerProps venomWf venomFnScheduleRunner venomFnScheduleRunnerProps fcgBridge

Theorem fmp_cover_step_signature[local]:
  fn_pass_step rpolicy pass observed s fn out /\
  fn_pass_tag pass <> VP_FmpLowering ==>
  out.fpo_function.fn_fmp_signature = fn.fn_fmp_signature
Proof
  rw[fn_pass_step_def, fn_pass_effects_hold_def, fn_abi_effect_holds_def,
     fn_fmp_convention_eq_def] >>
  Cases_on `fn_pass_tag pass` >> gvs[fn_pass_abi_effect_def]
QED

Theorem fmp_cover_direct_nonpublish[local]:
  pre_fmp_ops fn ==> ~(fmp_direct_info fn).fi_publishes_fmp
Proof
  simp[pre_fmp_ops_def, fmp_direct_info_def] >>
  qspec_tac (`fn_insts fn`, `insts`) >> Induct >>
  simp[fmp_scan_insts_def, fmp_info_bottom_def, fmp_info_join_def,
       fmp_opcode_publishes_fmp_def, pre_fmp_opcode_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem fmp_cover_own_seal[local]:
  fmp_lower_function ctx sp fn = SOME (fn',sp') /\
  fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn ==>
  ?sig. fn'.fn_fmp_signature = SOME sig /\ ~sig.fms_publishes
Proof
  strip_tac >>
  `~(fmp_direct_info fn).fi_publishes_fmp` by
    metis_tac[fmp_cover_direct_nonpublish] >>
  gvs[fmp_lower_function_def, AllCaseEqs()] >>
  `MEM fn ctx.ctx_functions` by
    (gvs[fmp_lower_function_with_info_def, fmp_lower_input_def, AllCaseEqs()] >>
     metis_tac[lookup_function_MEM]) >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  drule_all analyze_fmp_context_unsealed_publishes_iff >> strip_tac >>
  gvs[fmp_checked_seal_def, fmp_seal_def, AllCaseEqs()]
QED

Theorem fmp_cover_later_signature[local]:
  fn_steps rpolicy (DROP 4 o1_fn_passes) fn fn' ==>
  fn'.fn_fmp_signature = fn.fn_fmp_signature
Proof
  simp[o1_fn_passes_def, fn_steps_def] >> rpt strip_tac >>
  imp_res_tac fmp_cover_step_signature >> gvs[fn_pass_tag_def]
QED

Theorem fmp_cover_output_nonpublish[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  lookup_function nm C'.ctx_functions = SOME fn' ==>
  ?sig. fn'.fn_fmp_signature = SOME sig /\ ~sig.fms_publishes
Proof
  strip_tac >>
  `MEM fn' C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `LIST_REL (\fn fn'. ?observed sp out.
      fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed sp fn out /\
      out.fpo_function = fn') C.ctx_functions C'.ctx_functions` by
    (gvs[fmp_stage_ctx_def, ctx_pass_stage_def] >>
     irule listTheory.LIST_REL_mono >> first_assum (irule_at Any) >> metis_tac[]) >>
  drule_all listTheory.LIST_REL_MEM_IMP_R >> strip_tac >>
  rename1 `MEM src C.ctx_functions` >>
  `src.fn_fmp_signature = NONE /\ pre_fmp_ops src` by
    (gvs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def,
         fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  gvs[] >> drule fmp_fn_pass_step_result >> strip_tac >>
  metis_tac[fmp_cover_own_seal]
QED

Theorem fmp_cover_actual_nonpublish:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' ==>
  ?infos ctx runner.
    fmp_stage_lowered infos ctx runner fn fn' /\
    (!i callee info args. MEM i (fn_insts fn) /\
       fmp_resolve_invoke infos ctx i = SOME (callee,info,args) ==>
       ~info.fi_publishes_fmp)
Proof
  strip_tac >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[fmp_stage_ctx_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
      (o1_walk_view rpolicy 3) C C'` by gvs[fmp_stage_ctx_def] >>
  drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  `ir_supply_covers_fn s fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >>
     gvs[fn_pass_step_def] >>
     metis_tac[lookup_unique_function_member]) >>
  gvs[fmp_lower_function_def, AllCaseEqs()] >>
  qexistsl [`infos`, `observed.cu_context`, `FST (fresh_ir_var s)`] >>
  conj_tac >- (simp[fmp_stage_lowered_def] >> metis_tac[]) >>
  rpt strip_tac >> drule fmp_resolve_invoke_some >> strip_tac >>
  `i.inst_opcode = INVOKE` by
    (gvs[fmp_resolve_invoke_def, AllCaseEqs()] >> metis_tac[]) >>
  `MEM name (fn_invoke_targets fn)` by
    (simp[fn_invoke_targets_def, fcgDefsTheory.fcg_scan_function_def,
          mem_get_invoke_targets] >> metis_tac[]) >>
  `MEM name (ctx_fn_names C)` by
    metis_tac[lookup_function_mem, ctx_fn_names_def] >>
  `?src. lookup_function name C.ctx_functions = SOME src` by
    (Cases_on `lookup_function name C.ctx_functions` >>
     gvs[ctx_fn_names_def] >> metis_tac[lookup_function_not_mem]) >>
  drule_all ctx_pass_stage_lookup >> strip_tac >>
  `fn_steps rpolicy (DROP 4 o1_fn_passes) fn' callee` by
    (qpat_x_assum `o1_walk_view rpolicy 3 C' fn observed`
       (assume_tac o REWRITE_RULE [o1_walk_view_def]) >>
     drule_all walk_view_fn_steps >> strip_tac >> gvs[]) >>
  drule fmp_cover_later_signature >> strip_tac >>
  drule_all fmp_cover_output_nonpublish >> strip_tac >>
  gvs[fmp_info_of_signature_def]
QED
