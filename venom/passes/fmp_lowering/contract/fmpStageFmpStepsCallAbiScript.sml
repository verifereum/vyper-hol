(* Convention transport for the INVOKE call boundary. *)
Theory fmpStageFmpStepsCallAbi
Ancestors
  fmpStageOpBaseActual concretizeStageLookup fmpStepBridge
  fmpLowerProps fmpLowerDefs irSupply fmpStageRel o1PassContract venomPassDispatcher
  venomPassSchedule venomInst venomFnScheduleRunnerProps list

Theorem fmp_call_step_signature:
  fn_pass_step rpolicy pass observed s fn out /\
  fn_pass_tag pass <> VP_FmpLowering ==>
  out.fpo_function.fn_fmp_signature = fn.fn_fmp_signature
Proof
  rw[fn_pass_step_def, fn_pass_effects_hold_def, fn_abi_effect_holds_def,
     fn_fmp_convention_eq_def] >>
  Cases_on `fn_pass_tag pass` >> gvs[fn_pass_abi_effect_def]
QED

Theorem fmp_call_steps_signature:
  !passes fn fn'.
  EVERY (\p. fn_pass_tag p <> VP_FmpLowering) passes /\
  fn_steps rpolicy passes fn fn' ==>
  fn'.fn_fmp_signature = fn.fn_fmp_signature
Proof
  Induct >> simp[fn_steps_def] >> rpt strip_tac >>
  drule_all fmp_call_step_signature >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem fmp_call_later_signature:
  fn_steps rpolicy (DROP 4 o1_fn_passes) fn fn' ==>
  fn'.fn_fmp_signature = fn.fn_fmp_signature
Proof
  strip_tac >> irule fmp_call_steps_signature >>
  qexistsl [`DROP 4 o1_fn_passes`, `rpolicy`] >>
  simp[o1_fn_passes_def, fn_pass_tag_def]
QED

Theorem fmp_call_walk_signature:
  o1_walk_view rpolicy 3 C' fn observed /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name C'.ctx_functions = SOME callee' ==>
  ?callee. lookup_function name observed.cu_context.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = callee'.fn_fmp_signature
Proof
  simp[o1_walk_view_def] >> rpt strip_tac >>
  drule_all walk_view_fn_steps >> strip_tac >>
  drule fmp_call_later_signature >> strip_tac >> metis_tac[]
QED

Theorem fmp_call_actual_witness:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  lookup_function name C.ctx_functions = SOME fn ==>
  ?fn' observed sp out infos.
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed sp fn out /\
    out.fpo_function = fn' /\
    analyze_fmp_context observed.cu_context = SOME infos /\
    fmp_lower_function_with_info infos observed.cu_context sp fn =
      SOME (fn',out.fpo_supply) /\
    fmp_stage_lowered infos observed.cu_context (FST (fresh_ir_var sp)) fn fn' /\
    observed.cu_context.ctx_entry = C.ctx_entry /\
    o1_walk_view rpolicy 3 C' fn observed
Proof
  strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
     (o1_walk_view rpolicy 3) C C'` by gvs[fmp_stage_ctx_def] >>
  drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >>
  drule fmp_fn_pass_step_result >> strip_tac >>
  `ir_supply_covers_fn s fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >>
     gvs[fn_pass_step_def] >>
     metis_tac[lookup_unique_function_member]) >>
  gvs[fmp_lower_function_def, AllCaseEqs()] >>
  qexistsl [`observed`, `s`, `out`, `infos`] >>
  simp[fmp_stage_lowered_def] >> metis_tac[]
QED

Theorem fmp_call_lowered_signature_root:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\ ~fn_is_context_entry ctx fn ==>
  ?sig. fn'.fn_fmp_signature = SOME sig /\
    (sig.fms_has_fmp_param <=> IS_SOME (fmp_stage_root infos ctx fn))
Proof
  simp[fmp_stage_lowered_def] >> rpt strip_tac >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _`
    (strip_assume_tac o SRULE [fmp_lower_function_with_info_def, AllCaseEqs()]) >>
  gvs[] >> drule fmp_checked_seal_some >> strip_tac >>
  gvs[fmp_seal_def, fmp_stage_root_def] >>
  Cases_on `root_layout` >> gvs[fmp_make_root_layout_def, AllCaseEqs()] >>
  Cases_on `fn.fn_blocks` >> gvs[split_fmp_entry_def]
QED
