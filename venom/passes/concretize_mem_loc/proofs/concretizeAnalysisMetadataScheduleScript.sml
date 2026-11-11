Theory concretizeAnalysisMetadataSchedule
Ancestors
  o1PassContract venomPassSchedule venomPassDispatcher venomInst
  concretizeMemLocDefs concretizeSuffixMetadataDirect concretizeSuffixMetadataCFG list

Theorem concretize_observation_suffix:
  DROP 3 o1_fn_passes =
    [CFP_Simple VP_FmpLowering; CFP_Simple VP_MakeSSA;
     CFP_Simple VP_SimplifyCFG; CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
Proof
  simp[o1_fn_passes_def]
QED

Theorem fn_steps_name:
  !passes fn fn'. fn_steps rpolicy passes fn fn' ==> fn'.fn_name = fn.fn_name
Proof
  Induct >> simp[fn_steps_def] >> rpt strip_tac >>
  gvs[fn_pass_step_def] >> metis_tac[]
QED

Theorem concretize_context_rebuilds_metadata:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME out ==>
  ?layout. out = apply_context_concretize_layout ctx layout fn
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

(* Conditional transport states exactly what the suffix theorem must supply.
   It does not infer summary equality from the name-only runner checks. *)
Theorem walk_view_mems_used:
  walk_view rpolicy later C' fn observed /\
  (!g h. fn_steps rpolicy later g h ==> h.fn_mems_used = g.fn_mems_used) /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name C'.ctx_functions = SOME g' ==>
  ?g. lookup_function name observed.cu_context.ctx_functions = SOME g /\
      g.fn_name = g'.fn_name /\ g.fn_mems_used = g'.fn_mems_used
Proof
  rw[walk_view_def] >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `g` >> metis_tac[fn_steps_name]
QED

(* Summary equality is established from executable field-preservation facts
   below, not from fn_static_layout_eq (which checks only fn_eom). These
   interfaces transport summaries; they do not assert source ownership. *)

Theorem fn_steps_projection:
  !passes fn fn'.
    EVERY (\pass. !observed s f out.
      fn_pass_step rpolicy pass observed s f out ==>
      proj out.fpo_function = proj f) passes /\
    fn_steps rpolicy passes fn fn' ==> proj fn' = proj fn
Proof
  Induct >> simp[fn_steps_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem concretize_suffix_step_mems_used[local]:
  MEM pass (DROP 3 o1_fn_passes) /\
  fn_pass_step rpolicy pass observed s fn out ==>
  out.fpo_function.fn_mems_used = fn.fn_mems_used
Proof
  simp[concretize_observation_suffix] >> strip_tac >>
  gvs[fn_pass_step_def, AllCaseEqs(), dft_fn_mems_used] >>
  metis_tac[fmp_lower_function_mems_used, make_ssa_current_fn_mems_used,
    simplify_cfg_fn_with_labels_mems_used, sue_expand_function_supply_mems_used,
    cfg_norm_function_supply_mems_used]
QED

Theorem concretize_suffix_mems_used:
  fn_steps rpolicy (DROP 3 o1_fn_passes) fn fn' ==>
  fn'.fn_mems_used = fn.fn_mems_used
Proof
  strip_tac >> irule fn_steps_projection >>
  goal_assum (drule_at Any) >>
  simp[EVERY_MEM] >> metis_tac[concretize_suffix_step_mems_used]
QED

Theorem concretize_walk_view_mems_used:
  walk_view rpolicy (DROP 3 o1_fn_passes) C' fn observed /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name C'.ctx_functions = SOME g' ==>
  ?g. lookup_function name observed.cu_context.ctx_functions = SOME g /\
      g.fn_name = g'.fn_name /\ g.fn_mems_used = g'.fn_mems_used
Proof
  metis_tac[walk_view_mems_used, concretize_suffix_mems_used]
QED
