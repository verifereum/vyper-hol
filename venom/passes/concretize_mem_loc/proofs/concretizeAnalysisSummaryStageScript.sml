Theory concretizeAnalysisSummaryStage
Ancestors
  concretizeAnalysisSummaryCoverage concretizeAnalysisMetadataOwnership
  concretizeAnalysisMetadataSchedule concretizeAnalysisOwnership o1ScheduleDecompHelpers
  o1PassContract venomWf venomInst concretizeMemLocDefs list relation pair

Theorem concretize_stage_own_key_coverage:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_function name C'.ctx_functions = SOME out /\
  static_alloca_items fn = SOME items /\ MEM (a,sz) items ==>
  ?p sz'. MEM (a,p,sz') out.fn_mems_used
Proof
  strip_tac >> drule_all concretize_stage_lookup >> strip_tac >> gvs[] >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `lookup_function name C.ctx_functions = SOME fn`
       (mp_tac o MATCH_MP venomInstTheory.lookup_function_MEM) >>
     gvs[EVERY_MEM]) >>
  drule_all concretize_context_rebuilds_metadata >> strip_tac >> gvs[] >>
  metis_tac[context_layout_own_key_coverage]
QED

Theorem concretize_observed_key_coverage:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  source_call C caller callee /\
  lookup_function callee.fn_name C'.ctx_functions = SOME callee_out /\
  MEM (a,p,sz) callee_out.fn_mems_used ==>
  ?g. lookup_function callee.fn_name observed.cu_context.ctx_functions = SOME g /\
      MEM (a,p,sz) g.fn_mems_used
Proof
  strip_tac >> gvs[o1_walk_view_def, source_call_def] >>
  drule_all concretize_walk_view_mems_used >> strip_tac >> metis_tac[]
QED

Theorem concretize_stage_call_key_coverage:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  source_call C caller callee /\
  lookup_function caller.fn_name C'.ctx_functions = SOME caller_out /\
  lookup_function callee.fn_name C'.ctx_functions = SOME callee_out /\
  MEM (a,p,sz) callee_out.fn_mems_used ==>
  ?p' sz'. MEM (a,p',sz') caller_out.fn_mems_used
Proof
  strip_tac >>
  `lookup_function caller.fn_name C.ctx_functions = SOME caller` by
    (irule (iffRL lookup_function_member_iff) >>
     gvs[source_call_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  drule_all concretize_stage_lookup >> strip_tac >> gvs[] >>
  `caller.fn_eom = NONE` by gvs[source_call_def, EVERY_MEM] >>
  drule_all concretize_context_rebuilds_metadata >> strip_tac >> gvs[] >>
  `MEM callee.fn_name (fn_invoke_targets caller)` by gvs[source_call_def] >>
  drule_all concretize_walk_view_mems_used >> strip_tac >>
  `?inst args. MEM inst (fn_insts caller) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label callee.fn_name :: args` by
      metis_tac[invoke_target_instruction] >>
  `MEM (a,p,sz) (callee_mems_used observed.cu_context callee.fn_name)` by
    simp[callee_mems_used_def] >>
  drule_all invoke_import_key_coverage >> strip_tac >>
  metis_tac[context_layout_import_key_coverage]
QED

Theorem concretize_stage_path_key_coverage:
  !root owner. RTC (source_call C) root owner ==>
  !out owner_out a p sz.
    ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
      (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
    EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
    lookup_function root.fn_name C'.ctx_functions = SOME out /\
    lookup_function owner.fn_name C'.ctx_functions = SOME owner_out /\
    MEM (a,p,sz) owner_out.fn_mems_used ==>
    ?p' sz'. MEM (a,p',sz') out.fn_mems_used
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- (gvs[] >> metis_tac[]) >>
  rename1 `source_call C root mid` >>
  `lookup_function mid.fn_name C.ctx_functions = SOME mid` by
    (irule (iffRL lookup_function_member_iff) >>
     gvs[source_call_def, o1_ctx_shape_def, ctx_wf_def,
         ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  drule_all concretize_stage_lookup >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all concretize_stage_call_key_coverage >> metis_tac[]
QED

Theorem concretize_stage_descendant_item_coverage:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  MEM root C.ctx_functions /\ MEM owner C.ctx_functions /\
  RTC (source_call C) root owner /\
  static_alloca_items owner = SOME items /\ MEM (a,sz) items /\
  lookup_function root.fn_name C'.ctx_functions = SOME out ==>
  ?p. MEM (a,p,sz) out.fn_mems_used
Proof
  strip_tac >>
  `lookup_function owner.fn_name C.ctx_functions = SOME owner /\
   lookup_function root.fn_name C.ctx_functions = SOME root` by
    (conj_tac >> irule (iffRL lookup_function_member_iff) >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def,
         ctx_fn_names_def]) >>
  qpat_assum `lookup_function owner.fn_name C.ctx_functions = SOME owner`
    (mp_then Any mp_tac concretize_stage_lookup) >>
  disch_then (qspecl_then [`rpolicy`, `C'`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all concretize_stage_own_key_coverage >> strip_tac >>
  drule_all concretize_stage_path_key_coverage >> strip_tac >>
  `source_owns C owner a sz` by
    (drule_all static_alloca_items_source_owns >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  `EVERY (\(a,p,s). source_owns C root a s) out.fn_mems_used` by
    metis_tac[concretize_stage_source_owns] >>
  gvs[EVERY_MEM, FORALL_PROD] >>
  metis_tac[source_owns_size_unique]
QED

Theorem concretize_observed_descendant_item_coverage:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  source_call C caller root /\ MEM owner C.ctx_functions /\
  RTC (source_call C) root owner /\
  static_alloca_items owner = SOME items /\ MEM (a,sz) items /\
  o1_walk_view rpolicy 2 C' caller observed ==>
  ?g p. lookup_function root.fn_name observed.cu_context.ctx_functions = SOME g /\
        MEM (a,p,sz) g.fn_mems_used
Proof
  strip_tac >>
  `MEM root C.ctx_functions /\ MEM caller C.ctx_functions` by
    gvs[source_call_def] >>
  `lookup_function root.fn_name C.ctx_functions = SOME root` by
    (irule (iffRL lookup_function_member_iff) >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def,
         ctx_fn_names_def]) >>
  drule_all concretize_stage_lookup >> strip_tac >>
  drule_all concretize_stage_descendant_item_coverage >> strip_tac >>
  drule_all concretize_observed_key_coverage >> metis_tac[]
QED
