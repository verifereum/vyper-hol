Theory ctorDeployLoweringFramePipeline
Ancestors venomPipelineDriver

Theorem successful_pipeline_output_checks:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out ==>
  unit_wf out.po_unit /\
  unit_labels_wf out.po_unit /\
  context_target_safe rpolicy.rpol_target out.po_unit.cu_context /\
  concretized_static_layouts_wf out.po_unit.cu_context /\
  fmp_lowered_context_wf out.po_unit.cu_context /\
  mem_ok out.po_unit.cu_context /\
  calling_ok out.po_unit.cu_context /\
  post_ok out.po_unit.cu_context /\
  reachable_fcg_acyclic out.po_unit.cu_context (fcg_analyze out.po_unit.cu_context) /\
  codegen_ready out.po_unit.cu_context
Proof
  simp[run_venom_pipeline_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem successful_pipeline_preserves:
  P unit /\
  (!u s v t. P u /\
     run_pipeline_stages rpolicy spec.ps_pre_walk_stages u s = SOME (v,t)
     ==> P v) /\
  (!u. P u ==> P (prune_unit_fcg_unreachable u (fcg_analyze u.cu_context))) /\
  (!names u s v t. P u /\
     run_callee_first rpolicy spec.ps_fn_passes names u s = SOME (v,t)
     ==> P v) /\
  (!u s v t. P u /\
     run_pipeline_stages rpolicy spec.ps_post_walk_stages u s = SOME (v,t)
     ==> P v) /\
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out
  ==> P out.po_unit
Proof
  simp[run_venom_pipeline_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `P pre_unit` by metis_tac[] >>
  Cases_on `spec.ps_prune_unreachable` >> gvs[] >>
  `P walked_unit` by metis_tac[] >>
  metis_tac[]
QED
