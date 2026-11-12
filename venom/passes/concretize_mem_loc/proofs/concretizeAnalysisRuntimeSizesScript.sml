Theory concretizeAnalysisRuntimeSizes
Ancestors
  concretizeAnalysisImportSizes concretizeAnalysisStageSizes
  concretizeAnalysisSizes concretizeAnalysisOwnership frameExecutionHistory frameHistoryCfg
  o1PassContract venomWf venomInst list finite_map pred_set

Theorem concretize_runtime_context_size:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  o1_walk_view rpolicy 2 C' fn observed /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  context_alloca_size fn (imported_mems_used observed.cu_context fn)
    (Allocation aid) = sz
Proof
  strip_tac >>
  `EVERY (\f. fn_inst_wf f /\ fn_inst_ids_distinct f) C.ctx_functions` by
    (gvs[EVERY_MEM, o1_ctx_shape_def] >> rpt strip_tac >>
     metis_tac[o1_fn_shape_def, source_member_ids_distinct]) >>
  `EVERY wf_function C.ctx_functions` by
    (gvs[EVERY_MEM, o1_ctx_shape_def] >> metis_tac[o1_fn_shape_def]) >>
  `MEM fn C.ctx_functions` by
    (drule frame_reachable_has_history >> strip_tac >>
     drule_all frame_history_cfg_invariant >> simp[]) >>
  drule_all o1_frame_source_sizes_lookup >>
  simp[source_alloca_sizes_def, FLOOKUP_FUN_FMAP] >> strip_tac >>
  gvs[IN_IMAGE] >>
  drule_all concretize_local_context_size >> simp[]
QED

Theorem concretize_runtime_context_size_option:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_run_state_ok vs0 /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  o1_walk_view rpolicy 2 C' fn observed /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  (if context_alloca_size fn (imported_mems_used observed.cu_context fn)
        (Allocation aid) = 0 then NONE
   else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn)
        (Allocation aid))) = (if sz = 0 then NONE else SOME sz)
Proof
  strip_tac >> drule_all concretize_runtime_context_size >> simp[]
QED
