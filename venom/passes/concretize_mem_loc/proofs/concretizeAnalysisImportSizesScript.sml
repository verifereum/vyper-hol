Theory concretizeAnalysisImportSizes
Ancestors
  concretizeAnalysisMetadataOwnership concretizeAnalysisOwnership
  concretizeAnalysisMetadata concretizeAnalysisSizes concretizeMemLocDefs
  o1PassContract list pair

Theorem concretize_imports_source_owns:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ MEM caller C.ctx_functions /\
  o1_walk_view rpolicy 2 C' caller observed ==>
  EVERY (\(a,p,s). source_owns C caller a s)
    (imported_mems_used observed.cu_context caller)
Proof
  strip_tac >> irule imported_mems_used_every >> rpt strip_tac >>
  `MEM name (fn_invoke_targets caller)` by metis_tac[invoke_target_instruction] >>
  drule_all concretize_observed_source_owns >> strip_tac >>
  gvs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  irule source_owns_prepend_call >> metis_tac[]
QED

Theorem concretize_imports_exclude_local:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  MEM local_inst (fn_insts caller) ==>
  ~EXISTS (\(a,p,s). a = Allocation local_inst.inst_id)
    (imported_mems_used observed.cu_context caller)
Proof
  strip_tac >> irule imported_mems_used_excludes >> rpt strip_tac >>
  `MEM name (fn_invoke_targets caller)` by metis_tac[invoke_target_instruction] >>
  drule_all concretize_observed_source_owns >> strip_tac >>
  qpat_x_assum `MEM inst (fn_insts caller)` kall_tac >>
  drule_all source_owns_summary_excludes >>
  gvs[EVERY_MEM, EXISTS_MEM, FORALL_PROD] >>
  qexists_tac `e` >> PairCases_on `e` >> gvs[]
QED

Theorem source_owns_context_size:
  ctx_inst_ids_distinct C /\
  EVERY (\(a,p,s). source_owns C root a s) imports /\
  MEM (aid,pos,sz) imports ==>
  context_alloca_size fn imports aid = sz
Proof
  strip_tac >> irule context_import_size_valid >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `\a. SOME (@s. source_owns C root a s)` >>
  gvs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  irule SELECT_UNIQUE >> metis_tac[source_owns_size_unique]
QED

Theorem concretize_imports_context_size:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  MEM (aid,pos,sz) (imported_mems_used observed.cu_context caller) ==>
  context_alloca_size caller (imported_mems_used observed.cu_context caller) aid = sz
Proof
  metis_tac[concretize_imports_source_owns, source_owns_context_size]
QED

Theorem concretize_local_context_size:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  MEM inst (fn_insts caller) ==>
  context_alloca_size caller (imported_mems_used observed.cu_context caller)
    (Allocation inst.inst_id) = get_alloca_size caller (Allocation inst.inst_id)
Proof
  metis_tac[concretize_imports_exclude_local, context_alloca_size_local]
QED
