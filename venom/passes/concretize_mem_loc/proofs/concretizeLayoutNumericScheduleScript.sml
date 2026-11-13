Theory concretizeLayoutNumericSchedule
Ancestors concretizeLayoutNumeric concretizeLayoutMetadataSchedule
  concretizeStageLookup o1PassContract o1ScheduleDecompHelpers
  concretizeMemLocDefs venomPassDispatcher venomWf venomInst
  list pair words

Theorem concretize_canonical_numeric:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  canonical_metadata C C' a p s ==>
  p + s < dimword (:256) /\
  (0 < s ==> EVERY (reserved_intervals_disjoint (p,s)) C.ctx_global_reserved)
Proof
  strip_tac >> gvs[canonical_metadata_def] >>
  `lookup_function owner.fn_name C.ctx_functions = SOME owner` by
    (irule (iffRL lookup_function_member_iff) >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  drule_all ctx_pass_stage_lookup >> strip_tac >> gvs[] >>
  qpat_x_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
  simp[fn_pass_step_def, o1_walk_view_def, AllCaseEqs()] >> strip_tac >>
  drule_all concretize_context_local_numeric_find >> strip_tac >> gvs[]
QED

Theorem concretize_stage_metadata_numeric:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ MEM out C'.ctx_functions ==>
  EVERY (\(a,p,s). p + s < dimword (:256) /\
    (0 < s ==> EVERY (reserved_intervals_disjoint (p,s)) C.ctx_global_reserved))
    out.fn_mems_used
Proof
  strip_tac >> drule_all concretize_stage_member_canonical >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all concretize_canonical_numeric >> simp[EVERY_MEM, FORALL_PROD]
QED

Theorem concretize_import_metadata_numeric:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ MEM caller C.ctx_functions /\
  o1_walk_view rpolicy 2 C' caller observed ==>
  EVERY (\(a,p,s). p + s < dimword (:256) /\
    (0 < s ==> EVERY (reserved_intervals_disjoint (p,s)) C.ctx_global_reserved))
    (imported_mems_used observed.cu_context caller)
Proof
  strip_tac >> drule_all concretize_import_canonical_metadata >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all concretize_canonical_numeric >> simp[EVERY_MEM, FORALL_PROD]
QED
