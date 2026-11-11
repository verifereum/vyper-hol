Theory concretizeLayoutMetadataSchedule
Ancestors concretizeAnalysisSummaryCoverage concretizeAnalysisMetadata concretizeLayoutMetadata concretizeAnalysisMetadataOwnership
  concretizeAnalysisMetadataSchedule concretizeAnalysisOwnership
  staticLayoutAllocatorProofs concretizeStageLookup o1PassContract
  o1ScheduleDecomp concretizeMemLocDefs venomWf venomInst list pair
  ctxLookupAgreeHelpers fcgDefs o1ScheduleDecompHelpers

Definition canonical_metadata_def:
  canonical_metadata C C' a p s <=>
    ?owner items out.
      MEM owner C.ctx_functions /\
      static_alloca_items owner = SOME items /\ MEM (a,s) items /\
      lookup_function owner.fn_name C'.ctx_functions = SOME out /\
      FIND (\(b,q,t). b = a) out.fn_mems_used = SOME (a,p,s)
End

Theorem canonical_metadata_unique:
  ctx_inst_ids_distinct C /\
  canonical_metadata C C' a p s /\ canonical_metadata C C' a q t ==>
  p = q /\ s = t
Proof
  rw[canonical_metadata_def] >>
  `?i. MEM i (fn_insts owner) /\ exact_static_alloca i = SOME (a,s)` by
    metis_tac[static_alloca_items_MEM] >>
  `?j. MEM j (fn_insts owner') /\ exact_static_alloca j = SOME (a,t)` by
    metis_tac[static_alloca_items_MEM] >>
  gvs[exact_static_alloca_def, exact_static_alloca_size_def, AllCaseEqs()] >>
  `owner = owner'` by metis_tac[source_instruction_owner_unique] >> gvs[]
QED

Theorem concretize_context_canonical_metadata:
  MEM fn C.ctx_functions /\ fn.fn_eom = NONE /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out /\
  concretize_function_fuel_in_context fuel observed reserved fn = SOME out /\
  (!inst name args g.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label name :: args /\
    lookup_function name observed.ctx_functions = SOME g ==>
    EVERY (\(a,p,s). canonical_metadata C C' a p s) g.fn_mems_used) ==>
  EVERY (\(a,p,s). canonical_metadata C C' a p s) out.fn_mems_used
Proof
  strip_tac >>
  `EVERY (\(a,p,s). canonical_metadata C C' a p s)
     (imported_mems_used observed fn)` by
    (irule imported_mems_used_every >> metis_tac[]) >>
  drule_all concretize_context_rebuilds_metadata >> strip_tac >>
  Cases_on `static_alloca_items fn`
  >- (gvs[] >> simp[apply_context_concretize_layout_def] >>
      irule unique_mems_used_every >> simp[]) >>
  rename1 `static_alloca_items fn = SOME items` >>
  `ALL_DISTINCT (MAP FST items)` by metis_tac[static_alloca_items_ALL_DISTINCT] >>
  gvs[] >> irule apply_context_layout_mems_every >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  simp[canonical_metadata_def] >>
  qexistsl_tac [`fn`, `items`, `apply_context_concretize_layout observed layout fn`] >>
  simp[] >> irule context_layout_own_find >> simp[]
QED

Theorem concretize_stage_canonical_bounded[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions ==>
  !n name fn out.
    (!i. list_index fn.fn_name names = SOME i ==> i < n) /\
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME out ==>
    EVERY (\(a,p,s). canonical_metadata C C' a p s) out.fn_mems_used
Proof
  strip_tac >> completeInduct_on `n` >> rpt strip_tac >>
  drule_all concretize_stage_lookup >> strip_tac >> gvs[] >>
  irule concretize_context_canonical_metadata >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  qexistsl_tac [`fn`, `concretize_memloc_fuel fn`, `observed.cu_context`,
                `observed.cu_context.ctx_global_reserved`] >>
  simp[] >> reverse conj_tac >- gvs[EVERY_MEM] >>
  rpt strip_tac >>
  `MEM name' (fn_invoke_targets fn)` by metis_tac[invoke_target_instruction] >>
  drule_all source_invoke_lookup >> strip_tac >>
  drule_all source_call_precedes >> simp[list_precedes_iff] >> strip_tac >>
  drule_all concretize_stage_lookup >> strip_tac >>
  `j < n` by metis_tac[] >>
  `EVERY (\(a,p,s). canonical_metadata C C' a p s) out'.fn_mems_used` by
    (qpat_x_assum `!m. m < n ==> _` (qspec_then `j` mp_tac) >>
     simp[] >> disch_then irule >>
     qexistsl_tac [`callee`, `name'`] >> simp[]) >>
  drule_all concretize_walk_view_mems_used >> strip_tac >> gvs[]
QED

Theorem concretize_stage_canonical_metadata:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_function name C'.ctx_functions = SOME out ==>
  EVERY (\(a,p,s). canonical_metadata C C' a p s) out.fn_mems_used
Proof
  strip_tac >>
  `?n. !i. list_index fn.fn_name names = SOME i ==> i < n` by
    (Cases_on `list_index fn.fn_name names` >> simp[] >>
     rename1 `list_index fn.fn_name names = SOME i` >>
     qexists_tac `SUC i` >> simp[]) >>
  drule_all concretize_stage_canonical_bounded >> metis_tac[]
QED

Theorem concretize_observed_canonical_metadata:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  MEM name (fn_invoke_targets caller) /\
  lookup_function name observed.cu_context.ctx_functions = SOME g ==>
  EVERY (\(a,p,s). canonical_metadata C C' a p s) g.fn_mems_used
Proof
  strip_tac >> drule_all source_invoke_lookup >> strip_tac >>
  drule_all concretize_stage_lookup >> strip_tac >>
  `EVERY (\(a,p,s). canonical_metadata C C' a p s) out.fn_mems_used` by
    metis_tac[concretize_stage_canonical_metadata] >>
  gvs[o1_walk_view_def] >>
  drule_all concretize_walk_view_mems_used >> strip_tac >> gvs[]
QED

Theorem concretize_import_canonical_metadata:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed ==>
  EVERY (\(a,p,s). canonical_metadata C C' a p s)
    (imported_mems_used observed.cu_context caller)
Proof
  strip_tac >> irule imported_mems_used_every >> rpt strip_tac >>
  irule concretize_observed_canonical_metadata >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[invoke_target_instruction]
QED

Theorem concretize_stage_member_canonical:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ MEM out C'.ctx_functions ==>
  EVERY (\(a,p,s). canonical_metadata C C' a p s) out.fn_mems_used
Proof
  strip_tac >>
  `MAP (\f. f.fn_name) C'.ctx_functions = MAP (\f. f.fn_name) C.ctx_functions` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >>
     simp[ctx_pass_stage_def] >> strip_tac >>
     gvs[LIST_REL_EL_EQN] >> irule LIST_EQ >> simp[EL_MAP] >>
     rpt strip_tac >>
     qpat_x_assum `!n. n < _ ==> _` (qspec_then `x` mp_tac) >>
     simp[] >> strip_tac >> gvs[fn_pass_step_def]) >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions)` by
    gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  `lookup_function out.fn_name C'.ctx_functions = SOME out` by
    (irule (iffRL lookup_function_member_iff) >> simp[]) >>
  `MEM out.fn_name (MAP (\f. f.fn_name) C.ctx_functions)` by
    (qpat_x_assum `MAP _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  `?fn. lookup_function out.fn_name C.ctx_functions = SOME fn` by
    (Cases_on `lookup_function out.fn_name C.ctx_functions` >> simp[] >>
     metis_tac[lookup_function_not_mem]) >>
  metis_tac[concretize_stage_canonical_metadata]
QED

Theorem concretize_stage_metadata_coherent:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  MEM f C'.ctx_functions /\ MEM g C'.ctx_functions /\
  MEM (a,p,s) f.fn_mems_used /\ MEM (a,q,t) g.fn_mems_used ==>
  p = q /\ s = t
Proof
  strip_tac >>
  `EVERY (\(a,p,s). canonical_metadata C C' a p s) f.fn_mems_used /\
   EVERY (\(a,p,s). canonical_metadata C C' a p s) g.fn_mems_used` by
    (conj_tac >> irule concretize_stage_member_canonical >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[canonical_metadata_unique]
QED

Theorem concretize_observed_import_coherent:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  MEM name (fn_invoke_targets caller) /\
  lookup_function name observed.cu_context.ctx_functions = SOME g /\
  MEM (a,p,s) g.fn_mems_used /\
  MEM (a,q,t) (imported_mems_used observed.cu_context caller) ==>
  p = q /\ s = t
Proof
  strip_tac >>
  drule_all concretize_observed_canonical_metadata >> strip_tac >>
  drule_all concretize_import_canonical_metadata >> strip_tac >>
  gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[canonical_metadata_unique]
QED

Theorem concretize_observed_exact_import:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  MEM inst (fn_insts caller) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label name :: args /\
  lookup_function name observed.cu_context.ctx_functions = SOME g /\
  MEM (a,p,s) g.fn_mems_used ==>
  MEM (a,p,s) (imported_mems_used observed.cu_context caller)
Proof
  strip_tac >>
  `MEM name (fn_invoke_targets caller)` by metis_tac[invoke_target_instruction] >>
  `MEM (a,p,s) (callee_mems_used observed.cu_context name)` by
    simp[callee_mems_used_def] >>
  drule_all invoke_import_key_coverage >> strip_tac >>
  `p = p' /\ s = sz'` by metis_tac[concretize_observed_import_coherent] >>
  gvs[]
QED

Theorem concretize_observed_metadata_coherent:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  MEM name (fn_invoke_targets caller) /\ MEM name' (fn_invoke_targets caller) /\
  lookup_function name observed.cu_context.ctx_functions = SOME f /\
  lookup_function name' observed.cu_context.ctx_functions = SOME g /\
  MEM (a,p,s) f.fn_mems_used /\ MEM (a,q,t) g.fn_mems_used ==>
  p = q /\ s = t
Proof
  strip_tac >>
  `EVERY (\(a,p,s). canonical_metadata C C' a p s) f.fn_mems_used /\
   EVERY (\(a,p,s). canonical_metadata C C' a p s) g.fn_mems_used` by
    (conj_tac >> irule concretize_observed_canonical_metadata >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[canonical_metadata_unique]
QED
