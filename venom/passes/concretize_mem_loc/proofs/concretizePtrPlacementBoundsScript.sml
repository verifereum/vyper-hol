Theory concretizePtrPlacementBounds
Ancestors concretizePtrImportOrigins concretizePtrLayoutOutput
  staticLayoutAllocatorProofs staticLayoutCompletionProofs staticLayoutDefs concretizeMemLocDefs
  concretizePtrStagePlacements o1ScheduleDecompHelpers o1ScheduleDecomp
  ctxLookupAgreeHelpers fcgDefs
  o1PassContract venomPassDispatcher venomInst venomWf list finite_map words pair

Theorem ptr_layout_item_strict[local]:
  static_alloca_items fn = SOME items /\ MEM (a,sz) items /\
  (compute_function_layout_fuel_in_context fuel ctx reserved fn = SOME layout \/
   compute_function_layout_eval reserved fn = SOME layout) ==>
  ?p. FLOOKUP layout.cl_positions a = SOME p /\ p + sz < dimword(:256)
Proof
  strip_tac
  >- (gvs[compute_function_layout_fuel_in_context_def, AllCaseEqs()] >>
      drule_all complete_alloc_positions_with_imports_success >> strip_tac >>
      drule static_alloca_items_MEM >>
      disch_then (qspec_then `(a,sz)` mp_tac) >> simp[] >> strip_tac >>
      drule ptr_mk_layout_positions >> strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[compute_function_layout_eval_def, AllCaseEqs()] >>
  drule complete_alloc_positions_success >> strip_tac >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(a,sz)` mp_tac) >> simp[] >> strip_tac >>
  drule ptr_mk_layout_positions >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ptr_concretize_mems_strict_or_import:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  MEM (a,p,sz) fn'.fn_mems_used ==>
  p + sz < dimword(:256) \/ MEM (a,p,sz) (imported_mems_used ctx fn)
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[apply_context_concretize_layout_def] >>
  drule ptr_unique_mems_subset >>
  simp[MEM_MAP, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  TRY disj1_tac >> PairCases_on `y` >>
  Cases_on `static_alloca_items fn` >> gvs[] >>
  `?q. FLOOKUP layout.cl_positions a = SOME q /\ q + sz < dimword(:256)` by
    (irule ptr_layout_item_strict >> rpt (goal_assum (drule_at Any)) >>
     metis_tac[]) >>
  gvs[]
QED

Theorem ptr_step_mems_strict_or_import:
  fn.fn_eom = NONE /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  MEM (a,p,sz) out.fpo_function.fn_mems_used ==>
  p + sz < dimword(:256) \/
  MEM (a,p,sz) (imported_mems_used observed.cu_context fn)
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  irule ptr_concretize_mems_strict_or_import >> simp[] >>
  qexistsl [`fn'`,`concretize_memloc_fuel fn`,
            `observed.cu_context.ctx_global_reserved`] >> simp[]
QED

Theorem ptr_stage_indexed_mems_strict[local]:
  !n name g a p sz.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  list_index name names = SOME n /\
  lookup_function name C'.ctx_functions = SOME g /\
  MEM (a,p,sz) g.fn_mems_used ==> p + sz < dimword(:256)
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  drule_all ptr_stage_lookup_origin >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `out.fpo_function = g` (SUBST_ALL_TAC o SYM) >>
  drule_all ptr_step_mems_strict_or_import >> strip_tac >>
  drule_all ptr_stage_import_lookup >> strip_tac >>
  rename1 `lookup_function callee C'.ctx_functions = SOME g'` >>
  `list_precedes callee name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  gvs[list_precedes_iff] >>
  qpat_x_assum `!m. m < n ==> _` (qspec_then `i` mp_tac) >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem ptr_stage_mems_strict_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\ MEM g C'.ctx_functions /\
  MEM (a,p,sz) g.fn_mems_used ==> p + sz < dimword(:256)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) C'.ctx_functions)` by
    (drule ptr_stage_names >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
     metis_tac[]) >>
  `lookup_function g.fn_name C'.ctx_functions = SOME g` by
    metis_tac[lookup_function_member_iff] >>
  drule_all ptr_stage_lookup_origin >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn.fn_name = g.fn_name` by metis_tac[lookup_function_selected_name] >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `out.fpo_function = g` (SUBST_ALL_TAC o SYM) >>
  drule_all ptr_step_mems_strict_or_import >> strip_tac >>
  drule_all ptr_stage_import_lookup >> strip_tac >>
  `list_precedes name fn.fn_name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  fs[list_precedes_iff] >>
  drule_all ptr_stage_indexed_mems_strict >> simp[]
QED

Theorem ptr_stage_placements_strict_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (p,sz) ==>
  p + sz < dimword(:256)
Proof
  strip_tac >> gvs[ptr_stage_placements_def] >>
  drule_all ptr_stage_mems_strict_bound >> simp[]
QED

