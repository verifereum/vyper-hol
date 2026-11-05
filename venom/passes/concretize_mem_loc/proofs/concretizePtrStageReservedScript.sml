Theory concretizePtrStageReserved
Ancestors concretizePtrStageBounds concretizePtrLayoutOutput
  concretizePtrImportOrigins staticLayoutCompletionProofs staticLayoutAllocatorProofs
  concretizeMemLocDefs staticLayoutDefs o1PassContract venomPassDispatcher
  o1ScheduleDecomp o1ScheduleDecompHelpers venomWf fcgDefs
  ptrDiscipline concretizePtrStagePlacements venomInst ctxLookupAgreeHelpers
  list finite_map pair arithmetic

Theorem ptr_concretize_mems_reserved_or_import:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  MEM (a,p,sz) fn'.fn_mems_used ==>
  (0 < sz ==> EVERY (reserved_intervals_disjoint (p,sz)) reserved) \/
  MEM (a,p,sz) (imported_mems_used ctx fn)
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[apply_context_concretize_layout_def, apply_concretize_layout_def] >>
  drule ptr_unique_mems_subset >>
  simp[MEM_MAP, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  TRY disj1_tac >> PairCases_on `y` >>
  Cases_on `static_alloca_items fn` >> gvs[] >>
  gvs[compute_function_layout_fuel_in_context_def,
      compute_function_layout_eval_def, AllCaseEqs()] >>
  drule ptr_mk_layout_positions >> strip_tac >>
  FIRST [drule_all complete_alloc_positions_with_imports_success,
         drule complete_alloc_positions_success] >> strip_tac >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(a,sz)` mp_tac) >> simp[] >> strip_tac >>
  `?q. FLOOKUP completed a = SOME q` by metis_tac[] >>
  `?other recovered. MEM other (fn_insts fn) /\
    exact_static_alloca other = SOME (a,recovered) /\
    (0 < recovered ==> EVERY (reserved_intervals_disjoint (q,recovered)) reserved)` by
    metis_tac[] >>
  `recovered = sz` by metis_tac[static_alloca_items_exact_key_size_unique] >>
  gvs[]
QED

Theorem ptr_step_mems_reserved_or_import:
  fn.fn_eom = NONE /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  MEM (a,p,sz) out.fpo_function.fn_mems_used ==>
  (0 < sz ==> EVERY (reserved_intervals_disjoint (p,sz))
    observed.cu_context.ctx_global_reserved) \/
  MEM (a,p,sz) (imported_mems_used observed.cu_context fn)
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all ptr_concretize_mems_reserved_or_import >> simp[]
QED

Theorem ptr_stage_indexed_mems_reserved[local]:
  !n name g a p sz.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  list_index name names = SOME n /\
  lookup_function name C'.ctx_functions = SOME g /\
  MEM (a,p,sz) g.fn_mems_used /\ 0 < sz ==>
  EVERY (reserved_intervals_disjoint (p,sz)) C.ctx_global_reserved
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `MEM g C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `?fn observed s out. MEM fn C.ctx_functions /\
    fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
    out.fpo_function = g /\
    observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
    ctx_fn_names observed.cu_context = ctx_fn_names C /\
    o1_walk_view rpolicy 2 C' fn observed` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >>
     simp[ctx_pass_stage_def] >> strip_tac >>
     drule_all LIST_REL_MEM_IMP_R >> strip_tac >> metis_tac[]) >>
  `fn.fn_name = name` by
    (gvs[fn_pass_step_def] >> metis_tac[lookup_function_selected_name]) >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `out.fpo_function = g` (SUBST_ALL_TAC o SYM) >>
  drule_all ptr_step_mems_reserved_or_import >> strip_tac
  >- gvs[] >>
  drule_all ptr_stage_import_lookup >> strip_tac >>
  rename1 `lookup_function callee C'.ctx_functions = SOME g'` >>
  `list_precedes callee name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  gvs[list_precedes_iff] >>
  qpat_x_assum `!m. m < n ==> _` (qspec_then `i` mp_tac) >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem ptr_stage_mems_reserved:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\
  MEM g C'.ctx_functions /\ MEM (a,p,sz) g.fn_mems_used /\ 0 < sz ==>
  EVERY (reserved_intervals_disjoint (p,sz)) C.ctx_global_reserved
Proof
  strip_tac >>
  `?fn observed s out. MEM fn C.ctx_functions /\
    fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
    out.fpo_function = g /\
    observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
    ctx_fn_names observed.cu_context = ctx_fn_names C /\
    o1_walk_view rpolicy 2 C' fn observed` by
    (qpat_x_assum `ctx_pass_stage _ _ _ _ _` mp_tac >>
     simp[ctx_pass_stage_def] >> strip_tac >>
     drule_all LIST_REL_MEM_IMP_R >> strip_tac >> metis_tac[]) >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `out.fpo_function = g` (SUBST_ALL_TAC o SYM) >>
  drule_all ptr_step_mems_reserved_or_import >> strip_tac
  >- gvs[] >>
  drule_all ptr_stage_import_lookup >> strip_tac >>
  `list_precedes name fn.fn_name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  fs[list_precedes_iff] >>
  drule_all ptr_stage_indexed_mems_reserved >> simp[]
QED

Theorem ptr_stage_placements_reserved_prefix:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\ fixed_region_reserved lo C /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (p,sz) /\ k < sz ==>
  lo <= p + k
Proof
  strip_tac >>
  `0 < sz` by decide_tac >>
  `EVERY (reserved_intervals_disjoint (p,sz)) C.ctx_global_reserved` by
    (gvs[ptr_stage_placements_def] >>
     `0 < sz` by decide_tac >>
     drule_all ptr_stage_mems_reserved >> simp[]) >>
  spose_not_then assume_tac >>
  `p + k < lo` by decide_tac >>
  qpat_x_assum `fixed_region_reserved lo C` mp_tac >>
  rewrite_tac[fixed_region_reserved_def] >>
  disch_then (qspec_then `p + k` mp_tac) >>
  impl_tac >- decide_tac >> strip_tac >>
  qpat_x_assum `EVERY (reserved_intervals_disjoint _) _` mp_tac >>
  pure_rewrite_tac[EVERY_MEM] >> disch_then drule >>
  simp[reserved_intervals_disjoint_def] >> decide_tac
QED
