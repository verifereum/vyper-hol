Theory concretizePtrStageBounds
Ancestors stackPlanGen concretizePtrPlacementBounds concretizePtrLayoutOutput
  staticLayoutDefs staticLayoutFoldProofs staticLayoutAllocatorProofs
  concretizeMemLocDefs concretizePtrImportOrigins o1ScheduleDecompHelpers
  o1ScheduleDecomp ctxLookupAgreeHelpers fcgDefs venomPassDispatcher venomWf
  o1PassContract ptrDiscipline venomInst list arithmetic option finite_map words pair

Theorem ptr_collect_fn_eoms_member[local]:
  !fns es fn. collect_fn_eoms fns = SOME es /\ MEM fn fns ==>
    ?n. fn.fn_eom = SOME n /\ MEM n es
Proof
  Induct >> simp[collect_fn_eoms_def] >>
  rpt gen_tac >> simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem ptr_fold_max_bounds[local]:
  !xs acc. acc <= FOLDL MAX acc xs /\
    (!n. MEM n xs ==> n <= FOLDL MAX acc xs)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then `MAX acc h` strip_assume_tac) >>
  `acc <= MAX acc h /\ h <= MAX acc h` by simp[MAX_DEF] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem ptr_max_live_global_bound:
  max_live_eom C = SOME eom ==>
  ?global_end. global_reserved_end C.ctx_global_reserved 0 = SOME global_end /\
    global_end <= eom
Proof
  simp[max_live_eom_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[ptr_fold_max_bounds]
QED

Theorem ptr_max_live_function_bound:
  max_live_eom C = SOME eom /\ MEM fn C.ctx_functions ==>
  ?n. fn.fn_eom = SOME n /\ n <= eom
Proof
  simp[max_live_eom_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all ptr_collect_fn_eoms_member >> strip_tac >>
  metis_tac[ptr_fold_max_bounds]
QED

Theorem ptr_stage_fixed_region_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  fixed_region_reserved lo C /\ max_live_eom C' = SOME eom ==>
  lo <= eom
Proof
  strip_tac >> drule ptr_max_live_global_bound >> strip_tac >>
  drule global_reserved_end_success >> strip_tac >>
  `C'.ctx_global_reserved = C.ctx_global_reserved` by fs[ctx_pass_stage_def] >>
  Cases_on `lo = 0` >- simp[] >>
  `lo - 1 < lo` by decide_tac >>
  gvs[fixed_region_reserved_def] >>
  qpat_x_assum `!i. i < lo ==> _` (qspec_then `lo - 1` mp_tac) >>
  simp[] >> strip_tac >>
  `pos + sz <= global_end` by metis_tac[] >> decide_tac
QED

Theorem ptr_layout_allocation_endpoint:
  mk_concretize_layout reserved positions fn = SOME layout /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  allocation_end positions inst = SOME endpoint ==>
  endpoint <= layout.cl_eom
Proof
  simp[mk_concretize_layout_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule allocation_eom_fold_success >> strip_tac >>
  qpat_x_assum `!i. MEM i _ /\ _ ==> _`
    (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem ptr_layout_item_endpoint[local]:
  static_alloca_items fn = SOME items /\ MEM (a,sz) items /\
  FLOOKUP layout.cl_positions a = SOME p /\
  mk_concretize_layout reserved positions fn = SOME layout ==>
  p + sz <= layout.cl_eom
Proof
  strip_tac >>
  `layout.cl_positions = positions` by metis_tac[ptr_mk_layout_positions] >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(a,sz)` mp_tac) >> simp[] >> strip_tac >>
  gvs[exact_static_alloca_def, AllCaseEqs()] >>
  irule ptr_layout_allocation_endpoint >>
  rpt (goal_assum (drule_at Any)) >>
  gvs[exact_static_alloca_size_def, AllCaseEqs()] >>
  simp[allocation_end_def]
QED

Theorem ptr_concretize_mems_endpoint_or_import:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  MEM (a,p,sz) fn'.fn_mems_used ==>
  (?n. fn'.fn_eom = SOME n /\ p + sz <= n) \/
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
  `?q. FLOOKUP layout.cl_positions a = SOME q` by
    (drule static_alloca_items_MEM >>
     disch_then (qspec_then `(a,sz)` mp_tac) >> simp[] >> strip_tac >>
     drule ptr_mk_layout_positions >> strip_tac >>
     FIRST [drule_all (cj 2 staticLayoutCompletionProofsTheory.complete_alloc_positions_with_imports_success),
            drule (cj 2 staticLayoutCompletionProofsTheory.complete_alloc_positions_success)] >>
     simp[] >> metis_tac[]) >>
  drule_all ptr_layout_item_endpoint >> simp[]
QED

Theorem ptr_step_mems_endpoint_or_import:
  fn.fn_eom = NONE /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  MEM (a,p,sz) out.fpo_function.fn_mems_used ==>
  (?n. out.fpo_function.fn_eom = SOME n /\ p + sz <= n) \/
  MEM (a,p,sz) (imported_mems_used observed.cu_context fn)
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  irule ptr_concretize_mems_endpoint_or_import >> simp[] >>
  qexistsl [`concretize_memloc_fuel fn`,
            `observed.cu_context.ctx_global_reserved`] >> simp[]
QED

Theorem ptr_stage_indexed_mems_endpoint[local]:
  !n name g a p sz.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ max_live_eom C' = SOME eom /\
  list_index name names = SOME n /\
  lookup_function name C'.ctx_functions = SOME g /\
  MEM (a,p,sz) g.fn_mems_used ==> p + sz <= eom
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  drule_all ptr_stage_lookup_origin >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  `MEM g C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule_all ptr_max_live_function_bound >> strip_tac >>
  qpat_x_assum `out.fpo_function = g` (SUBST_ALL_TAC o SYM) >>
  drule_all ptr_step_mems_endpoint_or_import >> strip_tac
  >- (gvs[] >> decide_tac) >>
  drule_all ptr_stage_import_lookup >> strip_tac >>
  rename1 `lookup_function callee C'.ctx_functions = SOME g'` >>
  `list_precedes callee name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  gvs[list_precedes_iff] >>
  qpat_x_assum `!m. m < n ==> _` (qspec_then `i` mp_tac) >> simp[] >>
  disch_then drule_all >> simp[]
QED

Theorem ptr_stage_mems_endpoint_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\ max_live_eom C' = SOME eom /\
  MEM g C'.ctx_functions /\ MEM (a,p,sz) g.fn_mems_used ==>
  p + sz <= eom
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
  drule_all ptr_max_live_function_bound >> strip_tac >>
  qpat_x_assum `out.fpo_function = g` (SUBST_ALL_TAC o SYM) >>
  drule_all ptr_step_mems_endpoint_or_import >> strip_tac
  >- (gvs[] >> decide_tac) >>
  drule_all ptr_stage_import_lookup >> strip_tac >>
  `list_precedes name fn.fn_name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  fs[list_precedes_iff] >>
  drule_all ptr_stage_indexed_mems_endpoint >> simp[]
QED

Theorem ptr_stage_placements_endpoint_bound:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  callee_first names C.ctx_functions /\ max_live_eom C' = SOME eom /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (p,sz) ==>
  p + sz <= eom
Proof
  strip_tac >> gvs[concretizePtrStagePlacementsTheory.ptr_stage_placements_def] >>
  drule_all ptr_stage_mems_endpoint_bound >> simp[]
QED
