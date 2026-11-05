Theory concretizePtrPlacementBounds
Ancestors concretizePtrImportOrigins concretizePtrLayoutOutput
  staticLayoutAllocatorProofs staticLayoutCompletionProofs staticLayoutDefs concretizeMemLocDefs
  o1PassContract venomPassDispatcher venomInst list finite_map words pair

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
