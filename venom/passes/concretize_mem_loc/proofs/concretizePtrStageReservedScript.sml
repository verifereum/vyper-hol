Theory concretizePtrStageReserved
Ancestors concretizePtrStageBounds concretizePtrLayoutOutput
  concretizePtrImportOrigins staticLayoutCompletionProofs staticLayoutAllocatorProofs
  concretizeMemLocDefs staticLayoutDefs o1PassContract venomPassDispatcher
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
