Theory concretizePtrLayoutOutput
Ancestors concretizePtrExecutedCoverage concretizePtrImportOrigins
  concretizeMemLocDefs staticLayoutDefs staticLayoutCompletionProofs
  o1PassContract list finite_map

Theorem ptr_fresh_layout_representation:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' ==>
  ?items layout. static_alloca_items fn = SOME items /\
    fn' = apply_context_concretize_layout ctx layout fn /\
    ((fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []) ==>
      ?candidate imported completed.
        candidate = compute_alloc_map_fuel_in_context fuel ctx fn
          (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)
          (forced_candidate_positions items fn.fn_forced_alloc_positions FEMPTY) reserved /\
        imported = FILTER (\(p,s). p <> 0 \/ s <> 0)
          (MAP (\(_,p,s). (p,s)) (imported_mems_used ctx fn)) /\
        complete_alloc_positions_with_imports items fn.fn_forced_alloc_positions
          reserved imported fn candidate = SOME completed /\
        mk_concretize_layout (reserved ++ imported) completed fn = SOME layout) /\
    (~(fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []) ==>
      ?completed. complete_alloc_positions fn.fn_forced_alloc_positions reserved fn FEMPTY = SOME completed /\
        mk_concretize_layout reserved completed fn = SOME layout)
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def] >>
  Cases_on `fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []` >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `compute_function_layout_fuel_in_context _ _ _ _ = _` mp_tac >>
      simp[compute_function_layout_fuel_in_context_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `compute_function_layout_eval _ _ = _` mp_tac >>
  simp[compute_function_layout_eval_def, AllCaseEqs()] >> rpt strip_tac >>
  `?items. static_alloca_items fn = SOME items` by
    (qpat_x_assum `complete_alloc_positions _ _ _ _ = SOME _` mp_tac >>
     simp[complete_alloc_positions_def, AllCaseEqs()] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ptr_layout_local_metadata:
  static_alloca_items fn = SOME items /\ MEM (a,sz) items /\
  FLOOKUP layout.cl_positions a = SOME p ==>
  MEM (a,p,sz) (apply_context_concretize_layout ctx layout fn).fn_mems_used
Proof
  strip_tac >> drule_all ptr_layout_own_mems >>
  disch_then (qspecl_then [`layout`,`ctx`] mp_tac) >> simp[]
QED

Theorem ptr_step_layout_metadata_exact:
  fn.fn_eom = NONE /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  out.fpo_function = apply_context_concretize_layout ctx layout fn /\
  static_alloca_items fn = SOME items /\ MEM (a,sz) items /\
  FLOOKUP layout.cl_positions a = SOME p /\
  MEM (a,q,t) out.fpo_function.fn_mems_used ==> q = p /\ t = sz
Proof
  strip_tac >>
  `MEM (a,p,sz) out.fpo_function.fn_mems_used` by
    metis_tac[ptr_layout_local_metadata] >>
  metis_tac[ptr_step_mems_functional]
QED

Theorem ptr_mk_layout_positions:
  mk_concretize_layout reserved completed fn = SOME layout ==>
  layout.cl_positions = completed
Proof
  simp[mk_concretize_layout_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED
