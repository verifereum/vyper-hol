Theory concretizePtrLayoutOutput
Ancestors concretizePtrExecutedCoverage concretizePtrImportOrigins
  concretizeMemLocDefs staticLayoutDefs staticLayoutCompletionProofs
  concretizePtrProductionSeparation staticLayoutAllocatorProofs
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

Theorem ptr_output_local_import_separation:
  fn.fn_eom = NONE /\ fn_ptr_ok P fn /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  fn' = out.fpo_function /\
  static_alloca_items fn = SOME items /\ MEM (a,sa) items /\
  MEM (a,pa,sa) fn'.fn_mems_used /\
  MEM (b,pb,sb) (imported_mems_used ctx fn) /\ 0 < sa /\ 0 < sb /\
  (!c p sz. MEM (c,p,sz) (imported_mems_used ctx fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) a = SOME la /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) b = SOME lb /\
  MEM addr la /\ MEM addr lb ==>
  reserved_intervals_disjoint (pa,sa) (pb,sb)
Proof
  strip_tac >> drule_all ptr_fresh_layout_representation >> strip_tac >>
  `items' = items` by
    (qpat_x_assum `static_alloca_items fn = SOME items'` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `imported_mems_used ctx fn <> []` by (strip_tac >> gvs[]) >>
  qpat_x_assum `(fn_needs_liveness_allocation fn \/ _) ==> _` mp_tac >>
  simp[] >> strip_tac >>
  `?p. FLOOKUP completed a = SOME p` by
    (drule static_alloca_items_MEM >> disch_then (qspec_then `(a,sa)` mp_tac) >>
     disch_then (fn th => fs[th]) >>
     drule_all (cj 2 complete_alloc_positions_with_imports_success) >>
     metis_tac[]) >>
  `layout.cl_positions = completed` by metis_tac[ptr_mk_layout_positions] >>
  `out.fpo_function = apply_context_concretize_layout ctx layout fn /\
   FLOOKUP layout.cl_positions a = SOME p /\
   MEM (a,pa,sa) out.fpo_function.fn_mems_used` by
    (asm_rewrite_tac[] >> metis_tac[]) >>
  `pa = p` by
    (drule_all ptr_step_layout_metadata_exact >> simp[]) >>
  gvs[] >> irule ptr_production_completed_local_import >>
  asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `complete_alloc_positions_with_imports _ _ _ _ _ _ = SOME _`)) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem ptr_two_allocas_multiple[local]:
  !insts. MEM i insts /\ MEM j insts /\ i <> j /\
    is_alloca_op i.inst_opcode /\ is_alloca_op j.inst_opcode ==>
    insts_have_multiple_allocas insts
Proof
  Induct >> simp[insts_have_multiple_allocas_def] >> rpt strip_tac >>
  Cases_on `is_alloca_op h.inst_opcode` >>
  gvs[insts_have_multiple_allocas_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem ptr_static_distinct_needs_liveness:
  static_alloca_items fn = SOME items /\ MEM (a,sa) items /\
  MEM (b,sb) items /\ a <> b ==> fn_needs_liveness_allocation fn
Proof
  strip_tac >>
  drule static_alloca_items_MEM >>
  disch_then (fn th => fs[th]) >>
  simp[fn_needs_liveness_allocation_def] >>
  irule ptr_two_allocas_multiple >>
  metis_tac[venomInstTheory.is_alloca_op_def, optionTheory.SOME_11, pairTheory.PAIR_EQ]
QED

Theorem ptr_output_local_local_separation:
  fn.fn_eom = NONE /\ fn_ptr_ok P fn /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  fn' = out.fpo_function /\
  static_alloca_items fn = SOME items /\ MEM (a,sa) items /\ MEM (b,sb) items /\
  a <> b /\ 0 < sa /\ 0 < sb /\
  MEM (a,pa,sa) fn'.fn_mems_used /\ MEM (b,pb,sb) fn'.fn_mems_used /\
  (!c p sz. MEM (c,p,sz) (imported_mems_used ctx fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) a = SOME la /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) b = SOME lb /\
  MEM addr la /\ MEM addr lb ==>
  reserved_intervals_disjoint (pa,sa) (pb,sb)
Proof
  strip_tac >>
  `fn_needs_liveness_allocation fn` by metis_tac[ptr_static_distinct_needs_liveness] >>
  drule_all ptr_fresh_layout_representation >> strip_tac >>
  `items' = items` by
    (qpat_x_assum `static_alloca_items fn = SOME items'` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `(fn_needs_liveness_allocation fn \/ _) ==> _` mp_tac >>
  simp[] >> strip_tac >>
  `?p. FLOOKUP completed a = SOME p` by
    (drule static_alloca_items_MEM >> disch_then (qspec_then `(a,sa)` mp_tac) >>
     disch_then (fn th => fs[th]) >>
     drule_all (cj 2 complete_alloc_positions_with_imports_success) >> metis_tac[]) >>
  `?q. FLOOKUP completed b = SOME q` by
    (drule static_alloca_items_MEM >> disch_then (qspec_then `(b,sb)` mp_tac) >>
     disch_then (fn th => fs[th]) >>
     drule_all (cj 2 complete_alloc_positions_with_imports_success) >> metis_tac[]) >>
  `layout.cl_positions = completed` by metis_tac[ptr_mk_layout_positions] >>
  `out.fpo_function = apply_context_concretize_layout ctx layout fn /\
   FLOOKUP layout.cl_positions a = SOME p /\
   FLOOKUP layout.cl_positions b = SOME q /\
   MEM (a,pa,sa) out.fpo_function.fn_mems_used /\
   MEM (b,pb,sb) out.fpo_function.fn_mems_used` by
    (asm_rewrite_tac[] >> metis_tac[]) >>
  `pa = p /\ pb = q` by metis_tac[ptr_step_layout_metadata_exact] >>
  gvs[] >> irule ptr_production_completed_local_local >>
  asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `complete_alloc_positions_with_imports _ _ _ _ _ _ = SOME _`)) >>
  asm_rewrite_tac[] >> metis_tac[]
QED
