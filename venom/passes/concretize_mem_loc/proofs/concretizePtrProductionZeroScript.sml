Theory concretizePtrProductionZero
Ancestors concretizePtrZeroPlacements concretizePtrLayoutOutput
  concretizePtrProductionSeparation staticLayoutCompletionProofs
  concretizeMemLocDefs staticLayoutAllocatorProofs ptrDiscipline list finite_map

Theorem ptr_livesets_zero:
  !todo result already reserved a.
  (!live sz. MEM (a,live,sz) todo ==> sz = 0) /\
  (!p. FLOOKUP result a = SOME p ==> p = 0) ==>
  !p. FLOOKUP (allocate_with_livesets reserved already todo result) a = SOME p ==> p = 0
Proof
  Induct >> simp[allocate_with_livesets_def] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  pure_rewrite_tac[allocate_with_livesets_def, LET_THM] >>
  BETA_TAC >> pairarg_tac >>
  pop_assum (fn th => assume_tac th >> SUBST1_TAC th) >>
  simp[NoAsms] >> rpt strip_tac >>
  qpat_x_assum `!result already reserved a. _`
    (drule_at (Pat `FLOOKUP (allocate_with_livesets _ _ _ _) _ = SOME _`)) >>
  Cases_on `h0 = a` >> gvs[ptr_allocate_one_zero, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem ptr_compute_zero:
  get_alloca_size fn a = 0 /\ (!p. FLOOKUP seed a = SOME p ==> p = 0) ==>
  !p. FLOOKUP (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg seed reserved) a = SOME p ==>
      p = 0
Proof
  strip_tac >> simp[compute_alloc_map_fuel_in_context_def] >>
  rpt strip_tac >>
  drule_at (Pat `FLOOKUP (allocate_with_livesets _ _ _ _) _ = SOME _`) ptr_livesets_zero >>
  (impl_tac >- simp[MEM_MAP, pairTheory.EXISTS_PROD]) >> simp[]
QED

Theorem ptr_forced_candidate_empty:
  !items positions. forced_candidate_positions items FEMPTY positions = positions
Proof
  Induct >> simp[forced_candidate_positions_def] >>
  gen_tac >> PairCases_on `h` >> simp[forced_candidate_positions_def]
QED

Theorem ptr_production_layout_zero:
  static_alloca_items fn = SOME items /\ MEM (a,0) items /\
  complete_alloc_positions_with_imports items FEMPTY reserved imported fn
    (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved) = SOME completed /\
  mk_concretize_layout rs completed fn = SOME layout ==>
  FLOOKUP layout.cl_positions a = SOME 0
Proof
  strip_tac >>
  `get_alloca_size fn a = 0` by metis_tac[ptr_static_alloca_item_size] >>
  `!p. FLOOKUP completed a = SOME p ==> p = 0` by
    (drule_at (Pat `complete_alloc_positions_with_imports _ _ _ _ _ _ = SOME _`)
       ptr_complete_imports_zero >>
     disch_then (qspec_then `a` mp_tac) >>
     `!p. FLOOKUP (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved) a = SOME p ==> p = 0` by
       (rpt strip_tac >>
        drule_at (Pat `FLOOKUP (compute_alloc_map_fuel_in_context _ _ _ _ _ _ _) _ = SOME _`)
          ptr_compute_zero >> simp[]) >> simp[]) >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(a,0)` mp_tac) >> simp[] >> strip_tac >>
  drule_all (cj 2 complete_alloc_positions_with_imports_success) >>
  strip_tac >>
  `layout.cl_positions = completed` by metis_tac[ptr_mk_layout_positions] >>
  metis_tac[]
QED

Theorem ptr_eval_layout_zero:
  static_alloca_items fn = SOME items /\ MEM (a,0) items /\
  complete_alloc_positions FEMPTY reserved fn FEMPTY = SOME completed /\
  mk_concretize_layout reserved completed fn = SOME layout ==>
  FLOOKUP layout.cl_positions a = SOME 0
Proof
  strip_tac >>
  `!p. FLOOKUP completed a = SOME p ==> p = 0` by
    (drule_at (Pat `complete_alloc_positions _ _ _ _ = SOME _`) ptr_complete_zero >>
     disch_then (qspecl_then [`items`,`a`] mp_tac) >> simp[]) >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(a,0)` mp_tac) >> simp[] >> strip_tac >>
  drule (cj 2 complete_alloc_positions_success) >> strip_tac >>
  `layout.cl_positions = completed` by metis_tac[ptr_mk_layout_positions] >>
  metis_tac[]
QED

Theorem ptr_production_zero_metadata:
  fn.fn_eom = NONE /\ fn_ptr_ok P fn /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  static_alloca_items fn = SOME items /\ MEM (a,0) items ==>
  MEM (a,0,0) fn'.fn_mems_used
Proof
  strip_tac >>
  `fn.fn_forced_alloc_positions = FEMPTY` by fs[fn_ptr_ok_def] >>
  drule_all ptr_fresh_layout_representation >> strip_tac >> gvs[] >>
  `FLOOKUP layout.cl_positions a = SOME 0` by
    (Cases_on `fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []` >>
     gvs[ptr_forced_candidate_empty]
     >- metis_tac[ptr_production_layout_zero] >>
     metis_tac[ptr_eval_layout_zero]) >>
  metis_tac[ptr_layout_local_metadata]
QED
