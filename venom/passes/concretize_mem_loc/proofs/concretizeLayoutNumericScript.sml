Theory concretizeLayoutNumeric
Ancestors concretizeLayoutMetadata staticLayoutCompletionProofs
  staticLayoutAllocatorProofs concretizeMemLocDefs staticLayoutDefs
  list pair finite_map words

Theorem context_layout_local_position:
  static_alloca_items fn = SOME items /\ MEM (a,sz) items /\
  compute_function_layout_fuel_in_context fuel ctx reserved fn = SOME layout ==>
  ?p. FLOOKUP layout.cl_positions a = SOME p /\
      p + sz < dimword (:256) /\
      (0 < sz ==> EVERY (reserved_intervals_disjoint (p,sz)) reserved)
Proof
  strip_tac >>
  `?inst. MEM inst (fn_insts fn) /\ exact_static_alloca inst = SOME (a,sz)` by
    metis_tac[static_alloca_items_MEM] >>
  qpat_x_assum `compute_function_layout_fuel_in_context _ _ _ _ = _` mp_tac >>
  simp[compute_function_layout_fuel_in_context_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all complete_alloc_positions_with_imports_success >> strip_tac >>
  `?p. FLOOKUP completed a = SOME p /\ p + sz < dimword (:256)` by metis_tac[] >>
  `0 < sz ==> EVERY (reserved_intervals_disjoint (p,sz)) reserved` by
    (strip_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     `sz = sz'` by metis_tac[static_alloca_items_exact_key_size_unique] >> gvs[]) >>
  gvs[mk_concretize_layout_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem context_layout_local_lookup_find:
  static_alloca_items fn = SOME items /\ MEM (a,sz) items /\
  FLOOKUP layout.cl_positions a = SOME p ==>
  FIND (\(b,q,t). b = a)
    (apply_context_concretize_layout ctx layout fn).fn_mems_used = SOME (a,p,sz)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST items)` by metis_tac[static_alloca_items_ALL_DISTINCT] >>
  drule_all context_layout_own_find >> simp[]
QED
