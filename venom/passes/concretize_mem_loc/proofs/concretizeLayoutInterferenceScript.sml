Theory concretizeLayoutInterference
Ancestors concretizeLayoutCompletion concretizeLayoutExtension
  staticLayoutAllocatorProofs concretizeMemLocDefs staticLayoutDefs
  concretizeAnalysisSizeLookup venomInst venomWf
  list pair finite_map enumeral

Theorem MEM_insert_alloc_liveset_item:
  !x y xs. MEM y (insert_alloc_liveset_item x xs) <=> y = x \/ MEM y xs
Proof
  gen_tac >> gen_tac >> Induct_on `xs` >>
  simp[insert_alloc_liveset_item_def] >> gen_tac >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem MEM_sort_alloc_liveset_items:
  !xs y. MEM y (sort_alloc_liveset_items xs) <=> MEM y xs
Proof
  Induct >> simp[sort_alloc_liveset_items_def, MEM_insert_alloc_liveset_item] >>
  metis_tac[]
QED

Theorem ALL_DISTINCT_MAP_insert_alloc_liveset_item:
  !xs x f. ALL_DISTINCT (MAP f (insert_alloc_liveset_item x xs)) <=>
    ~MEM (f x) (MAP f xs) /\ ALL_DISTINCT (MAP f xs)
Proof
  Induct >> simp[insert_alloc_liveset_item_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[MEM_MAP, MEM_insert_alloc_liveset_item] >> metis_tac[]
QED

Theorem ALL_DISTINCT_MAP_sort_alloc_liveset_items:
  !xs f. ALL_DISTINCT (MAP f (sort_alloc_liveset_items xs)) <=>
    ALL_DISTINCT (MAP f xs)
Proof
  Induct >> simp[sort_alloc_liveset_items_def,
    ALL_DISTINCT_MAP_insert_alloc_liveset_item, MEM_MAP,
    MEM_sort_alloc_liveset_items]
QED

Theorem alloc_liveset_items_ordered_distinct:
  ALL_DISTINCT (MAP FST (alloc_liveset_items_ordered raw fn ls))
Proof
  simp[alloc_liveset_items_ordered_def, MAP_COMPOSE, combinTheory.o_DEF,
    ml_complete_order_distinct]
QED

Theorem static_alloca_item_size:
  fn_inst_ids_distinct fn /\ static_alloca_items fn = SOME items /\
  MEM (a,s) items ==> get_alloca_size fn a = s
Proof
  strip_tac >>
  `?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    exact_static_alloca inst = SOME (a,s)` by metis_tac[static_alloca_items_MEM] >>
  gvs[exact_static_alloca_def, exact_static_alloca_size_def, AllCaseEqs()] >>
  metis_tac[get_alloca_size_from_inst]
QED

Theorem static_alloca_item_ordered_coverage:
  static_alloca_items fn = SOME items /\ MEM (a,s) items /\
  FLOOKUP ls a = SOME live ==>
  MEM (a,live) (alloc_liveset_items_ordered raw fn ls)
Proof
  strip_tac >> irule alloc_liveset_items_ordered_coverage >> simp[] >>
  `?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    exact_static_alloca inst = SOME (a,s)` by metis_tac[static_alloca_items_MEM] >>
  gvs[exact_static_alloca_def, AllCaseEqs()] >>
  simp[MEM_MAP, MEM_FILTER] >> qexists_tac `inst` >> simp[is_alloca_op_def]
QED

Theorem imported_liveset_info_MEM:
  MEM (a,l,p,s) (imported_liveset_info imports ls) <=>
  MEM (a,p,s) imports /\ FLOOKUP ls a = SOME l
Proof
  simp[imported_liveset_info_def, MEM_FLAT, MEM_MAP, EXISTS_PROD] >>
  eq_tac
  >- (rpt strip_tac >> gvs[AllCaseEqs()]) >>
  strip_tac >> qexists_tac `[(a,l,p,s)]` >> simp[] >>
  qexistsl_tac [`a`,`p`,`s`] >> simp[]
QED

Theorem context_candidate_extension:
  (!a l. MEM (a,l) (alloc_liveset_items_ordered raw fn ls) ==>
    !p s. ~MEM (a,p,s) imports) ==>
  ?E.
    MAP (\(a,l,p,s). (a,l,s)) E =
      MAP (\(a,l). (a,l,get_alloca_size fn a))
        (sort_alloc_liveset_items (alloc_liveset_items_ordered raw fn ls)) /\
    (!a l p s. MEM (a,l,p,s) E ==>
      FLOOKUP (allocate_with_livesets reserved (imported_liveset_info imports ls)
        (MAP (\(a,l). (a,l,get_alloca_size fn a))
          (sort_alloc_liveset_items (alloc_liveset_items_ordered raw fn ls)))
        FEMPTY) a = SOME p) /\
    (!a l p s b k q t. MEM (a,l,p,s) E /\ MEM (b,q,t) imports /\
      FLOOKUP ls b = SOME k /\ sinter inst_addr_to l k <> [] ==>
      p+s <= q \/ q+t <= p) /\
    (!a l p s b k q t. MEM (a,l,p,s) E /\ MEM (b,k,q,t) E /\
      a <> b /\ sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p)
Proof
  strip_tac >>
  qspecl_then [`reserved`, `imported_liveset_info imports ls`,
    `MAP (\(a,l). (a,l,get_alloca_size fn a))
      (sort_alloc_liveset_items (alloc_liveset_items_ordered raw fn ls))`,
    `FEMPTY`] mp_tac allocation_extension >>
  (impl_tac >-
    (simp[MAP_COMPOSE, combinTheory.o_DEF, LAMBDA_PROD,
       ALL_DISTINCT_MAP_sort_alloc_liveset_items,
       alloc_liveset_items_ordered_distinct] >>
     simp[MEM_MAP, EXISTS_PROD, MEM_sort_alloc_liveset_items,
       imported_liveset_info_MEM] >>
     conj_tac >- simp[alloc_liveset_items_ordered_def, MAP_COMPOSE,
       combinTheory.o_DEF, ml_complete_order_distinct] >> metis_tac[])) >>
  strip_tac >> qexists_tac `E` >> simp[] >>
  metis_tac[imported_liveset_info_MEM]
QED

Theorem forced_candidate_positions_empty:
  !items positions. forced_candidate_positions items FEMPTY positions = positions
Proof
  Induct >> simp[forced_candidate_positions_def, FORALL_PROD]
QED

Theorem merge_forced_positions_empty:
  !items positions. merge_forced_positions items FEMPTY positions = SOME positions
Proof
  Induct >> simp[merge_forced_positions_def, FORALL_PROD]
QED

Theorem context_layout_preserves_candidate:
  static_alloca_items fn = SOME items /\ fn.fn_forced_alloc_positions = FEMPTY /\
  compute_function_layout_fuel_in_context fuel ctx reserved fn = SOME layout /\
  FLOOKUP (compute_alloc_map_fuel_in_context fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn) FEMPTY reserved) a = SOME p ==>
  FLOOKUP layout.cl_positions a = SOME p
Proof
  strip_tac >>
  qpat_x_assum `compute_function_layout_fuel_in_context _ _ _ _ = _` mp_tac >>
  simp[compute_function_layout_fuel_in_context_def, forced_candidate_positions_empty] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule complete_alloc_positions_with_imports_preserves_lookup >>
  simp[merge_forced_positions_empty] >> strip_tac >>
  gvs[mk_concretize_layout_def, AllCaseEqs()]
QED

Theorem FILTER_pair_constant:
  !xs c. FILTER (\(a,b). c) xs = if c then xs else []
Proof
  Induct >> simp[] >> PairCases_on `h` >> simp[] >> metis_tac[]
QED

Theorem context_layout_interference_extension:
  static_alloca_items fn = SOME items /\ fn_inst_ids_distinct fn /\
  fn.fn_forced_alloc_positions = FEMPTY /\
  compute_function_layout_fuel_in_context fuel ctx reserved fn = SOME layout /\
  (!inst p s. MEM inst (fn_insts fn) /\ is_alloca_op inst.inst_opcode ==>
    ~MEM (Allocation inst.inst_id,p,s) (imported_mems_used ctx fn)) ==>
  ?E.
    (!a s l. MEM (a,s) items /\
      FLOOKUP (context_mem_livesets fuel ctx fn
        (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) a = SOME l ==>
      ?p. MEM (a,l,p,s) E) /\
    (!a l p s. MEM (a,l,p,s) E ==> FLOOKUP layout.cl_positions a = SOME p) /\
    (!a l p s b k q t. MEM (a,l,p,s) E /\
      MEM (b,q,t) (imported_mems_used ctx fn) /\
      FLOOKUP (context_mem_livesets fuel ctx fn
        (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) b = SOME k /\
      sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p) /\
    (!a l p s b k q t. MEM (a,l,p,s) E /\ MEM (b,k,q,t) E /\
      a <> b /\ sinter inst_addr_to l k <> [] ==> p+s <= q \/ q+t <= p)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `FLOOKUP ls` >>
  qabbrev_tac `raw = ml_ordered_keys fuel (bp_analyze_fuel fuel (cfg_analyze fn) fn)
    (\name. MAP FST (callee_mems_used ctx name))
    (\a. if context_alloca_size fn (imported_mems_used ctx fn) a = 0 then NONE
         else SOME (context_alloca_size fn (imported_mems_used ctx fn) a))
    [] (cfg_analyze fn) fn` >>
  `!a l. MEM (a,l) (alloc_liveset_items_ordered raw fn ls) ==>
    !p s. ~MEM (a,p,s) (imported_mems_used ctx fn)` by
    (simp[alloc_liveset_items_ordered_def, MEM_MAP, ml_complete_order_mem,
       MEM_FILTER] >> metis_tac[]) >>
  drule context_candidate_extension >>
  disch_then (qspec_then `reserved` strip_assume_tac) >>
  qexists_tac `E` >>
  conj_tac >- suspend "coverage" >>
  conj_tac >- suspend "positions" >>
  metis_tac[]
QED

Resume context_layout_interference_extension[coverage]:
  rpt strip_tac >>
  `MEM (a,l) (alloc_liveset_items_ordered raw fn ls)` by
    metis_tac[static_alloca_item_ordered_coverage] >>
  `get_alloca_size fn a = s` by metis_tac[static_alloca_item_size] >>
  `MEM (a,l,s) (MAP (\(a,l). (a,l,get_alloca_size fn a))
    (sort_alloc_liveset_items (alloc_liveset_items_ordered raw fn ls)))` by
    (simp[MEM_MAP, EXISTS_PROD, MEM_sort_alloc_liveset_items] >> metis_tac[]) >>
  qpat_x_assum `MEM (a,l,s) (MAP _ _)` mp_tac >>
  qpat_x_assum `MAP _ E = _` (fn th => once_rewrite_tac[GSYM th]) >>
  simp[MEM_MAP, EXISTS_PROD]
QED

Resume context_layout_interference_extension[positions]:
  rpt strip_tac >> irule context_layout_preserves_candidate >>
  goal_assum (drule_at (Pat `compute_function_layout_fuel_in_context _ _ _ _ = _`)) >>
  simp[] >>
  simp[compute_alloc_map_fuel_in_context_def, FILTER_pair_constant] >>
  qpat_x_assum `!a l p s. MEM (a,l,p,s) E ==> FLOOKUP _ a = SOME p` drule >>
  simp[Abbr `raw`, Abbr `ls`, LAMBDA_PROD]
QED

Finalise context_layout_interference_extension

Theorem context_layout_local_import_disjoint:
  static_alloca_items fn = SOME items /\ fn_inst_ids_distinct fn /\
  fn.fn_forced_alloc_positions = FEMPTY /\
  compute_function_layout_fuel_in_context fuel ctx reserved fn = SOME layout /\
  (!inst p s. MEM inst (fn_insts fn) /\ is_alloca_op inst.inst_opcode ==>
    ~MEM (Allocation inst.inst_id,p,s) (imported_mems_used ctx fn)) /\
  MEM (a,s) items /\ MEM (b,q,t) (imported_mems_used ctx fn) /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) a = SOME l /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) b = SOME k /\
  sinter inst_addr_to l k <> [] ==>
  ?p. FLOOKUP layout.cl_positions a = SOME p /\ (p+s <= q \/ q+t <= p)
Proof
  strip_tac >> drule_all context_layout_interference_extension >> strip_tac >>
  metis_tac[]
QED

Theorem context_layout_local_local_disjoint:
  static_alloca_items fn = SOME items /\ fn_inst_ids_distinct fn /\
  fn.fn_forced_alloc_positions = FEMPTY /\
  compute_function_layout_fuel_in_context fuel ctx reserved fn = SOME layout /\
  (!inst p s. MEM inst (fn_insts fn) /\ is_alloca_op inst.inst_opcode ==>
    ~MEM (Allocation inst.inst_id,p,s) (imported_mems_used ctx fn)) /\
  MEM (a,s) items /\ MEM (b,t) items /\ a <> b /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) a = SOME l /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) b = SOME k /\
  sinter inst_addr_to l k <> [] ==>
  ?p q. FLOOKUP layout.cl_positions a = SOME p /\
        FLOOKUP layout.cl_positions b = SOME q /\ (p+s <= q \/ q+t <= p)
Proof
  strip_tac >> drule_all context_layout_interference_extension >> strip_tac >>
  metis_tac[]
QED
