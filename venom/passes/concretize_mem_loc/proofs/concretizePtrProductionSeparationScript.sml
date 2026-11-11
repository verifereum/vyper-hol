Theory concretizePtrProductionSeparation
Ancestors venomWfProps
  concretizePtrCandidateSeparation concretizePtrOrdering
  staticLayoutAllocatorProofs concretizeMemLocDefs sorting list finite_map
  venomInst removeUnusedSsaProofs ptrDiscipline
  concretizePtrCompletionSeparation staticLayoutCompletionProofs staticLayoutDefs

Theorem ptr_insert_liveset_perm[local]:
  !xs x. PERM (insert_alloc_liveset_item x xs) (x::xs)
Proof
  Induct >> simp[insert_alloc_liveset_item_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  irule PERM_TRANS >> qexists `h::x::xs` >>
  simp[PERM_SWAP_AT_FRONT, PERM_CONS_IFF]
QED

Theorem ptr_sort_liveset_perm[local]:
  !xs. PERM (sort_alloc_liveset_items xs) xs
Proof
  Induct >> simp[sort_alloc_liveset_items_def] >>
  metis_tac[ptr_insert_liveset_perm, PERM_CONS_IFF, PERM_TRANS]
QED

Theorem ptr_ordered_items_keys_distinct[local]:
  !raw fn ls. ALL_DISTINCT (MAP FST (alloc_liveset_items_ordered raw fn ls))
Proof
  simp[alloc_liveset_items_ordered_def, MAP_MAP_o, combinTheory.o_DEF,
       ml_complete_order_distinct]
QED

Theorem ptr_sort_keys_preserves[local]:
  !xs : (allocation # inst_addr list) list.
  ALL_DISTINCT (MAP FST xs) ==>
  ALL_DISTINCT (MAP FST (sort_alloc_liveset_items xs))
Proof
  metis_tac[ALL_DISTINCT_PERM, PERM_MAP, ptr_sort_liveset_perm]
QED

Theorem ptr_sorted_items_keys_distinct[local]:
  !raw fn ls. ALL_DISTINCT (MAP FST
    (sort_alloc_liveset_items (alloc_liveset_items_ordered raw fn ls)))
Proof
  rpt gen_tac >> irule ptr_sort_keys_preserves >>
  simp[ptr_ordered_items_keys_distinct]
QED

Theorem ptr_sorted_items_mem[local]:
  MEM (a,live) (sort_alloc_liveset_items (alloc_liveset_items_ordered raw fn ls)) <=>
  MEM (a,live) (alloc_liveset_items_ordered raw fn ls)
Proof
  metis_tac[ptr_sort_liveset_perm, PERM_MEM_EQ]
QED

Theorem ptr_imported_liveset_info_mem[local]:
  MEM (a,live,p,s) (imported_liveset_info imports ls) <=>
  MEM (a,p,s) imports /\ FLOOKUP ls a = SOME live
Proof
  simp[imported_liveset_info_def, MEM_FLAT, MEM_MAP,
       pairTheory.EXISTS_PROD] >>
  eq_tac
  >- (rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  strip_tac >> qexists `[(a,live,p,s)]` >> simp[] >>
  qexistsl_tac [`a`,`p`,`s`] >> simp[]
QED

Theorem ptr_pair_const[local]:
  !xs. FILTER (\(x,y). T) xs = xs /\ FILTER (\(x,y). F) xs = []
Proof
  Induct >> simp[] >> PairCases_on `h` >> simp[]
QED

Theorem ptr_pair_fst[local]:
  (\(x,y). x) = FST
Proof
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

Theorem ptr_production_candidate_local_local:
  MEM a (MAP (\i. Allocation i.inst_id)
    (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn))) /\
  MEM b (MAP (\i. Allocation i.inst_id)
    (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn))) /\
  (!c p s. MEM (c,p,s) (imported_mems_used ctx fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  a <> b /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) a = SOME la /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) b = SOME lb /\
  MEM addr la /\ MEM addr lb /\
  FLOOKUP (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved) a = SOME pa /\
  FLOOKUP (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved) b = SOME pb ==>
  pa + get_alloca_size fn a <= pb \/ pb + get_alloca_size fn b <= pa
Proof
  strip_tac >>
  `sinter inst_addr_to la lb <> [] /\ sinter inst_addr_to lb la <> []` by
    (imp_res_tac ptr_context_livesets_sinter_membership >>
     metis_tac[MEM]) >>
  fs[compute_alloc_map_fuel_in_context_def, ptr_pair_const, pairTheory.LAMBDA_PROD,
     pairTheory.FORALL_PROD, pairTheory.EXISTS_PROD] >>
  irule (INST_TYPE [alpha |-> ``:allocation``] ptr_awl_new_new) >>
  qexists `a` >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  qexistsl_tac [`la`,`lb`] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD,
       ptr_sorted_items_keys_distinct, MEM_MAP, pairTheory.EXISTS_PROD,
       ptr_sorted_items_mem, ptr_imported_liveset_info_mem, ptr_pair_fst] >>
  conj_tac
  >- (qpat_x_assum `!c p s. _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[alloc_liveset_items_ordered_def, MEM_MAP, ml_complete_order_mem] >>
      metis_tac[]) >>
  conj_tac >> irule alloc_liveset_items_ordered_coverage >> simp[]
QED

Theorem ptr_production_candidate_local_import:
  MEM a (MAP (\i. Allocation i.inst_id)
    (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn))) /\
  (!c p s. MEM (c,p,s) (imported_mems_used ctx fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  MEM (b,pb,sb) (imported_mems_used ctx fn) /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) a = SOME la /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) b = SOME lb /\
  MEM addr la /\ MEM addr lb /\
  FLOOKUP (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved) a = SOME pa ==>
  pa + get_alloca_size fn a <= pb \/ pb + sb <= pa
Proof
  strip_tac >>
  `sinter inst_addr_to lb la <> []` by
    (imp_res_tac ptr_context_livesets_sinter_membership >> metis_tac[MEM]) >>
  fs[compute_alloc_map_fuel_in_context_def, ptr_pair_const] >>
  irule (INST_TYPE [alpha |-> ``:allocation``] ptr_awl_new_initial) >>
  qexists `a` >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  qexistsl_tac [`b`,`la`,`lb`] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD,
       ptr_sorted_items_keys_distinct, MEM_MAP, pairTheory.EXISTS_PROD,
       ptr_sorted_items_mem, ptr_imported_liveset_info_mem, ptr_pair_fst] >>
  conj_tac
  >- (qpat_x_assum `!c p s. _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[alloc_liveset_items_ordered_def, MEM_MAP, ml_complete_order_mem] >>
      metis_tac[]) >>
  irule alloc_liveset_items_ordered_coverage >> simp[]
QED

Theorem ptr_static_alloca_item_size:
  static_alloca_items fn = SOME items /\ MEM (a,sa) items ==>
  get_alloca_size fn a = sa
Proof
  strip_tac >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(a,sa)` mp_tac) >> simp[] >> strip_tac >>
  `a = Allocation inst.inst_id` by
    gvs[exact_static_alloca_def, AllCaseEqs()] >>
  gvs[] >> simp[get_alloca_size_def] >>
  qmatch_goalsub_abbrev_tac `FIND pred instrs` >>
  `MEM inst instrs /\ pred inst` by
    (simp[Abbr `instrs`, Abbr `pred`, is_alloca_op_def] >>
     gvs[fn_insts_def, fn_insts_blocks_flat]) >>
  `?found. FIND pred instrs = SOME found /\ MEM found instrs /\ pred found` by
    (qpat_x_assum `MEM inst instrs` mp_tac >>
     qpat_x_assum `pred inst` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Induct_on `instrs` >> simp[FIND_thm] >>
     rpt strip_tac >> Cases_on `pred h` >> gvs[] >> metis_tac[]) >>
  `MEM found (fn_insts fn) /\ found.inst_opcode = ALLOCA /\
   found.inst_id = inst.inst_id` by
    (gvs[Abbr `instrs`, Abbr `pred`, fn_insts_def, fn_insts_blocks_flat] >>
     Cases_on `found.inst_opcode` >> gvs[is_alloca_op_def]) >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  rename1 `found.inst_operands = [Lit sz]` >>
  `w2n sz = sa` by
    (irule static_alloca_items_exact_key_size_unique >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`fn`,`inst`,`items`] >> simp[]) >>
  simp[]
QED

Theorem ptr_empty_forced_positions[local]:
  !items positions.
  forced_candidate_positions items FEMPTY positions = positions /\
  merge_forced_positions items FEMPTY positions = SOME positions
Proof
  Induct >> simp[forced_candidate_positions_def, merge_forced_positions_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[forced_candidate_positions_def, merge_forced_positions_def]
QED

Theorem ptr_static_item_local_key[local]:
  static_alloca_items fn = SOME items /\ MEM (a,sa) items ==>
  MEM a (MAP (\i. Allocation i.inst_id)
    (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))
Proof
  strip_tac >> drule static_alloca_items_MEM >>
  disch_then (fn th => fs[th, MEM_MAP, MEM_FILTER]) >>
  gvs[exact_static_alloca_def, AllCaseEqs()] >> metis_tac[is_alloca_op_def]
QED

Theorem ptr_production_completed_local_local:
  fn_ptr_ok P fn /\ static_alloca_items fn = SOME items /\
  candidate = compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg
    (forced_candidate_positions items fn.fn_forced_alloc_positions FEMPTY) reserved /\
  complete_alloc_positions_with_imports items fn.fn_forced_alloc_positions
    reserved imported fn candidate = SOME completed /\
  (!c p s. MEM (c,p,s) (imported_mems_used ctx fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  MEM (a,sa) items /\ MEM (b,sb) items /\ a <> b /\ 0 < sa /\ 0 < sb /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) a = SOME la /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) b = SOME lb /\
  MEM addr la /\ MEM addr lb /\
  FLOOKUP completed a = SOME pa /\ FLOOKUP completed b = SOME pb ==>
  reserved_intervals_disjoint (pa,sa) (pb,sb)
Proof
  strip_tac >>
  `fn.fn_forced_alloc_positions = FEMPTY` by fs[fn_ptr_ok_def] >>
  gvs[ptr_empty_forced_positions] >>
  irule ptr_completion_pair_separation >> simp[] >>
  goal_assum (drule_at (Pat `complete_alloc_positions_with_imports _ _ _ _ _ _ = SOME _`)) >>
  qexistsl_tac [`a`,`b`,`compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved`] >>
  simp[ptr_empty_forced_positions] >>
  rpt strip_tac >>
  `get_alloca_size fn a = sa /\ get_alloca_size fn b = sb` by
    metis_tac[ptr_static_alloca_item_size] >>
  `MEM a (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn))) /\
   MEM b (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))` by
    metis_tac[ptr_static_item_local_key] >>
  drule_all ptr_production_candidate_local_local >>
  simp[reserved_intervals_disjoint_def]
QED

Theorem ptr_production_completed_local_import:
  fn_ptr_ok P fn /\ static_alloca_items fn = SOME items /\
  candidate = compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg
    (forced_candidate_positions items fn.fn_forced_alloc_positions FEMPTY) reserved /\
  imported = FILTER (\(p,s). p <> 0 \/ s <> 0)
    (MAP (\(_,p,s). (p,s)) (imported_mems_used ctx fn)) /\
  complete_alloc_positions_with_imports items fn.fn_forced_alloc_positions
    reserved imported fn candidate = SOME completed /\
  (!c p s. MEM (c,p,s) (imported_mems_used ctx fn) ==>
    ~MEM c (MAP (\i. Allocation i.inst_id)
      (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))) /\
  MEM (a,sa) items /\ 0 < sa /\ 0 < sb /\
  MEM (b,pb,sb) (imported_mems_used ctx fn) /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) a = SOME la /\
  FLOOKUP (context_mem_livesets fuel ctx fn bpr cfg) b = SOME lb /\
  MEM addr la /\ MEM addr lb /\ FLOOKUP completed a = SOME pa ==>
  reserved_intervals_disjoint (pa,sa) (pb,sb)
Proof
  strip_tac >>
  `fn.fn_forced_alloc_positions = FEMPTY` by fs[fn_ptr_ok_def] >>
  `MEM (pb,sb) imported` by
    (simp[MEM_FILTER, MEM_MAP] >>
     qexists `(b,pb,sb)` >> simp[]) >>
  qpat_x_assum `imported = _` kall_tac >>
  gvs[ptr_empty_forced_positions] >>
  Cases_on `FLOOKUP (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved) a`
  >- (`merge_forced_positions items FEMPTY
        (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved) =
        SOME (compute_alloc_map_fuel_in_context fuel ctx fn bpr cfg FEMPTY reserved)` by
        simp[ptr_empty_forced_positions] >>
      drule_all complete_alloc_positions_with_imports_fresh_disjoint >> metis_tac[]) >>
  `FLOOKUP completed a = SOME x` by
    (drule_all (cj 1 complete_alloc_positions_with_imports_success) >> simp[]) >>
  `get_alloca_size fn a = sa` by metis_tac[ptr_static_alloca_item_size] >>
  `MEM a (MAP (\i. Allocation i.inst_id)
    (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn)))` by
    metis_tac[ptr_static_item_local_key] >>
  drule_all ptr_production_candidate_local_import >>
  gvs[reserved_intervals_disjoint_def]
QED
