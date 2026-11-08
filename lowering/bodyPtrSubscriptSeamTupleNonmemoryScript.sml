(* Nonmemory tuple selection: restrict slot taint, preserving code cleanliness. *)
Theory bodyPtrSubscriptSeamTupleNonmemory
Ancestors
  bodyPtrSubscriptSeamTuplePost bodyPtrAttributeFields bodyPtrAttributeStorage
  bodyPtrDefs ptrDiscipline targetPlaceLive accountsRelProps
  vyperStoragePlaceRegion vyperState loweringPosts compileEnv words arithmetic
  exprSimProps exprSimTuple exprLowering exprSimAttributeProps context list rich_list

Theorem tuple_storage_child_address:
  storage_holds cx tr ty btv w es s /\
  evaluate_type (get_tenv cx) ty = SOME (TupleTV tvs) /\
  k < LENGTH tvs /\ 0 < type_slot_size (EL k tvs) ==>
  w2n (w + n2w (tuple_prefix_slot_size k tvs)) =
    w2n w + tuple_prefix_slot_size k tvs
Proof
  strip_tac >>
  `oEL k tvs = SOME (EL k tvs)` by simp[oEL_THM] >>
  drule tuple_component_slot_end_bound >> strip_tac >>
  gvs[storage_holds_def, storage_range_agree_def] >>
  `w2n w + tuple_prefix_slot_size k tvs < dimword (:256)` by decide_tac >>
  Cases_on `w` >> gvs[word_add_n2w]
QED

Theorem tuple_nonmemory_child_ptr:
  ptr_vv_ok cx (TupleT tys) tv vv ee G tn s /\ vv_loc vv <> LocMemory /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) ct = SOME (EL k tvs) /\ k < LENGTH tvs /\
  eval_operand (vv_operand vv) s = SOME w /\ eval_operand dst t = SOME (w + n2w off) /\
  ((vv_loc vv = LocStorage \/ vv_loc vv = LocTransient) ==>
    off = tuple_prefix_slot_size k tvs) /\
  ((vv_loc vv = LocStorage \/ vv_loc vv = LocTransient) /\
    0 < type_slot_size (EL k tvs) ==> w2n (w + n2w off) = w2n w + off) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  op_taint tn' dst = {} /\ (vv_loc vv = LocCode ==> op_prov H dst = NONE) ==>
  ptr_vv_ok cx ct tv' (LocatedValue ann (mk_ptr dst (vv_loc vv))) ee' H tn' t
Proof
  strip_tac >> irule ptr_vv_ok_nonmemory >>
  simp[mk_ptr_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `type_slot_size (EL k tvs) = 0` >- gvs[] >>
  `oEL k tvs = SOME (EL k tvs)` by simp[oEL_THM] >>
  drule tuple_component_slot_end_bound >> strip_tac >>
  `w2n w <= w2n k' /\ w2n k' < w2n w + type_slot_size (TupleTV tvs)` by decide_tac >>
  Cases_on `vv` >> gvs[vv_loc_def, vv_location_def] >>
  gvs[ptr_vv_ok_def, vv_operand_def] >>
  qpat_x_assum `!j byte. _` (qspecl_then [`k'`, `b`] mp_tac) >>
  simp[] >> simp[Once dead_bytes_def] >> strip_tac >>
  simp[nested_pop_dead_tuple_selected]
QED

Theorem tuple_nonmemory_selected_ptr:
  vv_post ctx func cenv cx obj es sa sm s0 ee tv vv s /\
  post_value_type cenv obj = TupleT tys /\ expr_sim_inv cenv cx env es /\
  ptr_vv_ok cx (TupleT tys) tv vv ee G tn s /\ vv_loc vv <> LocMemory /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) ct = SOME (EL k tvs) /\ k < LENGTH tvs /\
  eval_operand (vv_operand vv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w (tuple_offset cenv tys (vv_loc vv) k)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  op_taint tn' dst = {} /\ (vv_loc vv = LocCode ==> op_prov H dst = NONE) ==>
  ptr_vv_ok cx ct tv' (LocatedValue ann (mk_ptr dst (vv_loc vv))) ee' H tn' t
Proof
  strip_tac >>
  `vv_holds cenv cx (TupleT tys) tv vv ee s` by gvs[vv_post_def] >>
  reverse (Cases_on `vv_loc vv = LocStorage \/ vv_loc vv = LocTransient`)
  >- (irule ptr_vv_ok_nonmemory >> Cases_on `vv_loc vv` >> gvs[mk_ptr_def]) >>
  `storage_holds cx (vv_loc vv = LocTransient) (TupleT tys) tv w ee s` by
    (Cases_on `vv` >>
     gvs[vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def] >>
     Cases_on `p.ptr_location` >> gvs[] >> metis_tac[]) >>
  `tuple_offset cenv tys (vv_loc vv) k = tuple_prefix_slot_size k tvs` by
    (drule_all tuple_location_sizes >>
     disch_then (qspec_then `vv_loc vv` mp_tac) >>
     Cases_on `vv_loc vv` >>
     gvs[tuple_offset_def, is_slot_addressed_def, tuple_prefix_slot_size_sum, MAP_TAKE]) >>
  `0 < type_slot_size (EL k tvs) ==>
     w2n (w + n2w (tuple_prefix_slot_size k tvs)) = w2n w + tuple_prefix_slot_size k tvs` by
    (strip_tac >> drule_all tuple_storage_child_address >> simp[]) >>
  irule tuple_nonmemory_child_ptr >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
