(* Pointer and ordinary posts for a declared mapping leaf. *)
Theory bodyPtrSubscriptSeamMapPost
Ancestors
  bodyPtrDefs exprSimSubscriptMap targetPlaceLive exprSimPtrTopLevelViews
  loweringPosts context ptrDiscipline venomState vyperAST vyperState
  vyperStorageLayoutSafety vyperStorageBackend accountsRelProps
  pred_set words finite_map

Theorem mapping_leaf_ptr_vv_ok:
  storage_mapping_region cx tr slot (Type typ) /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME slot /\
  op_taint tn p.ptr_operand = {} /\ stor_taint_ok cx tn s ==>
  ptr_vv_ok cx typ tv (LocatedValue typ p) es G tn s
Proof
  strip_tac >>
  `!ty. evaluate_type (get_tenv cx) typ = SOME ty ==>
    storage_read_live cx tr
      (if tr then s.vs_transient s.vs_call_ctx.cc_address
       else (s.vs_accounts s.vs_call_ctx.cc_address).storage) slot ty` by
    (rpt strip_tac >> irule nested_pop_mapping_leaf_live >> metis_tac[]) >>
  Cases_on `tr` >>
  gvs[ptr_vv_ok_def, slot_loc_def] >> rpt strip_tac >>
  metis_tac[SRULE [] (Q.SPEC `T` toplevel_live_storage_taint),
            SRULE [] (Q.SPEC `F` toplevel_live_storage_taint),
            arithmeticTheory.ADD_COMM]
QED

Theorem mapping_leaf_vv_storage_live:
  storage_mapping_region cx tr slot (Type typ) /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME slot ==>
  vv_storage_live cx (LocatedValue typ p) es s
Proof
  strip_tac >> Cases_on `tr` >>
  gvs[vv_storage_live_def, slot_loc_def] >> rpt strip_tac >>
  irule nested_pop_mapping_leaf_live >> metis_tac[]
QED

Theorem mapping_leaf_vv_post:
  storage_mapping_region cx tr slot (Type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  contract_storage_well_formed cx ee /\ storage_layout_safe cx /\
  stmt_state_rel ctx fn cenv cx ee s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME slot /\
  wb_frame cenv es sa s0 s ==>
  vv_post ctx fn cenv cx (Subscript ann obj idx) es sa sb s0 ee
    (PlaceR (StoragePlace tr slot tv)) (LocatedValue ann p) s
Proof
  strip_tac >> drule_all mapping_leaf_vv_holds >> strip_tac >>
  drule_all mapping_leaf_vv_storage_live >> strip_tac >>
  simp[vv_post_def, expr_type_def, vv_at_def] >>
  conj_tac >- (Cases_on `tr` >> gvs[slot_loc_def]) >>
  gvs[wb_frame_def] >> gvs[]
QED

Theorem mapping_leaf_ptr_post:
  storage_mapping_region cx tr slot (Type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  contract_storage_well_formed cx ee /\ storage_layout_safe cx /\
  stmt_state_rel ctx fn cenv cx ee s /\ ghost_inv d cenv cx ee G tn s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME slot /\
  op_taint tn p.ptr_operand = {} /\ wb_frame cenv es sa s0 s ==>
  vv_post ctx fn cenv cx (Subscript ann obj idx) es sa sb s0 ee
    (PlaceR (StoragePlace tr slot tv)) (LocatedValue ann p) s /\
  ptr_vv_ok cx (post_value_type cenv (Subscript ann obj idx))
    (PlaceR (StoragePlace tr slot tv)) (LocatedValue ann p) ee G tn s /\
  (!ty op. LocatedValue ann p = StackValue ty op /\
      ~is_word_type (post_value_type cenv (Subscript ann obj idx)) ==>
    ptr_buf_ok cenv (Subscript ann obj idx) op G s) /\
  (!ty q. LocatedValue ann p = LocatedValue ty q /\ q.ptr_location = LocMemory ==>
    ptr_buf_ok cenv (Subscript ann obj idx) q.ptr_operand G s)
Proof
  strip_tac >>
  `stor_taint_ok cx tn s` by gvs[ghost_inv_def] >>
  conj_tac >- (irule mapping_leaf_vv_post >> metis_tac[]) >>
  conj_tac >- (simp[expr_type_def] >> irule mapping_leaf_ptr_vv_ok >> metis_tac[]) >>
  Cases_on `tr` >> simp[slot_loc_def] >> gvs[slot_loc_def]
QED
