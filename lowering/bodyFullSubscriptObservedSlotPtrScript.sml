(* A saved slot pointer is checked against the current target storage and
   taint, not the state in which Subscript obtained the base place. *)
Theory bodyFullSubscriptObservedSlotPtr
Ancestors
  bodyPtrDefs loweringPosts accountsRelProps vyperStoragePlaceObserved
  loweringStateRelDefs sourceUnitExecution words pred_set

Theorem subscript_observed_slot_ptr_at:
  dead_lo_ok H D lo cenv cx /\ ghost_inv_at D lo d cenv cx es G tn q /\
  storage_place_observed H (StoragePlace tr slot vt) /\
  evaluate_type (get_tenv cx) ty = SOME vt /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand q = SOME slot /\
  op_taint tn p.ptr_operand = {} ==>
  ptr_vv_ok cx ty (PlaceR (StoragePlace tr slot vt)) (LocatedValue ann p)
    es G tn q
Proof
  strip_tac >>
  Cases_on `type_slot_size vt = 0`
  >- (Cases_on `tr` >> gvs[ptr_vv_ok_def, slot_loc_def]) >>
  `!raw. storage_read_live H tr raw slot vt` by
    (gen_tac >> irule storage_place_observed_read_live >> simp[]) >>
  `stor_taint_ok_at D tn q` by fs[ghost_inv_at_def] >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` kall_tac >>
  Cases_on `tr` >> Cases_on `q.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[ptr_vv_ok_def, slot_loc_def, stor_taint_ok_at_def, dead_lo_ok_def,
      cx_dead_def, SUBSET_DEF, pairTheory.FORALL_PROD, storage_read_live_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[]
QED
