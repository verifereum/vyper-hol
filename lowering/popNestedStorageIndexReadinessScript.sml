(* Storage-frame target indices retain the actual prefix's live storage. *)
Theory popNestedStorageIndexReadiness
Ancestors
  exprSimPopNestedStorageFrame targetSubscriptContinuation exprSimPopStorage
  vyperStoragePlaceProvenance vyperStorageLayoutSafety vyperStorageBackend
  vyperStatePreservation vyperInterpreter vyperState words arithmetic
  exprSimPopNestedBase targetPlaceLive vyperPlaceStoragePreservation

Theorem pop_nested_storage_index_ready:
  storage_layout_safe cx /\ contract_storage_well_formed cx es /\
  EVERY (storage_frame_expr cx) (target_indices bt) /\
  storage_frame_expr cx e /\
  eval_base_place cx bt es = (INL (PlaceR (StoragePlace tr slot tv)),mid) /\
  bind (eval_expr cx e) (read_result cx) mid = (res,ee) ==>
  storage_read_live cx tr (get_storage cx ee tr) slot tv /\
  w2n slot + type_slot_size tv <= dimword(:256) /\
  (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
    w2n (lookup_storage slot (get_storage cx ee tr)) <= cnt)
Proof
  strip_tac >>
  drule_all nested_pop_eval_base_storage_frame >> strip_tac >>
  `nested_pop_result_slots cx mid (PlaceR (StoragePlace tr slot tv)) /\
   nested_pop_result_live cx mid (PlaceR (StoragePlace tr slot tv))` by
    metis_tac[nested_pop_result_slots_storage_frame,
              nested_pop_result_live_storage_frame] >>
  `!b. get_storage cx ee b = get_storage cx mid b` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
     imp_res_tac read_result_state >> gvs[] >>
     metis_tac[storage_frame_expr_def]) >>
  `slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
   storage_read_live cx tr (get_storage cx ee tr) slot tv` by
    fs[nested_pop_result_slots_def, nested_pop_result_live_def,
       get_storage_backend_eq] >>
  simp[] >> conj_tac
  >- (drule eval_base_place_region >>
      simp[storage_result_region_def] >> strip_tac >>
      Cases_on `type_slot_size tv = 0`
      >- simp[w2n_lt, LESS_IMP_LESS_OR_EQ] >>
      `0 < type_slot_size tv` by decide_tac >>
      drule_all storage_place_region_numeric >> strip_tac >> decide_tac) >>
  rpt strip_tac >> gvs[] >> metis_tac[pop_array_length_bound]
QED
