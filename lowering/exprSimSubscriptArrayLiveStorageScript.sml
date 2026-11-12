(* Current-state storage representation for a live captured array base. *)
Theory exprSimSubscriptArrayLiveStorage
Ancestors
  targetSubscriptStorage exprSimSubscriptArraySource
  accountsRelProps loweringPosts loweringStateRelDefs exprLoweringProps vyperLookupStorage
  vyperStorageBackend vyperState

Theorem live_storage_holds_current:
  storage_holds cx tr ty r slot mid u /\
  evaluate_type (get_tenv cx) ty = SOME vt /\
  well_formed_type_value vt /\
  stmt_state_rel ctx func cenv cx ee s /\
  storage_read_live cx tr (get_storage cx ee tr) slot vt /\
  slots_in_range (get_storage cx ee tr) (w2n slot) vt ==>
  storage_holds cx tr ty (PlaceR (StoragePlace tr slot vt)) slot ee s
Proof
  strip_tac >>
  `w2n slot + type_slot_size vt <= dimword (:256)` by
    fs[storage_holds_def, storage_range_agree_def] >>
  `storage_range_agree (get_storage cx ee tr)
    (if tr then contract_transient s else contract_storage s) slot vt` by
    (irule storage_range_agree_of_live >>
     conj_tac >- simp[] >> qexistsl_tac [`cx`, `tr`] >> simp[] >>
     Cases_on `tr` >>
     fs[stmt_state_rel_def, state_rel_def, storage_rel_def,
        transient_rel_def, vyperStorageBackendTheory.get_storage_def,
        vfmStateTheory.lookup_account_def]) >>
  drule_all decode_value_from_slots_in_range >> strip_tac >>
  simp[storage_holds_def, read_storage_slot_eq, read_result_def,
       read_place_def, bind_def, return_def] >>
  goal_assum (drule_at Any) >> simp[]
QED
