(* Restrict a current storage array post to an in-range element. *)
Theory exprSimSubscriptArrayLiveStorageElement
Ancestors
  exprSimSubscriptArrayLiveStorage exprSimPopNestedBase targetPlaceLive
  vyperStorageWritePreservation exprSimHash exprLoweringProps loweringPosts
  loweringStateRelDefs vyperAST accountsRelProps vyperLookupStorage
  vyperStorageBackend vyperState vyperValue targetSubscriptStorage context

Theorem live_storage_array_element_post:
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
    (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
    (LocatedValue (ArrayT et bd) p) q /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  well_formed_type_value etv /\
  storage_read_live cx tr (get_storage cx ee tr) slot (ArrayTV etv bd) /\
  slots_in_range (get_storage cx ee tr) (w2n slot) (ArrayTV etv bd) /\
  Num i < bound_length bd /\
  (!n. bd = Dynamic n ==> Num i < w2n (lookup_storage slot (get_storage cx ee tr))) /\
  off = (case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv /\
  eval_operand dst q = SOME (slot + n2w off) ==>
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee
    (PlaceR (StoragePlace tr (slot + n2w off) etv))
    (LocatedValue et (mk_ptr dst (slot_loc tr))) q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx ee q /\
   wb_frame cenv es ee sa s0 q /\
   (~expr_has_effect (Subscript et obj idx) ==> pure_frame cenv func es sa s0 q)` by
    (fs[vv_post_def, wb_frame_def, expr_has_effect_thm] >> metis_tac[]) >>
  `w2n slot + type_slot_size (ArrayTV etv bd) <= dimword (:256)` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_place_ptr_def, expr_type_def] >> strip_tac >>
     Cases_on `tr` >>
     gvs[vv_holds_def, slot_loc_def, storage_holds_def,
         storage_range_agree_def, evaluate_type_def]) >>
  `storage_read_live cx tr (get_storage cx ee tr) (slot + n2w off) etv /\
   slots_in_range (get_storage cx ee tr) (w2n (slot + n2w off)) etv /\
   w2n (slot + n2w off) + type_slot_size etv <= dimword (:256)` by
    (Cases_on `bd`
     >- (gvs[bound_length_def] >> rpt conj_tac
         >- metis_tac[nested_pop_live_fixed_element]
         >- metis_tac[nested_pop_fixed_slots] >>
         once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
         irule (cj 4 fixed_array_child_region_bounds) >> simp[] >>
         goal_assum (drule_at Any) >> simp[]) >>
     gvs[bound_length_def] >> rpt conj_tac
     >- metis_tac[nested_pop_live_dynamic_element, arithmeticTheory.ADD_COMM]
     >- metis_tac[nested_pop_dynamic_slots, arithmeticTheory.ADD_COMM] >>
     Cases_on `type_slot_size etv = 0`
     >- (simp[] >> qspec_then `(slot:bytes32) + 1w` mp_tac wordsTheory.w2n_lt >> simp[]) >>
     `w2n (slot + n2w (1 + Num i * type_slot_size etv)) + type_slot_size etv <= dimword (:256)` by
       (irule (cj 4 dynamic_array_child_region_bounds) >>
        conj_tac >- simp[] >> qexists_tac `n` >> simp[]) >>
     qpat_x_assum `w2n _ + _ <= _` mp_tac >>
     simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]) >>
  `storage_range_agree (get_storage cx ee tr)
    (if tr then contract_transient q else contract_storage q) (slot + n2w off) etv` by
    (irule storage_range_agree_of_live >>
     conj_tac >- simp[] >> qexistsl_tac [`cx`, `tr`] >> simp[] >>
     Cases_on `tr` >>
     fs[stmt_state_rel_def, state_rel_def, storage_rel_def,
        transient_rel_def, vyperStorageBackendTheory.get_storage_def,
        vfmStateTheory.lookup_account_def]) >>
  `storage_holds cx tr et (PlaceR (StoragePlace tr (slot + n2w off) etv))
      (slot + n2w off) ee q` by
    (drule_all decode_value_from_slots_in_range >> strip_tac >>
     gvs[storage_holds_def, read_storage_slot_eq, read_result_def,
         read_place_def, bind_def, return_def]) >>
  irule vv_post_frame_intro >>
  simp[expr_type_def, vv_holds_def, vv_at_def, vv_place_ptr_def, slot_loc_def] >>
  Cases_on `tr` >> gvs[slot_loc_def, mk_ptr_def]
QED
