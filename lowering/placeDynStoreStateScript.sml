Theory placeDynStoreState
Ancestors
  placeDynStorageEffect placeStoreStatePatch placeStoreRegion storageDynPrefixLive
  placeDynLayout stmtSimStoreCopy exprLoweringProps exprSimProps compileEnv loweringStateRelDefs loweringPosts
  vyperPlaceFrames vyperStorageBackend venomState valueEncoding vyperTyping
  vyperStorageLayoutSafety vyperStoragePlaceRegion
  list words arithmetic

Theorem place_dyn_storage_write_state:
  stmt_state_rel ctx func cenv cx ee q /\
  declared_storage_region cx mid name subs = SOME (tr,root,tv) /\
  w2n root + type_slot_size tv <= dimword (:256) /\
  (!mid' name' subs' root' tv'.
    declared_storage_region cx mid' name' subs' = SOME (tr,root',tv') /\
    (root',tv') <> (root,tv) ==>
    ranges_disjoint (w2n root) (type_slot_size tv)
                    (w2n root') (type_slot_size tv')) /\
  storage_subregion tv path delta (ArrayTV et (Dynamic cap)) /\
  w2n k = w2n root + delta /\
  well_formed_type_value (ArrayTV et (Dynamic cap)) /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n b) q.vs_memory /\
  w2n b+32*(1+LENGTH vs*type_slot_size et) <= dimword (:256) /\
  write_place cx (StoragePlace tr k (ArrayTV et (Dynamic cap)))
    (ArrayV (DynArrayV vs)) ee = (INL (),ff) ==>
  stmt_state_rel ctx func cenv cx ff
    (store_copy_prefix (if tr then LocTransient else LocStorage) b k q
      (1+LENGTH vs*type_slot_size et))
Proof
  strip_tac >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [write_storage_place_eq, AllCaseEqs()] >> strip_tac >>
  drule stmt_state_selected_storage_agree >>
  disch_then (qspec_then `tr` assume_tac) >>
  drule_all storage_agree_dynarray_subregion_prefix >> strip_tac >>
  drule place_store_prefix_backend_natural >>
  disch_then (qspecl_then [`q`, `k`, `tr`] assume_tac) >>
  drule_all stmt_state_storage_patch >>
  once_rewrite_tac[place_store_prefix_state_patch] >>
  qpat_x_assum `_ (store_copy_prefix _ _ _ _ _) = _` mp_tac >>
  qpat_x_assum `set_storage _ _ _ _ = ff` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `tr` >> simp_tac (srw_ss()) [] >>
  rpt strip_tac >> FULL_SIMP_TAC bool_ss [ADD_COMM]
QED

Theorem place_store_normalize_state:
  stmt_state_rel ctx func cenv cx es (store_copy_normalize q t) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x q) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
    ((store_copy_normalize q t) with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `not_fresh_at sa p` by
           (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
         first_x_assum drule >> simp[store_copy_normalize_def, lookup_var_def]) >>
     conj_tac
     >- (gen_tac >> strip_tac >>
         `not_fresh_at sa p` by
           (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
         first_x_assum drule >> simp[store_copy_normalize_def, lookup_var_def]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (store_copy_normalize _ _)` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp_tac (srw_ss()) [store_copy_normalize_def, stmt_state_rel_def, state_rel_def,
    local_ptrs_rel_def, local_region_def, local_backed_def, storage_rel_def,
    transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def,
    venomMemDefsTheory.alloca_inv_def, alloca_room_def, fmp_room_def,
    immutable_alloca_sep_def, immutable_decl_sep_def, immutable_base_zero_def,
    lookup_var_def, oneline eval_operand_def, contract_storage_def, contract_transient_def,
    venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, pending_alloca_size_def] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem place_dyn_normalized_write_state:
  (loc = LocStorage \/ loc = LocTransient) /\
  place_ptr_rel cenv cx q (PlaceR p) k (SOME loc) (Type dty) /\
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
         0 < type_slot_size dtv) /\
  evaluate_type (get_tenv cx) dty = SOME (ArrayTV et (Dynamic cap)) /\
  well_formed_type_value (ArrayTV et (Dynamic cap)) /\
  value_has_type (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n b) q.vs_memory /\
  w2n b+32*(1+cap*type_slot_size et) <= dimword (:256) /\
  stmt_state_rel ctx func cenv cx ee q /\
  write_place cx p (ArrayV (DynArrayV vs)) ee = (INL (),ff) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x q) /\
  store_copy_normalize q t =
    (if loc = LocStorage then sstore else tstore) k
      (n2w (w2n (n2w (LENGTH vs):bytes32)))
      (place_dyn_prefix loc b k (type_slot_size et) (32*type_slot_size et)
        q (w2n (n2w (LENGTH vs):bytes32))) ==>
  stmt_state_rel ctx func cenv cx ff t
Proof
  strip_tac >>
  drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`) place_store_storage_region_witness >>
  disch_then (qspecl_then [`env`, `ee`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `leaf = ArrayTV et (Dynamic cap)` by metis_tac[optionTheory.SOME_11] >>
  `LENGTH vs <= cap` by fs[value_has_type_def] >>
  `type_slot_size (ArrayTV et (Dynamic cap)) = 1+cap*type_slot_size et` by
    simp[vyperValueTheory.type_slot_size_def] >>
  `mem_word_at (w2n b) q.vs_memory = n2w (LENGTH vs)` by
    (drule place_dyn_memory_header >> simp[]) >>
  `w2n k+1+cap*type_slot_size et <= dimword (:256)` by gvs[] >>
  drule_all place_dyn_storage_flat >>
  disch_then (qspec_then `tr` assume_tac) >>
  `loc = (if tr then LocTransient else LocStorage)` by
    (gvs[slot_loc_def]) >>
  `store_copy_normalize q t =
     store_copy_prefix (if tr then LocTransient else LocStorage) b k q
       (1+LENGTH vs*type_slot_size et)` by
    (Cases_on `tr` >> gvs[]) >>
  `w2n b+32*(1+LENGTH vs*type_slot_size et) <= dimword (:256)` by
    (`LENGTH vs*type_slot_size et <= cap*type_slot_size et` by
       simp[LE_MULT_RCANCEL] >> decide_tac) >>
  irule place_store_normalize_state >>
  qexistsl_tac [`q`, `sa`] >> asm_rewrite_tac[] >>
  qpat_x_assum `store_copy_normalize q t = store_copy_prefix _ _ _ _ _` SUBST1_TAC >>
  irule place_dyn_storage_write_state >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  gvs[] >>
  qexistsl_tac [`cap`, `ee`, `mid`, `n`, `path`, `subs`] >>
  asm_rewrite_tac[]
QED
