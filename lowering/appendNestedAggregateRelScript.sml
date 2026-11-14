(* Sparse aggregate Append at a resolved storage subregion. *)
Theory appendNestedAggregateRel
Ancestors
  appendStorageAggregateRel stmtSimStoreCopyState
  placeStoreStorage accountsRelProps vyperStoragePlaceRegion
  loweringStateRelDefs vyperStorage vyperStorageBackend vyperValue vfmState words combin


Theorem append_nested_aggregate_copy_success_post:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sb /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  (!mid' name' subs' k' tv'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
    (k',tv') <> (rootk,root) ==>
    ranges_disjoint (w2n rootk) (type_slot_size root)
                    (w2n k') (type_slot_size tv')) /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\ val_in_memory tv v (w2n b) s.vs_memory /\
  w2n b + 32 * type_slot_size tv <= dimword (:256) /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  store_copy_normalize s u =
    (if tr then tstore else sstore) slot (n2w (len+1))
      (FOLDL (\t i. (if tr then tstore else sstore)
        (slot+n2w (1+len*type_slot_size tv)+n2w i)
        (mem_word_at (w2n b+32*i) s.vs_memory) t) s ks) /\
  (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') ==>
  res = INL () /\ stmt_state_rel ctx func cenv cx es' u
Proof
  strip_tac >>
  drule_all stmt_state_rel_append_nested_storage_aggregate >> strip_tac >>
  conj_tac >- simp[] >>
  irule place_store_normalize_state >>
  qexistsl_tac [`s`, `sb`] >> simp[] >> gvs[]
QED
