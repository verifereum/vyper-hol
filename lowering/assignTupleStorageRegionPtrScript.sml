(* Declared-region metadata for a successfully evaluated storage target. *)
Theory assignTupleStorageRegionPtr
Ancestors
  exprSimHypsDefs vyperStoragePlaceProvenance vyperPlaceStoragePreservation
  vyperStorageLayoutSafety vyperStoragePlaceRegion vyperState arithmetic words

Theorem tuple_target_storage_region_ptr:
  expr_sim_inv cenv cx env es /\
  eval_target_place cx bt es = (INL (StoragePlace tr slot tv),ee) /\
  0 < type_slot_size tv ==>
  ?mid id subs root rtv path delta.
    declared_storage_region cx mid id subs = SOME (tr,root,rtv) /\
    storage_subregion rtv path delta tv /\
    w2n slot = w2n root + delta /\
    w2n root + type_slot_size rtv <= dimword (:256) /\
    w2n slot + type_slot_size tv <= dimword (:256) /\
    (!mid' id' subs' root' rtv'.
      declared_storage_region cx mid' id' subs' = SOME (tr,root',rtv') /\
      (root',rtv') <> (root,rtv) ==>
      ranges_disjoint (w2n root) (type_slot_size rtv)
        (w2n root') (type_slot_size rtv'))
Proof
  strip_tac >>
  `storage_layout_safe cx` by
    (first_assum (fn th =>
       FIRST (map ACCEPT_TAC (CONJUNCTS (REWRITE_RULE [expr_sim_inv_def] th))))) >>
  drule eval_target_place_region >> strip_tac >>
  drule_all storage_place_region_numeric >>
  disch_then (qx_choosel_then [`mid`,`id`,`subs`,`root`,`rtv`,`path`,`delta`]
    strip_assume_tac) >>
  qexistsl_tac [`mid`,`id`,`subs`,`root`,`rtv`,`path`,`delta`] >>
  asm_rewrite_tac[] >> conj_tac >- decide_tac >>
  rpt gen_tac >> strip_tac >>
  `((mid,id,subs) <> (mid',id',subs'))` by (CCONTR_TAC >> gvs[]) >>
  irule storage_layout_safe_region_separation >>
  metis_tac[]
QED
