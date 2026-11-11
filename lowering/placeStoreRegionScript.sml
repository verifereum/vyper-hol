Theory placeStoreRegion
Ancestors
  storageSubregionLive loweringPosts exprSimHypsDefs
  vyperStoragePlaceProvenance vyperStorageLayoutSafety vyperStoragePlaceRegion
Libs
  wordsLib

Theorem place_store_storage_region_witness:
  (loc = LocStorage \/ loc = LocTransient) /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
         0 < type_slot_size dtv) ==>
  ?tr leaf mid n subs root tv path off.
    p = StoragePlace tr w leaf /\ loc = slot_loc tr /\
    evaluate_type (get_tenv cx) dty = SOME leaf /\
    declared_storage_region cx mid n subs = SOME (tr,root,tv) /\
    storage_subregion tv path off leaf /\
    w2n root + type_slot_size tv <= dimword (:256) /\
    w2n w = w2n root + off /\
    w2n w + type_slot_size leaf <= dimword (:256) /\
    (!mid' n' subs' root' tv'.
      declared_storage_region cx mid' n' subs' = SOME (tr,root',tv') /\
      (root',tv') <> (root,tv) ==>
      ranges_disjoint (w2n root) (type_slot_size tv)
                      (w2n root') (type_slot_size tv'))
Proof
  Cases_on `p` >> pure_rewrite_tac[place_ptr_rel_def] >>
  rpt strip_tac >> gvs[] >>
  `storage_layout_safe cx` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     simp_tac pure_ss [expr_sim_inv_def] >> rpt strip_tac >> asm_rewrite_tac []) >>
  gvs[storage_place_region_def] >>
  drule_all storage_layout_safe_region_nonoverflow >> strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root + delta < dimword (:256)` by decide_tac >>
  `w2n (root + n2w delta) = w2n root + delta` by
    (`root + n2w delta = n2w (w2n root + delta)` by
       simp[GSYM wordsTheory.word_add_n2w] >> simp[] >>
     gvs[wordsTheory.dimword_def]) >>
  qexistsl_tac [`mid`,`var_name`,`keys`,`root`,`tv`,`path`,`delta`] >>
  gvs[wordsTheory.dimword_def] >>
  rpt strip_tac >>
  irule storage_layout_safe_region_separation >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`mid`,`var_name`,`keys`] >> simp[] >>
  rpt strip_tac >> gvs[]
QED
