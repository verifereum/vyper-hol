(* Declared-root provenance for a successful storage-place assignment. *)
Theory placeStorageWriteProvenance
Ancestors
  bodyMemAssignTopCopySem exprSimHypsDefs placeStore loweringPosts compileEnv
  vyperStoragePlaceProvenance vyperStoragePlaceRegion vyperStorageLayoutSafety
  vyperPlaceStoragePreservation vyperInterpreter vyperState vyperStorageBackend

Theorem place_storage_write_provenance:
  expr_sim_inv ce cx env ee /\ storage_place_region cx p /\
  place_ptr_rel ce cx s (PlaceR p) w
    (SOME (if tr then LocTransient else LocStorage)) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  0 < type_slot_size dtv /\ value_has_type dtv v /\ write_place cx p v ee = (INL (),ff) ==>
  ?mid name subs k root path delta writes.
    declared_storage_region cx mid name subs = SOME (tr,k,root) /\
    storage_subregion root path delta dtv /\
    w2n w = w2n k + delta /\
    w2n k + type_slot_size root <= dimword(:256) /\
    (!mid' name' subs' k' root'.
      declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
      (k',root') <> (k,root) ==>
      ranges_disjoint (w2n k) (type_slot_size root)
        (w2n k') (type_slot_size root')) /\
    encode_value dtv v = SOME writes /\
    ff = set_storage cx ee tr
      (apply_writes w writes (get_storage cx ee tr))
Proof
  strip_tac >> Cases_on `p` >>
  gvs[place_ptr_rel_def, slot_loc_def]
  >~ [`write_place cx (MemoryPlace _ _) _ _ = _`]
  >- (Cases_on `tr` >> gvs[]) >>
  `b = tr` by (Cases_on `b` >> Cases_on `tr` >> gvs[]) >> gvs[] >>
  `storage_layout_safe cx` by fs[expr_sim_inv_def] >>
  drule_all storage_place_region_numeric >> strip_tac >>
  `~cx.txn.is_static` by
    (Cases_on `cx.txn.is_static` >>
     fs[write_place_def, write_storage_slot_def, check_not_static_def,
        vyperStateTheory.bind_def, ignore_bind_def, assert_def, check_def,
        raise_def, vyperStateTheory.return_def]) >>
  drule_all topcopy_typed_storage_write >>
  disch_then (qspecl_then [`b`, `c`, `ee`] strip_assume_tac) >>
  gvs[write_place_def] >>
  qexistsl [`mid`, `name`, `keys`, `root`, `tv`, `path`, `delta`] >>
  simp[] >> rpt strip_tac >>
  `(mid,name,keys) <> (mid',name',subs')` by (strip_tac >> gvs[]) >>
  drule_all storage_layout_safe_region_separation >> simp[]
QED
