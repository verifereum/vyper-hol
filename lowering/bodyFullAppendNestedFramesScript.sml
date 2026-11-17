Theory bodyFullAppendNestedFrames
Ancestors
  placeStoreSlots placeStoreStorage accountsRelProps
  vyperStorageAccessFrame vyperStorageFootprint vyperStoragePlaceRegion
  vyperStorageWritePreservation
  vyperLookupStorage vyperEncodeDecode loweringStateRelDefs ptrDiscipline
  vyperStorageFrame vyperStorage vyperValue words pred_set list arithmetic vfmState

Theorem append_key_fold_cases[local]:
  !f m (ks:num list) X q b.
    (q,b) IN FOLDL (\Y j. key_update Y (f j) (m j)) X ks ==>
    ((q,b) IN X /\ (!j. MEM j ks ==> q <> f j)) \/
    (?j. MEM j ks /\ q = f j /\ b IN m j)
Proof
  rpt gen_tac >> qid_spec_tac `X` >> Induct_on `ks` >>
  simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  simp[key_update_def, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem append_child_dead_selected[local]:
  !H tr slot tv cap st j b i.
    MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
    regions_consistent (FST H) /\ i < cap /\
    w2n slot+1+i*type_slot_size tv <= j /\
    j < w2n slot+1+i*type_slot_size tv+type_slot_size tv /\
    storage_dead H tr st j b ==>
    dead_bytes st (w2n slot+1+i*type_slot_size tv) tv j b
Proof
  rpt gen_tac >> strip_tac >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)` by
    metis_tac[regions_consistent_def] >>
  `i*type_slot_size tv+type_slot_size tv <= cap*type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [storage_dead_def] >>
  disch_then (CONJUNCTS_THEN2 kall_tac strip_assume_tac) >>
  rename1 `dead_bytes st (w2n other) otv j b` >>
  Cases_on `(other,otv) = (slot,ArrayTV tv (Dynamic cap))`
  >- (gvs[] >> drule dyn_array_elem_dead >>
      disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  drule (cj 1 dead_bytes_range) >> strip_tac >>
  `ranges_disjoint (w2n other) (type_slot_size otv)
    (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))` by
    (first_x_assum irule >> metis_tac[pairTheory.PAIR_EQ]) >>
  gvs[ranges_disjoint_def, type_slot_size_def]
QED

Theorem append_child_dead_storage[local]:
  !H tr slot tv cap i st j b.
    MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    i < cap /\ dead_bytes st (w2n slot+1+i*type_slot_size tv) tv j b ==>
    storage_dead H tr st j b
Proof
  rpt gen_tac >> strip_tac >>
  `dead_bytes st (w2n slot) (ArrayTV tv (Dynamic cap)) j b` by
    (simp_tac (srw_ss()) [Once dead_bytes_def] >>
     qexists_tac `i` >> simp[]) >>
  drule (cj 1 dead_bytes_range) >> strip_tac >>
  simp_tac (srw_ss()) [storage_dead_def] >>
  conj_tac
  >- (Cases_on `tr` >> simp[] >> strip_tac >>
      qpat_x_assum `storage_locks_separated _ _`
        (mp_tac o REWRITE_RULE [storage_locks_separated_def]) >>
      disch_then (drule_then drule) >> simp[ranges_disjoint_def]) >>
  qexistsl_tac [`slot`, `ArrayTV tv (Dynamic cap)`] >> simp[] >>
  gvs[regions_consistent_def] >> metis_tac[pairTheory.PAIR_EQ]
QED

Theorem append_sparse_keys_dead_subset:
  !H tr slot tv cap len k v writes off M X ks st.
    MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
    len = w2n (lookup_storage slot st) /\ len < cap /\
    k = slot+n2w (1+len*type_slot_size tv) /\
    encode_value tv v = SOME writes /\
    (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
    X SUBSET {(q,b) | storage_dead H tr st (w2n q) b} /\
    (!j b. j < type_slot_size tv /\ b < 32 /\ MEM j (MAP FST writes) /\
      ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b
      ==> off+32*j+b NOTIN M) ==>
    key_update
      (FOLDL (\Y j. key_update Y (k+n2w j) (mem_word_taint M (off+32*j))) X ks)
      slot {} SUBSET
    {(q,b) | storage_dead H tr
      (update_storage slot (n2w (len+1)) (apply_writes k writes st)) (w2n q) b}
Proof
  rpt gen_tac >> strip_tac >>
  `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256)` by
    metis_tac[regions_consistent_def] >>
  `w2n k = w2n slot+1+len*type_slot_size tv /\
   w2n k+type_slot_size tv <= dimword (:256)` by
    metis_tac[dynamic_array_child_region_bounds] >>
  `!i. MEM i (MAP FST writes) ==> i < type_slot_size tv` by
    metis_tac[cj 1 encode_writes_bounded] >>
  `!i. i < type_slot_size tv ==> w2n (k+n2w i) = w2n k+i` by
    (rpt strip_tac >>
     `i < dimword (:256) /\ w2n k+i < dimword (:256)` by decide_tac >>
     simp_tac std_ss [word_add_def, w2n_n2w] >> metis_tac[LESS_MOD]) >>
  `!raw h. storage_dead H tr (update_storage slot h raw) = storage_dead H tr raw` by
    suspend "header" >>
  simp_tac (srw_ss()) [SUBSET_DEF, pairTheory.FORALL_PROD, Once key_update_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!raw h. _` (fn th => rewrite_tac[th]) >>
  rename1 `storage_dead H tr (apply_writes k writes st) (w2n q) b` >>
  qspecl_then [`\j. k+n2w j`, `\j. mem_word_taint M (off+32*j)`]
    (drule o BETA_RULE) append_key_fold_cases >> strip_tac
  >- suspend "retained"
  >> suspend "written"
QED

Resume append_sparse_keys_dead_subset[header]:
  rpt gen_tac >> irule storage_dead_update_in_region >>
  goal_assum (drule_at (Pat `MEM (_,_,_) (FST _)`)) >>
  simp_tac (srw_ss()) [type_slot_size_def] >> strip_tac >>
  (conj_tac >- simp[]) >> rpt gen_tac >>
  `!i. i < cap ==>
    (dead_bytes (update_storage slot h raw)
       (w2n slot+1+i*type_slot_size tv) tv j b <=>
     dead_bytes raw (w2n slot+1+i*type_slot_size tv) tv j b)` by
    (rpt strip_tac >> irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     rename1 `w2n slot+1+i*type_slot_size tv <= idx` >>
     `i*type_slot_size tv+type_slot_size tv <= cap*type_slot_size tv` by
       (irule array_index_element_end_bound >> simp[]) >>
     `idx < dimword (:256)` by
       (qpat_x_assum `w2n slot + type_slot_size (ArrayTV _ _) <= _` mp_tac >>
        simp_tac (srw_ss()) [type_slot_size_def] >> decide_tac) >>
     `n2w idx <> slot` by
       (strip_tac >> `idx = w2n slot` by metis_tac[w2n_n2w, LESS_MOD] >>
        decide_tac) >>
     simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]) >>
  pure_rewrite_tac[dead_bytes_def] >> metis_tac[]
QED
Resume append_sparse_keys_dead_subset[retained]:
  `storage_dead H tr st (w2n q) b` by
    (qpat_x_assum `X SUBSET _` mp_tac >>
     simp_tac (srw_ss()) [SUBSET_DEF, pairTheory.FORALL_PROD] >>
     disch_then drule >> simp[]) >>
  Cases_on `w2n k <= w2n q /\ w2n q < w2n k+type_slot_size tv`
  >- suspend "retained_inside" >>
  irule place_store_storage_dead_subregion_frame >>
  goal_assum (drule_at (Pat `MEM (_,_,_) (FST _)`)) >>
  qexistsl_tac [`1+len*type_slot_size tv`, `tv`,
    `[ValueSubscript (IntV (&len))]`, `st`] >>
  simp_tac (srw_ss()) [storage_subregion_def] >>
  conj_tac
  >- (rpt strip_tac >> irule apply_writes_word_frame >> rpt strip_tac >>
      rename1 `MEM j (MAP FST writes)` >>
      `j < type_slot_size tv` by metis_tac[] >>
      `w2n (k+n2w j) = w2n k+j` by metis_tac[] >>
      qpat_x_assum `_ = k+n2w j` SUBST_ALL_TAC >> decide_tac) >>
  metis_tac[ADD_ASSOC]

QED
Resume append_sparse_keys_dead_subset[written]:
  `MEM j (MAP FST writes) /\ j < type_slot_size tv` by metis_tac[] >>
  `b < 32 /\ off+32*j+b IN M` by
    (qpat_x_assum `_ IN mem_word_taint _ _` mp_tac >>
     simp_tac (srw_ss()) [mem_word_taint_def]) >>
  `dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b` by
    metis_tac[] >>
  `w2n q = w2n k+j` by metis_tac[] >>
  irule append_child_dead_storage >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `MEM (_,_,_) (FST _)`)) >>
  qexists_tac `len` >>
  qpat_assum `w2n k = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  metis_tac[]
QED
Resume append_sparse_keys_dead_subset[retained_inside]:
  qabbrev_tac `d = w2n q-w2n k` >>
  `d < type_slot_size tv /\ w2n q = w2n k+d` by
    (simp_tac (srw_ss()) [Abbr `d`] >> decide_tac) >>
  `q = k+n2w d` by metis_tac[w2n_11] >>
  `~MEM d (MAP FST writes)` by metis_tac[] >>
  `dead_bytes st (w2n k) tv (w2n q) b` by
    (qpat_assum `w2n k = _` (fn th => pure_rewrite_tac[th]) >>
     irule append_child_dead_selected >>
     (conj_tac >- decide_tac) >> (conj_tac >- decide_tac) >>
     goal_assum (drule_at (Pat `MEM (_,_,_) (FST _)`)) >>
     metis_tac[]) >>
  `b < 32` by metis_tac[cj 1 dead_bytes_range] >>
  `dead_bytes (apply_writes k writes st) (w2n k) tv (w2n q) b` by
    (spose_not_then assume_tac >>
     drule place_store_unwritten_live_preserved >>
     disch_then (qspecl_then [`st`, `w2n k`, `d`, `b`] mp_tac) >>
     simp_tac (srw_ss()) [n2w_w2n] >> metis_tac[]) >>
  irule append_child_dead_storage >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `MEM (_,_,_) (FST _)`)) >>
  qexists_tac `len` >>
  qpat_assum `w2n k = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  metis_tac[]
QED
Finalise append_sparse_keys_dead_subset
