(* Full-layout storage copying at a capacity subregion. *)
Theory placeStorageFixedSemantic
Ancestors
  placeStorageDynamicAgreement stmtSimAssignStorageCopy bodyMemAssignTopCopyPaths
  bodyMemAssignTopCopySem storageCopyLive placeStorageSubregionLive
  accountsRelProps vyperStoragePlaceRegion valueEncodingProps words arithmetic
  compileEnv vyperStorage vyperTyping venomState list rich_list stmtSimStoreCopy

Theorem storage_fixed_subregion_agree[local]:
  declared_storage_region cx mid name subs = SOME (tr,k,root) /\
  storage_subregion root path delta tv /\ w2n d = w2n k+delta /\
  w2n k+type_slot_size root <= dimword(:256) /\
  (!mid' name' subs' k' root'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
    (k',root') <> (k,root) ==>
    ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\ val_in_memory tv v off mem /\
  storage_agree (storage_dead cx tr st1) st1 st2 ==>
  storage_agree (storage_dead cx tr (apply_writes d writes st1))
    (apply_writes d writes st1)
    (FOLDL (\a i. update_storage (d+n2w i) (mem_word_at (off+32*i) mem) a)
      st2 (COUNT_LIST (type_slot_size tv)))
Proof
  strip_tac >> drule storage_subregion_bounds >> strip_tac >>
  `w2n d+type_slot_size tv <= dimword(:256)` by decide_tac >>
  pure_rewrite_tac[storage_agree_def] >> rpt gen_tac >> strip_tac >>
  rename1 `~storage_dead cx tr (apply_writes d writes st1) (w2n q) b` >>
  `lookup_storage q (FOLDL (\a i. update_storage (d+n2w i)
    (mem_word_at (off+32*i) mem) a) st2 (COUNT_LIST (type_slot_size tv))) =
    if w2n d <= w2n q /\ w2n q < w2n d+type_slot_size tv then
      mem_word_at (off+32*(w2n q-w2n d)) mem else lookup_storage q st2` by
    (ho_match_mp_tac copy_fold_region >> simp[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `w2n d <= w2n q /\ w2n q < w2n d+type_slot_size tv`
  >- suspend "inside" >> suspend "outside"
QED
Resume storage_fixed_subregion_agree[inside]:
  `~dead_bytes (apply_writes d writes st1) (w2n d) tv (w2n q) b` by
    (strip_tac >> qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >> simp[] >>
     pure_rewrite_tac[storage_dead_def] >>
     qexistsl_tac [`mid`, `name`, `subs`, `k`, `root`] >> simp[] >>
     conj_tac >- gvs[] >> drule storage_subregion_dead_leaf >>
     disch_then (qspecl_then [`apply_writes d writes st1`, `w2n k`, `w2n q`, `b`] mp_tac) >>
     simp[] >> metis_tac[ADD_COMM]) >>
  `w2n d+(w2n q-w2n d) = w2n q /\ w2n q-w2n d < type_slot_size tv` by decide_tac >>
  simp[] >> drule encode_value_memory_live >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`d`, `st1`, `w2n q-w2n d`, `b`] mp_tac) >> gvs[]
QED
Resume storage_fixed_subregion_agree[outside]:
  `!a. a < dimword(:256) /\
    (a < w2n d \/ w2n d+type_slot_size tv <= a) ==>
    lookup_storage (n2w a) (apply_writes d writes st1) = lookup_storage (n2w a) st1` by
    (gen_tac >> disch_tac >> irule copy_encoded_outside >>
     conj_tac >- gvs[] >> qexistsl_tac [`tv`, `v`] >> simp[] >> decide_tac) >>
  `~storage_dead cx tr st1 (w2n q) b` by
    (strip_tac >> qpat_x_assum `~storage_dead _ _ (apply_writes _ _ _) _ _` mp_tac >> simp[] >>
     irule (INST_TYPE [alpha |-> ``:256``] storage_subregion_dead_outside) >>
     qexistsl_tac [`d`, `delta`, `k`, `tv`, `mid`, `name`,
       `path`, `root`, `st1`, `subs`] >> simp[] >> gvs[]) >>
  `lookup_storage q (apply_writes d writes st1) = lookup_storage q st1` by
    (first_x_assum (qspec_then `w2n q` mp_tac) >> simp[w2n_lt] >> decide_tac) >>
  simp[] >> qpat_x_assum `storage_agree _ _ _` mp_tac >> simp[storage_agree_def]
QED
Finalise storage_fixed_subregion_agree

Theorem storage_fixed_subregion_state:
  stmt_state_rel ctx fn ce cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,k,root) /\
  storage_subregion root path delta tv /\ w2n d = w2n k+delta /\
  w2n k+type_slot_size root <= dimword(:256) /\
  (!mid' name' subs' k' root'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
    (k',root') <> (k,root) ==>
    ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  val_in_memory tv v (w2n p) s.vs_memory /\
  w2n p+type_memory_size tv <= dimword(:256) ==>
  stmt_state_rel ctx fn ce cx
    (set_storage cx es tr (apply_writes d writes (get_storage cx es tr)))
    (store_copy_prefix (if tr then LocTransient else LocStorage) p d s (type_slot_size tv))
Proof
  strip_tac >>
  `!i. i < type_slot_size tv ==>
    mload (w2n (p+n2w i*32w)) s = mem_word_at (w2n p+32*i) s.vs_memory` by
    (rpt strip_tac >>
     `w2n p+32*i < dimword(:256)` by
       (fs[type_memory_size_slots] >> decide_tac) >>
     `(p+n2w i*32w:256 word) = p+n2w (32*i)` by
       simp_tac bool_ss [word_mul_n2w, MULT_COMM] >>
     asm_rewrite_tac[] >> simp[w2n_add_2, mem_word_at_eq_mload]) >>
  `store_copy_prefix (if tr then LocTransient else LocStorage) p d s (type_slot_size tv) =
    FOLDL (\a i. (if tr then tstore else sstore) (d+n2w i)
      (mem_word_at (w2n p+32*i) s.vs_memory) a) s (COUNT_LIST (type_slot_size tv))` by
    (simp[store_copy_prefix_def] >>
     irule FOLDL_CONG >> simp[MEM_COUNT_LIST] >> rpt strip_tac >>
     Cases_on `tr` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  ho_match_mp_tac storage_copy_state_fold >> simp[] >>
  drule topcopy_initial_agree >> disch_then (qspec_then `tr` assume_tac) >>
  drule_all storage_fixed_subregion_agree >> simp[]
QED
