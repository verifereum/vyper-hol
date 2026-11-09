(*
 * place_store_value_run (placeStore) at a slot in storage or transient
 * storage, of a type other than a DynArray: a word by one SSTORE or
 * TSTORE; an aggregate laid out at the place's type in memory (through a
 * fresh buffer when the value's type differs and is not a bytestring),
 * then copied word by word to the slots (one MLOAD and store for at most
 * 32 bytes).
 *
 * TOP-LEVEL: place_store_value_storage_run
 *)

Theory placeStoreStorage
Ancestors
  stmtSimDefs exprSimHypsDefs typedCopyDomain vyperStoragePlaceProvenance
  loweringPosts fragGasMode accountsRelProps copyExecution stmtSimStoreCopy placeStoreCopyChunk
  stmtLowering exprLowering compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  venomState fragGasSeq fragGasPath arithmetic venomExecSemantics venomInst exprLoweringProps

Theorem place_store_dead_tuple_component:
  !types i elem st base j b.
    oEL i types = SOME elem /\
    dead_bytes st (base + tuple_prefix_slot_size i types) elem j b ==>
    dead_bytes st base (TupleTV types) j b
Proof
  Induct >> Cases_on `i` >>
  simp[listTheory.oEL_def, tuple_prefix_slot_size_def, dead_bytes_def] >>
  rpt strip_tac >> disj2_tac >>
  gvs[dead_bytes_def] >> first_x_assum irule >>
  qexistsl_tac [`elem`, `n`] >> asm_rewrite_tac[GSYM ADD_ASSOC]
QED

Theorem place_store_dead_struct_component:
  !fields id delta elem st base j b.
    struct_field_slot fields id = SOME (delta,elem) /\
    dead_bytes st (base + delta) elem j b ==>
    dead_bytes st base (StructTV fields) j b
Proof
  Induct >> simp[struct_field_slot_def, dead_bytes_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[struct_field_slot_def] >>
  IF_CASES_TAC >> simp[] >> rpt strip_tac >>
  gvs[AllCaseEqs(), dead_bytes_def] >>
  PairCases_on `z` >> gvs[] >>
  disj2_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  `base' + type_slot_size r + z0 = base' + (z0 + type_slot_size r)` by
    decide_tac >> asm_rewrite_tac[]
QED

Theorem place_store_dead_subregion:
  !root path delta leaf.
    storage_subregion root path delta leaf ==>
    !base st j b. dead_bytes st (base + delta) leaf j b ==>
      dead_bytes st base root j b
Proof
  ho_match_mp_tac vyperStoragePlaceRegionTheory.storage_subregion_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  rpt strip_tac >> gvs[]
  >- suspend "fixed"
  >- suspend "dynamic"
  >- suspend "struct"
  >> suspend "tuple"
QED

Resume place_store_dead_subregion[fixed]:
  simp[dead_bytes_def] >> qexists_tac `Num i` >> simp[] >>
  first_x_assum drule >> disch_then irule >>
  `base' + Num i * type_slot_size root + rest =
   base' + (rest + Num i * type_slot_size root)` by decide_tac >>
  asm_rewrite_tac[]
QED

Resume place_store_dead_subregion[dynamic]:
  `dead_bytes st (base' + 1 + Num i * type_slot_size root) root j b` by
    (first_x_assum drule >> disch_then irule >>
     `base' + 1 + Num i * type_slot_size root + rest =
      base' + (rest + (Num i * type_slot_size root + 1))` by decide_tac >>
     asm_rewrite_tac[]) >>
  simp[dead_bytes_def] >> qexists_tac `Num i` >> simp[] >>
  IF_CASES_TAC
  >- (`base' + (Num i * type_slot_size root + 1) =
       base' + 1 + Num i * type_slot_size root` by decide_tac >>
      asm_rewrite_tac[]) >>
  drule (cj 1 dead_bytes_range) >> strip_tac >> simp[] >> decide_tac
QED

Resume place_store_dead_subregion[struct]:
  irule place_store_dead_struct_component >>
  goal_assum (drule_at (Pat `struct_field_slot _ _ = _`)) >>
  first_x_assum drule >> disch_then irule >>
  asm_rewrite_tac[GSYM ADD_ASSOC]
QED

Resume place_store_dead_subregion[tuple]:
  irule place_store_dead_tuple_component >>
  goal_assum (drule_at Any) >>
  first_x_assum drule >> disch_then irule >>
  `base' + tuple_prefix_slot_size (Num i) types + rest =
   base' + (rest + tuple_prefix_slot_size (Num i) types)` by decide_tac >>
  asm_rewrite_tac[]
QED

Finalise place_store_dead_subregion

Theorem place_store_dead_tuple_frame:
  !types i elem base lo len st st'.
    oEL i types = SOME elem /\
    base + tuple_prefix_slot_size i types <= lo /\
    lo + len <= base + tuple_prefix_slot_size i types + type_slot_size elem /\
    base + type_slot_size (TupleTV types) <= dimword (:256) /\
    (!q. ~(lo <= w2n q /\ w2n q < lo + len) ==>
         lookup_storage q st' = lookup_storage q st) /\
    (!j b. ~(lo <= j /\ j < lo + len) /\
       dead_bytes st (base + tuple_prefix_slot_size i types) elem j b ==>
       dead_bytes st' (base + tuple_prefix_slot_size i types) elem j b) ==>
    !j b. ~(lo <= j /\ j < lo + len) /\
      dead_bytes st base (TupleTV types) j b ==>
      dead_bytes st' base (TupleTV types) j b
Proof
  Induct >- simp[listTheory.oEL_def] >>
  gen_tac >> Cases_on `i`
  >- (simp[listTheory.oEL_def, tuple_prefix_slot_size_def,
           type_slot_size_def, dead_bytes_def] >>
      rpt strip_tac >> gvs[] >> disj2_tac >>
      `dead_bytes_list st' (base' + type_slot_size h) types j b =
       dead_bytes_list st (base' + type_slot_size h) types j b` by
        (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
         first_x_assum irule >>
         `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
         simp[wordsTheory.w2n_n2w] >> decide_tac) >>
      asm_rewrite_tac[]) >>
  simp[listTheory.oEL_def, tuple_prefix_slot_size_def,
       type_slot_size_def, dead_bytes_def] >>
  rpt strip_tac >> gvs[] >>
  (Cases_on `dead_bytes st base' h j b`
  >- (disj1_tac >>
      `dead_bytes st' base' h j b = dead_bytes st base' h j b` by
        (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
         first_x_assum irule >>
         `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
         simp[wordsTheory.w2n_n2w] >> decide_tac) >>
      asm_rewrite_tac[]) >>
  gvs[] >> disj2_tac >>
  first_x_assum (drule_at (Pat `oEL _ _ = _`)) >>
  disch_then (qspec_then `base' + type_slot_size h` mp_tac) >>
  simp[GSYM ADD_ASSOC, type_slot_size_def, dead_bytes_def] >>
  disch_then irule >> goal_assum (drule_at Any) >>
  qexistsl_tac [`len`, `lo`] >> simp[] >> metis_tac[])
QED

Theorem place_store_dead_struct_frame:
  !fields id off elem base lo len st st'.
    struct_field_slot fields id = SOME (off,elem) /\
    base + off <= lo /\ lo + len <= base + off + type_slot_size elem /\
    base + type_slot_size (StructTV fields) <= dimword (:256) /\
    (!q. ~(lo <= w2n q /\ w2n q < lo + len) ==>
         lookup_storage q st' = lookup_storage q st) /\
    (!j b. ~(lo <= j /\ j < lo + len) /\
       dead_bytes st (base + off) elem j b ==>
       dead_bytes st' (base + off) elem j b) ==>
    !j b. ~(lo <= j /\ j < lo + len) /\
      dead_bytes st base (StructTV fields) j b ==>
      dead_bytes st' base (StructTV fields) j b
Proof
  Induct >- simp[struct_field_slot_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `h0 = id`
  >- (simp[struct_field_slot_def, type_slot_size_def, dead_bytes_def] >>
      rpt strip_tac >> gvs[] >> disj2_tac >>
      `dead_bytes_fields st' (base' + type_slot_size elem) fields j b =
       dead_bytes_fields st (base' + type_slot_size elem) fields j b` by
        (irule (cj 3 dead_bytes_frame) >> rpt strip_tac >>
         first_x_assum irule >>
         `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
         simp[wordsTheory.w2n_n2w] >> decide_tac) >>
      asm_rewrite_tac[]) >>
  simp[struct_field_slot_def, type_slot_size_def, dead_bytes_def,
       AllCaseEqs()] >>
  rpt strip_tac >> PairCases_on `z` >> gvs[] >>
  (Cases_on `dead_bytes st base' h1 j b`
   >- (disj1_tac >>
       `dead_bytes st' base' h1 j b = dead_bytes st base' h1 j b` by
         (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
          first_x_assum irule >>
          `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
          simp[wordsTheory.w2n_n2w] >> decide_tac) >>
       asm_rewrite_tac[]) >>
   gvs[] >> disj2_tac >>
   first_x_assum (drule_at (Pat `struct_field_slot _ _ = _`)) >>
   disch_then (qspec_then `base' + type_slot_size h1` mp_tac) >>
   simp[GSYM ADD_ASSOC, type_slot_size_def, dead_bytes_def] >>
   disch_then irule >> goal_assum (drule_at Any) >>
   qexistsl_tac [`len`, `lo`] >> simp[] >> metis_tac[])
QED

Theorem place_store_dead_subregion_frame:
  !root path delta leaf.
    storage_subregion root path delta leaf ==>
    !base st st' j b.
    0 < type_slot_size leaf /\
    (!q. ~(base+delta <= w2n q /\
           w2n q < base+delta+type_slot_size leaf) ==>
         lookup_storage q st' = lookup_storage q st) /\
    ~(base+delta <= j /\ j < base+delta+type_slot_size leaf) /\
    base + type_slot_size root <= dimword (:256) /\
    dead_bytes st base root j b ==>
    dead_bytes st' base root j b
Proof
  ho_match_mp_tac vyperStoragePlaceRegionTheory.storage_subregion_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp_tac (srw_ss())
    [Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  strip_tac >> rpt (first_x_assum SUBST_ALL_TAC) >>
  rpt gen_tac >> disch_tac >>
  all_tac
  >- (gvs[] >> drule (cj 1 dead_bytes_range) >> decide_tac)
  >- suspend "fixed"
  >- suspend "dynamic"
  >- suspend "struct"
  >> suspend "tuple"
QED

Resume place_store_dead_subregion_frame[struct]:
  qpat_x_assum `?delta' elem rest. _` strip_assume_tac >>
  qpat_x_assum `delta = _` SUBST_ALL_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rule_assum_tac (REWRITE_RULE [GSYM ADD_ASSOC]) >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  (irule place_store_dead_struct_frame >>
   conj_tac >- (simp_tac (srw_ss()) [wordsTheory.dimword_def, ADD_ASSOC] >>
     first_assum (ACCEPT_TAC o SRULE [wordsTheory.dimword_def, ADD_ASSOC])) >>
   goal_assum (drule_at (Pat `struct_field_slot _ _ = _`)) >>
   goal_assum (drule_at (Pat `dead_bytes _ _ _ _ _`)) >>
   qexistsl_tac [`type_slot_size leaf`, `base' + delta' + rest`] >>
   simp_tac (srw_ss()) [GSYM ADD_ASSOC] >>
   conj_tac >- (simp_tac (srw_ss()) [wordsTheory.dimword_def, ADD_ASSOC] >>
     first_assum (ACCEPT_TAC o SRULE [wordsTheory.dimword_def, ADD_ASSOC])) >>
   conj_tac
   >- (rpt gen_tac >> strip_tac >>
       first_x_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
       disch_then irule >>
       drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >>
       strip_tac >> simp[GSYM ADD_ASSOC] >>
       qexists_tac `st` >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
   decide_tac)
QED
Resume place_store_dead_subregion_frame[tuple]:
  qpat_x_assum `_ /\ ?elem rest. _` strip_assume_tac >>
  qpat_x_assum `delta = _` SUBST_ALL_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rule_assum_tac (REWRITE_RULE [GSYM ADD_ASSOC]) >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  (irule place_store_dead_tuple_frame >>
   conj_tac >- (simp_tac (srw_ss()) [wordsTheory.dimword_def, ADD_ASSOC] >>
     first_assum (ACCEPT_TAC o SRULE [wordsTheory.dimword_def, ADD_ASSOC])) >>
   goal_assum (drule_at (Pat `oEL _ _ = _`)) >>
   goal_assum (drule_at (Pat `dead_bytes _ _ _ _ _`)) >>
   qexistsl_tac [`type_slot_size leaf`,
     `base' + tuple_prefix_slot_size (Num i) types + rest`] >>
   simp_tac (srw_ss()) [GSYM ADD_ASSOC] >>
   conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
   conj_tac
   >- (rpt gen_tac >> strip_tac >>
       first_x_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
       disch_then irule >>
       drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >>
       strip_tac >> simp[GSYM ADD_ASSOC] >>
       qexists_tac `st` >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
   decide_tac)
QED
Resume place_store_dead_subregion_frame[fixed]:
  gvs[] >> rpt strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  qpat_x_assum `base' + type_slot_size (ArrayTV _ _) <= _` mp_tac >>
  simp_tac (srw_ss()) [Once type_slot_size_def] >> disch_tac >>
  qpat_x_assum `dead_bytes st base' (ArrayTV _ _) j b` mp_tac >>
  simp_tac (srw_ss()) [Once dead_bytes_def] >> strip_tac >>
  pure_once_rewrite_tac [dead_bytes_def] >>
  rename1 `dead_bytes st (base' + k * type_slot_size root) root j b` >>
  (qexists_tac `k` >> (conj_tac >- first_assum ACCEPT_TAC) >>
  `k * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  Cases_on `k = Num i`
  >- (qpat_x_assum `k = Num i` SUBST_ALL_TAC >>
      first_x_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
      disch_then irule >> simp[GSYM ADD_ASSOC] >>
      qexists_tac `st` >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  `dead_bytes st' (base' + k * type_slot_size root) root j b =
   dead_bytes st (base' + k * type_slot_size root) root j b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >>
     rename1 `base' + k * type_slot_size root <= idx` >>
     `idx < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
     simp[wordsTheory.w2n_n2w] >>
     Cases_on `k < Num i`
     >- (`k * type_slot_size root + type_slot_size root <= Num i * type_slot_size root` by
           (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
         decide_tac) >>
     `Num i * type_slot_size root + type_slot_size root <= k * type_slot_size root` by
       (irule vyperLookupStorageTheory.array_index_element_end_bound >> decide_tac) >>
     decide_tac) >>
  asm_rewrite_tac[])
QED
Resume place_store_dead_subregion_frame[dynamic]:
  gvs[] >> rpt strip_tac >>
  qpat_x_assum `!delta. storage_subregion _ _ _ _ ==> _` (mk_asm "ih") >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `lookup_storage (n2w base') st' = lookup_storage (n2w base') st` by
    (first_x_assum irule >>
     `base' < dimword (:256)` by
       (gvs[type_slot_size_def] >> decide_tac) >>
     simp[wordsTheory.w2n_n2w]) >>
  qpat_x_assum `base' + type_slot_size (ArrayTV _ _) <= _` mp_tac >>
  simp_tac (srw_ss()) [type_slot_size_def] >> disch_tac >>
  qpat_x_assum `dead_bytes st base' (ArrayTV _ _) j b` mp_tac >>
  simp_tac (srw_ss()) [Once dead_bytes_def] >> strip_tac >>
  pure_once_rewrite_tac [dead_bytes_def] >>
  rename1 `k < n` >>
  (qexists_tac `k` >> simp[] >>
   Cases_on `k < w2n (lookup_storage (n2w base') st)`
   >- (gvs[] >>
       `k * type_slot_size root + type_slot_size root <= n * type_slot_size root` by
         (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
       Cases_on `k = Num i`
       >- (gvs[] >>
           asm_x "ih" (drule_at (Pat `storage_subregion _ _ _ _`)) >>
           disch_then irule >> simp[GSYM ADD_ASSOC] >>
           qexists_tac `st` >> asm_rewrite_tac[]) >>
       `dead_bytes st' (base' + (k * type_slot_size root + 1)) root j b =
        dead_bytes st (base' + (k * type_slot_size root + 1)) root j b` by
         (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
          first_x_assum irule >>
          rename1 `base' + (k * type_slot_size root + 1) <= idx` >>
          `idx < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
          simp[wordsTheory.w2n_n2w] >>
          Cases_on `k < Num i`
          >- (`k * type_slot_size root + type_slot_size root <= Num i * type_slot_size root` by
                (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
              decide_tac) >>
          `Num i * type_slot_size root + type_slot_size root <= k * type_slot_size root` by
            (irule vyperLookupStorageTheory.array_index_element_end_bound >> decide_tac) >>
          decide_tac) >>
       asm_rewrite_tac[]) >>
   gvs[])
QED
Finalise place_store_dead_subregion_frame

Theorem place_store_storage_dead_subregion_frame:
  !cx tr mid name subs rootk root path delta leaf st st' j b.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta leaf /\
    0 < type_slot_size leaf /\
    (!q. ~(w2n rootk + delta <= w2n q /\
           w2n q < w2n rootk + delta + type_slot_size leaf) ==>
         lookup_storage q st' = lookup_storage q st) /\
    ~(w2n rootk + delta <= j /\
      j < w2n rootk + delta + type_slot_size leaf) /\
    storage_dead cx tr st j b ==>
    storage_dead cx tr st' j b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [storage_dead_def] >> strip_tac >>
  `dead_bytes st' (w2n slot) tv j b` suffices_by
    (rpt strip_tac >> simp_tac (srw_ss()) [storage_dead_def] >>
     goal_assum (drule_at (Pat `dead_bytes _ _ _ _ _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  Cases_on `(slot,tv) = (rootk,root)`
  >- (gvs[] >>
      (irule place_store_dead_subregion_frame >>
       conj_tac >- (fs[wordsTheory.dimword_def] >> decide_tac) >>
       goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
       qexists_tac `st` >> gvs[AC ADD_ASSOC ADD_COMM] >> metis_tac[])) >>
  `ranges_disjoint (w2n slot) (type_slot_size tv)
       (w2n rootk) (type_slot_size root)` by
    (first_x_assum irule >> conj_tac
     >- (goal_assum (drule_at Any)) >> gvs[] >> metis_tac[]) >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `dead_bytes st' (w2n slot) tv j b = dead_bytes st (w2n slot) tv j b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >>
     `i < dimword (:256)` by (fs[wordsTheory.dimword_def] >> decide_tac) >>
     simp[wordsTheory.w2n_n2w] >>
     gvs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
  asm_rewrite_tac[]
QED

Theorem place_store_subregion_agree:
  !cx tr mid name subs rootk root path delta leaf k st1 st2 st1' st2'.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta leaf /\
    w2n k = w2n rootk + delta /\ 0 < type_slot_size leaf /\
    w2n rootk + type_slot_size root <= dimword (:256) /\
    (!mid' name' subs' k' tv'.
       declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (rootk,root) ==>
       ranges_disjoint (w2n rootk) (type_slot_size root)
                       (w2n k') (type_slot_size tv')) /\
    (!q. ~(w2n k <= w2n q /\ w2n q < w2n k + type_slot_size leaf) ==>
       lookup_storage q st1' = lookup_storage q st1 /\
       lookup_storage q st2' = lookup_storage q st2) /\
    (!i b. i < type_slot_size leaf /\ b < 32 /\
       ~dead_bytes st1' (w2n k) leaf (w2n k+i) b ==>
       EL b (word_to_bytes (lookup_storage (k+n2w i) st1') T) =
       EL b (word_to_bytes (lookup_storage (k+n2w i) st2') T)) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr st1') st1' st2'
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac (srw_ss()) [storage_agree_def] >> rpt gen_tac >> strip_tac >>
  rename1 `~storage_dead cx tr st1' (w2n q) b` >>
  Cases_on `w2n k <= w2n q /\ w2n q < w2n k + type_slot_size leaf`
  >- suspend "inside"
  >> suspend "outside"
QED
Resume place_store_subregion_agree[inside]:
  qpat_x_assum `w2n rootk + type_slot_size root <= _`
    (assume_tac o SRULE [wordsTheory.dimword_def, ADD_COMM]) >>
  `~dead_bytes st1' (w2n k) leaf (w2n q) b` by
    (strip_tac >>
     `dead_bytes st1' (w2n rootk) root (w2n q) b` by
       (drule place_store_dead_subregion >>
        disch_then (qspec_then `w2n rootk` mp_tac) >>
        asm_rewrite_tac[] >> metis_tac[]) >>
     qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >>
     simp_tac (srw_ss()) [storage_dead_def] >>
     qexistsl_tac [`mid`, `name`, `subs`, `rootk`, `root`] >>
     simp[wordsTheory.dimword_def] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     metis_tac[]) >>
  `k + n2w (w2n q - w2n k) = q` by
    (qpat_x_assum `w2n k = _` kall_tac >>
     `w2n q - w2n k < dimword (:256)` by
       (qspec_then `q` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
     `w2n k + (w2n q - w2n k) = w2n q` by decide_tac >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w]) >>
  first_x_assum (qspecl_then [`w2n q - w2n k`, `b`] mp_tac) >>
  simp[] >> gvs[ADD_COMM]
QED
Resume place_store_subregion_agree[outside]:
  `~storage_dead cx tr st1 (w2n q) b` by
    (strip_tac >>
     `storage_dead cx tr st1' (w2n q) b` suffices_by metis_tac[] >>
     irule place_store_storage_dead_subregion_frame >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     qexists_tac `st1` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  simp_tac (srw_ss()) [storage_agree_def] >>
  disch_then (qspecl_then [`q`, `b`] mp_tac) >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED
Finalise place_store_subregion_agree

Theorem place_store_updates_lookup:
  !xs a st.
    lookup_storage a
      (FOLDL (\st kv. update_storage (FST kv) (SND kv) st) st xs) =
    case FILTER (\kv. FST kv = a) (REVERSE xs) of
      [] => lookup_storage a st
    | kv::rest => SND kv
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[listTheory.FILTER_APPEND_DISTRIB] >>
  Cases_on `FILTER (\kv. FST kv = a) (REVERSE xs)` >>
  simp[] >> Cases_on `h` >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `q = a` >> simp[]
QED

Theorem place_store_updates_miss:
  !xs a st.
    ~MEM a (MAP FST xs) ==>
    lookup_storage a
      (FOLDL (\st kv. update_storage (FST kv) (SND kv) st) st xs) =
    lookup_storage a st
Proof
  rpt strip_tac >> rewrite_tac[place_store_updates_lookup] >>
  `FILTER (\kv. FST kv = a) (REVERSE xs) = []` by
    (simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM,
          listTheory.MEM_REVERSE] >>
     gvs[listTheory.MEM_MAP] >> metis_tac[]) >>
  simp[]
QED

Theorem place_store_updates_hit:
  !xs a w st.
    MEM (a,w) xs /\
    (!kv. MEM kv xs /\ FST kv = a ==> SND kv = w) ==>
    lookup_storage a
      (FOLDL (\st kv. update_storage (FST kv) (SND kv) st) st xs) = w
Proof
  rpt strip_tac >> rewrite_tac[place_store_updates_lookup] >>
  Cases_on `FILTER (\kv. FST kv = a) (REVERSE xs)`
  >- (gvs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM,
          listTheory.MEM_REVERSE] >>
      first_x_assum (qspec_then `(a,w)` mp_tac) >> simp[]) >>
  simp[] >> first_x_assum irule >>
  `MEM h (FILTER (\kv. FST kv = a) (REVERSE xs))` by simp[] >>
  gvs[listTheory.MEM_FILTER, listTheory.MEM_REVERSE]
QED

Theorem place_store_apply_writes_fold:
  !writes k st.
    apply_writes k writes st =
    FOLDL (\st kv. update_storage (FST kv) (SND kv) st) st
      (MAP (\(off,v). (k + n2w off,v)) writes)
Proof
  Induct >> simp[vyperStorageTheory.apply_writes_def] >>
  Cases_on `h` >> simp[vyperStorageTheory.apply_writes_def,
    GSYM wordsTheory.word_add_n2w, ADD_COMM]
QED

Theorem place_store_bytes_live_bound:
  !l src_cap dst_cap st base i b.
    l <= src_cap /\ src_cap <= dst_cap /\
    w2n (lookup_storage (n2w base) st) = l /\
    i < 1 + word_size dst_cap /\ b < 32 /\
    ~dyn_bytes_dead st base dst_cap (base+i) b ==>
    i < 1 + word_size src_cap
Proof
  rpt gen_tac >> strip_tac >> Cases_on `i = 0` >- simp[] >>
  gvs[dyn_bytes_dead_def, vfmConstantsTheory.word_size_def] >>
  spose_not_then assume_tac >>
  `(src_cap + 31) DIV 32 < i` by decide_tac >>
  gvs[arithmeticTheory.DIV_LT_X] >> decide_tac
QED

Theorem place_store_apply_writes_header:
  !writes k st w.
    MEM (0,w) writes /\
    (!off v. MEM (off,v) writes ==> off < dimword (:256) /\
      (off = 0 ==> v = w)) ==>
    lookup_storage k (apply_writes k writes st) = w
Proof
  rpt strip_tac >> rewrite_tac[place_store_apply_writes_fold] >>
  irule place_store_updates_hit >>
  simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  reverse conj_tac >- (qexists_tac `0` >> simp[wordsTheory.WORD_ADD_0]) >>
  Cases >> simp[] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  `n2w p_1 = (0w:bytes32)` by
    (metis_tac[wordsTheory.WORD_EQ_ADD_LCANCEL, wordsTheory.WORD_ADD_0]) >>
  gvs[wordsTheory.n2w_11]
QED

Theorem place_store_dyn_bytes_header:
  !cap bs writes k st.
    encode_dyn_bytes_slots cap bs = SOME writes /\
    w2n k + 1 + word_size cap <= dimword (:256) ==>
    lookup_storage k (apply_writes k writes st) = n2w (LENGTH bs)
Proof
  rpt gen_tac >> strip_tac >>
  `value_has_type (BaseTV (BytesT (Dynamic cap))) (BytesV bs)` by
    (gvs[vyperStorageTheory.encode_dyn_bytes_slots_def,
         vyperTypingTheory.value_has_type_def, AllCaseEqs()]) >>
  `encode_value (BaseTV (BytesT (Dynamic cap))) (BytesV bs) = SOME writes` by
    simp[vyperStorageTheory.encode_value_def] >>
  irule place_store_apply_writes_header >> reverse conj_tac
  >- (gvs[vyperStorageTheory.encode_dyn_bytes_slots_def, AllCaseEqs()]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`MEM off (MAP FST writes)` by
        (simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      drule_all (cj 1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
      simp[vyperValueTheory.type_slot_size_def] >> strip_tac >>
      gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
      decide_tac) >>
  strip_tac >> gvs[vyperStorageTheory.encode_dyn_bytes_slots_def,
    AllCaseEqs(), indexedListsTheory.MEM_MAPi] >> gvs[]
QED

(* Both dynamic bytes and strings use encode_dyn_bytes_slots; keeping
   the coverage boundary here avoids duplicating the identical arithmetic. *)
Theorem place_store_dyn_bytes_live_bound:
  !src_cap dst_cap bs writes k st i b.
    LENGTH bs <= src_cap /\ src_cap <= dst_cap /\
    encode_dyn_bytes_slots dst_cap bs = SOME writes /\
    w2n k + 1 + word_size dst_cap <= dimword (:256) /\
    i < 1 + word_size dst_cap /\ b < 32 /\
    ~dyn_bytes_dead (apply_writes k writes st) (w2n k) dst_cap (w2n k+i) b ==>
    i < 1 + word_size src_cap
Proof
  rpt strip_tac >>
  drule_all place_store_dyn_bytes_header >> strip_tac >>
  irule place_store_bytes_live_bound >>
  goal_assum (drule_at (Pat `~dyn_bytes_dead _ _ _ _ _`)) >>
  qexists_tac `w2n (n2w (LENGTH bs) : bytes32)` >>
  simp[wordsTheory.w2n_n2w] >>
  `LENGTH bs MOD dimword (:256) <= LENGTH bs` by
    simp[arithmeticTheory.MOD_LESS_EQ] >>
  gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac
QED

Theorem place_store_bytestring_live_copy:
  !tv v off mem k writes st src_cap dst_cap i b.
    (tv = BaseTV (BytesT (Dynamic dst_cap)) \/ tv = BaseTV (StringT dst_cap)) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v off mem /\
    (case v of BytesV bs => LENGTH bs <= src_cap
             | StringV s => LENGTH s <= src_cap | _ => F) /\
    src_cap <= dst_cap /\ encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+i) b ==>
    i < 1 + word_size src_cap /\
    EL b (word_to_bytes
      (lookup_storage (n2w (w2n k+i)) (apply_writes k writes st)) T) =
    EL b (word_to_bytes (mem_word_at (off+32*i) mem) T)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (qpat_x_assum `tv = _ \/ tv = _` strip_assume_tac >> gvs[] >>
      Cases_on `v` >>
      gvs[vyperTypingTheory.value_has_type_def,
          vyperStorageTheory.encode_value_def, dead_bytes_def,
          vyperValueTheory.type_slot_size_def] >>
      gvs[wordsTheory.dimword_def, AC ADD_ASSOC ADD_COMM] >>
      irule (SRULE [wordsTheory.dimword_def, AC ADD_ASSOC ADD_COMM]
        place_store_dyn_bytes_live_bound) >>
      goal_assum (drule_at (Pat `encode_dyn_bytes_slots _ _ = _`)) >>
      goal_assum (drule_at (Pat `~dyn_bytes_dead _ _ _ _ _`)) >> simp[]) >>
  drule_all storageCopyLiveTheory.encode_value_memory_live >> simp[]
QED

Theorem place_store_encoded_copy_agree:
  !cx tr mid name subs rootk root path delta tv base writes v n read_word st1 st2.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta tv /\
    base = w2n rootk + delta /\ 0 < type_slot_size tv /\
    w2n rootk + type_slot_size root <= dimword (:256) /\
    (!mid' name' subs' k' tv'.
       declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (rootk,root) ==>
       ranges_disjoint (w2n rootk) (type_slot_size root)
                       (w2n k') (type_slot_size tv')) /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    base + type_slot_size tv <= dimword (:256) /\
    n <= type_slot_size tv /\
    (!i b. i < type_slot_size tv /\ b < 32 /\
       ~dead_bytes (apply_writes (n2w base) writes st1) base tv (base+i) b ==>
       i < n /\
       EL b (word_to_bytes (lookup_storage (n2w (base+i))
         (apply_writes (n2w base) writes st1)) T) =
       EL b (word_to_bytes (read_word i) T)) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr (apply_writes (n2w base) writes st1))
      (apply_writes (n2w base) writes st1)
      (FOLDL (\st i. update_storage (n2w (base+i)) (read_word i) st)
        st2 (COUNT_LIST n))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `apply_writes (n2w start) writes st1` >>
  `start < dimword (:256)` by decide_tac >>
  irule place_store_subregion_agree >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qexists_tac `(n2w start):bytes32` >>
  goal_assum (drule_at (Pat `storage_agree _ _ _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  `w2n ((n2w start):bytes32) = start` by simp[wordsTheory.w2n_n2w] >>
  qpat_x_assum `start = _` (mk_asm "origin") >>
  simp[wordsTheory.w2n_n2w, GSYM wordsTheory.word_add_n2w] >>
  conj_tac >- suspend "frame" >> suspend "live"
QED
Resume place_store_encoded_copy_agree[frame]:
  gen_tac >> disch_tac >> conj_tac
  >- (rewrite_tac[place_store_apply_writes_fold] >>
      irule place_store_updates_miss >>
      simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP,
           pairTheory.EXISTS_PROD] >>
      rpt strip_tac >>
      rename1 `MEM (off,word) writes` >>
      `off < type_slot_size tv` by
        (irule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
         goal_assum (drule_at (Pat `encode_value _ _ = _`)) >>
         simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
      `start + off < dimword (:256)` by decide_tac >>
      gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  rename1 `FOLDL (\st i. update_storage (n2w start + n2w i) (rd i) st) st2 (COUNT_LIST n)` >>
  `~MEM q (MAP FST (MAP (\i. ((n2w start + n2w i):bytes32,rd i))
       (COUNT_LIST n)))` by
    (simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MEM_MAP,
          rich_listTheory.MEM_COUNT_LIST] >>
     rpt strip_tac >>
     `start + i < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >> decide_tac) >>
  drule place_store_updates_miss >>
  disch_then (qspec_then `st2` mp_tac) >> simp[rich_listTheory.FOLDL_MAP]
QED
Resume place_store_encoded_copy_agree[live]:
  reverse conj_tac >- (asm "origin" mp_tac >> simp[ADD_COMM]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `FOLDL (\st j. update_storage (n2w start + n2w j) (rd j) st) st2 (COUNT_LIST n)` >>
  `i < n /\
   EL b (word_to_bytes (lookup_storage (n2w (start+i))
     (apply_writes (n2w start) writes st1)) T) =
   EL b (word_to_bytes (rd i) T)` by
    (first_x_assum irule >> simp[ADD_COMM]) >>
  `lookup_storage (n2w start + n2w i)
     (FOLDL (\st j. update_storage (n2w start + n2w j) (rd j) st)
       st2 (COUNT_LIST n)) = rd i` suffices_by
    gvs[GSYM wordsTheory.word_add_n2w] >>
  `MEM ((n2w start + n2w i):bytes32,rd i)
     (MAP (\j. (n2w start + n2w j,rd j)) (COUNT_LIST n))` by
    (simp[listTheory.MEM_MAP, rich_listTheory.MEM_COUNT_LIST] >>
     qexists_tac `i` >> simp[]) >>
  drule place_store_updates_hit >>
  disch_then (qspec_then `st2` mp_tac) >>
  simp[rich_listTheory.FOLDL_MAP, listTheory.MEM_MAP,
       rich_listTheory.MEM_COUNT_LIST] >>
  impl_tac >- (rpt strip_tac >> gvs[] >>
    `i < dimword (:256)` by decide_tac >>
    `j < dimword (:256)` by decide_tac >>
    gvs[wordsTheory.n2w_11]) >> simp[]
QED
Finalise place_store_encoded_copy_agree

Theorem place_store_alloc_buffer_path:
  !func cenv cx es sa sm buf sz s ctx.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    fn_has_code sa sm func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t w. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\
      sa.cs_next_id < sm.cs_next_id /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes t name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
      ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      (FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,sz) \/
       (FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
        w2n w = s.vs_alloca_next))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `emitted_insts sa sm = [inst] /\
   sm.cs_current_bb = sa.cs_current_bb /\
   sm.cs_current_insts = sa.cs_current_insts ++ [inst]` by
    suspend "layout" >>
  `step_inst_base inst s = OK u /\
   ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   u.vs_labels = s.vs_labels` by
    suspend "execution" >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    suspend "path" >>
  `FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,sz) \/
   (FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
    w2n w = s.vs_alloca_next)` suffices_by
    (disch_tac >>
     qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`, `w`] >>
     suspend "transport") >>
  suspend "address"
QED
Resume place_store_alloc_buffer_path[layout]:
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  gvs[Abbr `inst`] >>
  gvs[emitHelperTheory.emit_op_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED
Resume place_store_alloc_buffer_path[execution]:
  `step_inst_base inst s = OK u` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def] >> Cases_on `step_inst_base inst s` >> simp[]) >>
  simp[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Abbr `inst`, step_inst_base_def, mk_inst_def,
       exec_alloca_def, eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (strip_tac >> gvs[update_var_def]) >>
  PairCases_on `x` >> strip_tac >> gvs[update_var_def]
QED
Resume place_store_alloc_buffer_path[path]:
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_edge ctx func s 0
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `get_instruction _ _ = _`) tuple_straight_line_edge >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     disch_then (qspecl_then [`func`, `ctx`] mp_tac) >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  simp[gas_marked_path_def] >>
  metis_tac[gas_path_rules, gas_path_edge_normal, ADD_0]
QED
Resume place_store_alloc_buffer_path[address]:
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[Abbr `inst`, step_inst_base_def, mk_inst_def,
           exec_alloca_def, eval_operand_def] >> strip_tac >>
      gvs[update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  disj1_tac >>
  qpat_x_assum `!aid entry. _` drule >>
  gvs[]
QED
Resume place_store_alloc_buffer_path[transport]:
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       eval_operand_def, lookup_var_def, local_region_def] >>
  metis_tac[eval_operand_def, lookup_var_def, local_region_def]
QED
Finalise place_store_alloc_buffer_path

Theorem place_store_alloc_source_disjoint:
  !s sa w sz src len.
    (FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,sz) \/
     (FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
      w2n w = s.vs_alloca_next)) /\
    src + len <= s.vs_alloca_next /\
    (!aid b size. FLOOKUP s.vs_allocas aid = SOME (b,size) /\
       sa.cs_next_id <= aid ==> src + len <= b \/ b + size <= src) ==>
    regions_disjoint src len (w2n w) sz
Proof
  rpt gen_tac >> strip_tac >>
  simp[regions_disjoint_def] >> metis_tac[LESS_EQ_REFL, ADD_COMM]
QED

(* C1.1.n DESIGN ONLY: counted recursive interface (not an assertion).
   Proposed entry predicate E cenv ctx dty sty dtv stv v is the following
   universally quantified contract. For ALL dst src sa sb func s dw sw,
     compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
     (!x. dst = Var x ==> not_fresh_at sa x) /\
     (!x. src = Var x ==> not_fresh_at sa x) /\
     eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
     val_in_memory stv v (w2n sw) s.vs_memory /\
     w2n sw + type_memory_size stv < dimword (:256) /\
     w2n dw + type_memory_size dtv < dimword (:256) /\
     regions_disjoint (w2n sw) (type_memory_size stv)
                      (w2n dw) (type_memory_size dtv) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
     s.vs_inst_idx = LENGTH sa.cs_current_insts
   implies EXISTS t,
     gas_marked_path F ctx func s 0 (OK t) /\
     val_in_memory dtv v (w2n dw) t.vs_memory /\
     typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts.
   The rank theorem should have EXACTLY the hypotheses of typed_copy_rank_entry
   and conclusion E instead of typed_copy_entry. No continuation-to-path
   implication is assumed. The checked word boundary below is stronger than
   this entry's word instance (no source freshness, bounds or disjointness).

   Array consumer, slow path: set N = LENGTH values, hs = hd = 0 for fixed
   arrays and hs = hd = 32 for dynamic arrays. ss,ds are evaluated element
   memory sizes, equal to compiler element sizes. At the cond block entry
   (index 0), invariant I(i,q), relative to original s, is:
     i <= N /\ lookup_var counter q = SOME (n2w i) /\ ~q.vs_halted /\
     q.vs_current_bb = cond_lbl /\ q.vs_inst_idx = 0 /\
     gas_marked_path F ctx func s 0 (OK q) /\
     val_in_memory stv v (w2n sw) q.vs_memory /\
     (!j. j < i ==> val_in_memory detv (EL j values)
          (w2n dw + hd + j*ds) q.vs_memory) /\
     typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s q.
   Also retain base/length operands at their original values and all loop
   temporaries allocated before the child compiler state; these variables
   are not_fresh_at child_sa, NOT necessarily not_fresh_at outer sa.
   Fixed typing gives N=count. Dynamic typing gives N<=source_cap<=dest_cap
   and N<dimword; MLOAD/GT/ISZERO/ASSERT must be executed and MSTORE establishes
   the destination length header, retained by each child frame. Zero length
   exits without a child call. Child addresses are sw+hs+i*ss, dw+hd+i*ds;
   full-region bounds prove no word wrap, and disjoint full regions imply
   disjoint child regions. Rank(element)<rank(array) supplies E for EL i.
   At child entry use its actual compiler block/index, not the body label:
   the address prefix has already advanced the index. Child E returns its
   own exit block/index, which may differ after nested loops. Execute the
   increment/ASSIGN/JMP suffix from THAT exit, re-enter cond_lbl at index 0.
   Compose prefix, child and suffix zero-count paths using path transitivity;
   finite induction on N-i justifies repetition, not an unbounded back-edge
   rule. At i=N execute LT/ISZERO/JNZ to exit_lbl, index 0, then match sb.
   Frame composition and child disjointness preserve earlier elements and
   source memory; reassemble val_in_memory only at exit. Fast fixed copy
   and dynamic copy need separate actual counted MCOPY/loop boundaries;
   the above invariant does not certify those dispatch branches.

   Sequential fields consumer: zip destination/source types, evaluated types
   and values (structs select source type by ALOOKUP name as in the compiler).
   At field k retain original base operands, source val_in_memory, the full
   outer state frame and val_in_memory for each destination field j<k at
   dw+SUM(previous destination sizes). Source offset is SUM(previous selected
   source sizes), including the struct compiler's traversal order. Distinct
   names, metadata consistency and existing field-layout lemmas must justify
   this selection/order, not an assumed identity of source/destination sizes.
   Execute both compile_with_byte_offset prefixes, apply E for that field's
   smaller rank with its actual child_sa/child_sb, then compose with the tail
   list induction at updated offsets. Child frames preserve original bases
   and preceding fields; whole-region disjointness preserves source values.
   Empty lists use the reflexive zero path at the unchanged compiler endpoint.
   Missing source fields must be ruled out by typing before taking a child.
   No arrays/fields/bytes fast-path proof is claimed by this design artifact.
*)
Theorem place_store_typed_word_path:
  !cenv ctx func tenv dst dty src sty sa sb stv dtv v sw dw s.
    compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
    is_word_type dty /\ type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typedMemoryCopyTheory.typed_copy_word_widening >> strip_tac >> gvs[] >>
  `type_memory_size dtv = 32` by suspend "size" >>
  `mem_word_at (w2n sw) s.vs_memory = typed_val_to_w256 dtv v` by
    metis_tac[entryDecodePropsTheory.val_in_memory_word] >>
  drule_all typedMemoryCopyTheory.typed_copy_word_run_seq >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ _ = OK u` >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by suspend "prefix" >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    suspend "no_gas" >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    suspend "path" >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "post"
QED
Resume place_store_typed_word_path[size]:
  qpat_x_assum `is_word_type dty` mp_tac >>
  qpat_x_assum `evaluate_type tenv dty = SOME dtv` mp_tac >>
  Cases_on `dty` >> simp[is_word_type_def]
  >~ [`FlagT`]
  >- (rw[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      gvs[valueEncodingTheory.type_memory_size_def]) >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, evaluate_type_def, valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >> gvs[valueEncodingTheory.type_memory_size_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, evaluate_type_def, valueEncodingTheory.type_memory_size_def, AllCaseEqs()]
QED
Resume place_store_typed_word_path[prefix]:
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  qexists_tac `l` >> rewrite_tac[]
QED
Resume place_store_typed_word_path[no_gas]:
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def] >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >>
  gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]
QED
Resume place_store_typed_word_path[path]:
  drule_at (Pat `run_inst_seq _ _ = _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[gas_marked_path_def]
QED
Resume place_store_typed_word_path[post]:
  `typedMemoryCopy$typed_copy_state_frame sa (w2n dw) 32 s
     (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    simp[Abbr `u`, typedMemoryCopyTheory.typed_copy_word_state_frame] >>
  `val_in_memory dtv v (w2n dw) u.vs_memory` by
    (drule_all entryDecodePropsTheory.val_in_memory_word >>
     disch_then (fn th => rewrite_tac[th]) >>
     simp[Abbr `u`, valueEncodingPropsTheory.mstore_mem_word_at_same,
          GSYM valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `u`, mstore_def, update_var_def] >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def, same_blocks_def] >>
  metis_tac[]
QED
Finalise place_store_typed_word_path

(* Lift a GAS-free emitted prefix without exposing continuation semantics. *)
Theorem place_store_emitted_seq_path:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0 /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fragExecTheory.fn_has_code_def, same_blocks_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sb)
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     qpat_x_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                     rich_listTheory.DROP_LENGTH_APPEND] >>
     qexists_tac `l` >> rewrite_tac[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[gas_marked_path_def]
QED

Theorem place_store_emit_op_path:
  emit_op opc args sa = (op,sb) /\ fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc args [out]) s =
    OK (update_var out w s)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var)) w s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sa` >>
     simp[mk_inst_def, run_inst_seq_def] >>
     gvs[mk_inst_def, run_inst_seq_def]) >>
  qexists_tac `(update_var (STRING #"%" (toString sa.cs_next_var)) w s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var, update_var_def] >>
  simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
       typedMemoryCopyTheory.typed_copy_frame_def, venom_state_component_equality,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >> simp[]
QED

Theorem place_store_copy_dynamic_path:
  compile_copy_memory_dynamic dst src len sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand len s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK ((mcopy (w2n d) (w2n a) (w2n w) s)
          with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >>
  drule_all typedMemoryCopyTheory.typed_copy_dynamic_run_seq >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `compile_copy_memory_dynamic _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_copy_memory_dynamic_def,
          emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
          emit_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[] >> simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
                   mk_inst_def]) >>
  conj_tac >- (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sa` >> gvs[]) >>
  gvs[same_blocks_def]
QED

Theorem place_store_copy_fixed_path:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  n < dimword (:256) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK ((if n = 0 then s else mcopy (w2n d) (w2n a) n s)
          with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb
Proof
  Cases_on `n = 0`
  >- (simp[contextTheory.compile_copy_memory_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venom_state_component_equality] >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules]) >>
  Cases_on `n` >> gvs[contextTheory.compile_copy_memory_def] >> strip_tac >>
  `SUC n' < dimword (:256)` by
    gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  drule_all valueCopyTheory.emit_mcopy_run >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
          emit_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     gvs[] >> simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
                   mk_inst_def]) >>
  conj_tac >- (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `sa` >> gvs[]) >>
  gvs[same_blocks_def]
QED

Theorem place_store_offset_path:
  compile_with_byte_offset ptr0 off sa = (op,sb) /\
  eval_operand ptr0 s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand op t = SOME (w + n2w off) /\
      t.vs_memory = s.vs_memory /\
      (!dst len. typedMemoryCopy$typed_copy_state_frame sa dst len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[contextTheory.compile_with_byte_offset_def, comp_return_def] >>
      qexists_tac `s` >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules,
           wordsTheory.WORD_ADD_0,
           typedMemoryCopyTheory.typed_copy_state_frame_def,
           venom_state_component_equality,
           typedMemoryCopyTheory.typed_copy_frame_def]) >>
  drule_all typedMemoryCopyTheory.typed_copy_offset_run_seq >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ _ = OK u` >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_with_byte_offset_def] >>
     simp[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def,
          emit_def, comp_ignore_bind_def, emitHelperTheory.emit_inst_def, fresh_id_def,
          comp_return_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]) >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >>
     qexists_tac `sa` >> gvs[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "post"
QED
Resume place_store_offset_path[post]:
  simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, same_blocks_def] >>
  conj_tac
  >- (simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
           venom_state_component_equality,
           typedMemoryCopyTheory.typed_copy_frame_def,
           lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by
        (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >> simp[]) >>
  gvs[same_blocks_def]
QED
Finalise place_store_offset_path

Theorem place_store_bytestring_path:
  compile_store_bytestring src dst sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME d /\
  mem_word_at (w2n a) s.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory tv v (w2n a) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= type_memory_size tv /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n d) (type_memory_size tv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all valueCopyTheory.store_bytestring_run_exact >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    suspend "no_gas" >>
  `gas_marked_path F ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >>
     qexists_tac `sa` >> gvs[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  suspend "post"
QED
Resume place_store_bytestring_path[no_gas]:
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[contextTheory.compile_store_bytestring_def,
       contextTheory.compile_bytestring_copy_len_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]
QED
Resume place_store_bytestring_path[post]:
  `val_in_memory tv v (w2n d) t.vs_memory` by
    (asm_rewrite_tac[] >> irule valueCopyTheory.mcopy_val_in_memory >> simp[]) >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `typedMemoryCopy$typed_copy_state_frame sa (w2n d) (type_memory_size tv) s
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     conj_tac
     >- (qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     conj_tac
     >- (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
     simp[typedMemoryCopyTheory.typed_copy_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >>
         decide_tac) >>
     simp[mcopy_def, immutableMemoryFrameTheory.immutable_write_memory_capacity,
          MAX_DEF]) >>
  gvs[same_blocks_def] >> metis_tac[]
QED
Finalise place_store_bytestring_path

Theorem place_store_branch_path:
  emit_inst opc args [] sa = ((),sb) /\
  is_terminator opc /\ opc <> INVOKE /\ opc <> GAS /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc args []) s = OK (jump_to lbl s) ==>
  gas_marked_path F ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst sa.cs_next_id opc args []]` by
    (gvs[emitHelperTheory.emit_inst_def, comp_bind_def, fresh_id_def,
         emit_def, comp_ignore_bind_def, comp_return_def]) >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
     SOME (mk_inst sa.cs_next_id opc args [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_edge ctx func s 0 (OK (jump_to lbl s))` by
    (rewrite_tac[fragGasPathTheory.gas_path_edge_def] >> simp[] >>
     qexists_tac `0` >>
     simp[step_inst_non_invoke, mk_inst_def, gasCountTheory.gas_count_step_def] >>
     metis_tac[]) >>
  simp[gas_marked_path_def] >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_rules, ADD_0]
QED

Theorem place_store_runtime_header_path:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  eval_operand length s = SOME (n2w N) /\ k <= N /\ N < dimword (:256) /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand done t = SOME (if k < N then 0w else 1w) /\
      t.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame a off len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono] >>
  `fn_has_code a b func /\ fn_has_code b c func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `k < dimword (:256)` by decide_tac >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       eval_operand lt t = SOME (bool_to_word (k < N)) /\
       t.vs_memory = s.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame a off len s t) /\
       ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
       t.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure2_def, eval_operand_def, wordsTheory.w2n_n2w, LESS_MOD]) >>
  `?u. gas_marked_path F ctx func t 0 (OK u) /\
       eval_operand done u = SOME (bool_to_word (bool_to_word (k < N) = 0w)) /\
       u.vs_memory = t.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame b off len t u) /\
       ~u.vs_halted /\ u.vs_current_bb = c.cs_current_bb /\
       u.vs_inst_idx = LENGTH c.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs,
          mk_inst_def, exec_pure1_def]) >>
  qexists_tac `u` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  conj_tac >- (Cases_on `k < N` >> gvs[bool_to_word_def]) >>
  simp[] >> rpt gen_tac >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
  qexists_tac `t` >> simp[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem place_store_index_header_path:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\ ci_mono sa a /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\ N < dimword (:256) /\
  typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  eval_operand length s = SOME (n2w N) /\ fn_has_code a c func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
      eval_operand length t = SOME (n2w N) /\
      eval_operand done t = SOME (if k < N then 0w else 1w) /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >>
  `k <= N /\ lookup_var counter s = SOME (n2w k)` by
    fs[typedMemoryCopyTheory.typed_copy_index_inv_def] >>
  drule_all place_store_runtime_header_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_index_inv_preserve >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      qexistsl_tac [`a`, `0`, `0`] >> simp[]) >>
  `!x. length = Var x ==> not_fresh_at a x` by
    metis_tac[typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand]
QED

Theorem place_store_index_test_path:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] c = ((),d) /\
  ci_mono sa a /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\ N < dimword (:256) /\
  typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  eval_operand length s = SOME (n2w N) /\ fn_has_code a d func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k t /\
      eval_operand length t = SOME (n2w N) /\
      ~t.vs_halted /\ t.vs_current_bb = (if k < N then blabel else exit) /\
      t.vs_inst_idx = 0
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono, ci_mono_emit_inst, pairTheory.SND] >>
  `fn_has_code a c func /\ fn_has_code c d func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
  drule_all place_store_index_header_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func t 0
     (OK (jump_to (if k < N then blabel else exit) t))` by
    (irule place_store_branch_path >> simp[venomInstTheory.is_terminator_def] >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`[done; Label exit; Label blabel]`, `JNZ`] >>
     simp[venomInstTheory.is_terminator_def, mk_inst_def] >>
     qpat_assum `eval_operand done t = _`
       (mp_then Any mp_tac venomExecProofsTheory.step_jnz_behavior) >>
     disch_then (qspecl_then [`exit`, `blabel`, `c.cs_next_id`] mp_tac) >>
     Cases_on `k < N` >> simp[]) >>
  qexists_tac `jump_to (if k < N then blabel else exit) t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  conj_tac >- (irule typedMemoryCopyTheory.typed_copy_index_inv_jump >>
              first_assum ACCEPT_TAC) >>
  simp[jump_to_def, eval_operand_def, lookup_var_def]
QED

Theorem place_store_counted_iterate:
  !I N k q ctx func.
    (!i q. I i q ==> ~q.vs_halted) /\
    (!i q. i < N /\ I i q ==>
      ?r. gas_marked_path F ctx func q 0 (OK r) /\ I (SUC i) r) /\
    k <= N /\ I k q ==>
    ?r. gas_marked_path F ctx func q 0 (OK r) /\ I N r
Proof
  rpt gen_tac >> qid_spec_tac `q` >> measureInduct_on `N-k` >>
  rpt strip_tac >>
  Cases_on `k = N`
  >- (gvs[] >> qexists_tac `q` >>
      simp[gas_marked_path_def] >> metis_tac[fragGasPathTheory.gas_path_rules]) >>
  `k < N /\ SUC k <= N /\ N - SUC k < N - k` by decide_tac >>
  qpat_assum `!i q. i < N /\ _ ==> _`
    (qspecl_then [`k`, `q`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `!y. N - y < N - k ==> _`
    (qspec_then `SUC k` mp_tac) >> simp[] >>
  disch_then (qspec_then `r` mp_tac) >> impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rename1 `I' N final` >> qexists_tac `final` >> conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  first_assum ACCEPT_TAC
QED

(* Straight-line index arithmetic and counter updates. *)
Theorem place_store_binary_path:
  emit_op opc [lhs;rhs] a = (res,b) /\
  (opc = ADD \/ opc = MUL) /\
  eval_operand lhs s = SOME lw /\ eval_operand rhs s = SOME rw /\
  w = (if opc = ADD then lw + rw else lw * rw) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand res t = SOME w /\
      t.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame a off len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >> irule place_store_emit_op_path >> simp[] >>
  qexistsl_tac [`[lhs;rhs]`, `opc`] >>
  gvs[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs,
      mk_inst_def, exec_pure2_def]
QED

Theorem place_store_index_addresses_path:
  emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  not_fresh_at a counter /\ lookup_var counter s = SOME (n2w k) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  fn_has_code a e func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand sp t = SOME (sw + n2w (k * ss)) /\
      eval_operand dp t = SOME (dw + n2w (k * ds)) /\
      t.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame a off len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
      t.vs_inst_idx = LENGTH e.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono] >>
  `ci_mono a c /\ ci_mono a d /\ ci_mono b d /\ ci_mono b e /\ ci_mono c e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `fn_has_code a b func /\ fn_has_code b c func /\
   fn_has_code c d func /\ fn_has_code d e func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `?q1. gas_marked_path F ctx func s 0 (OK q1) /\
       eval_operand so q1 = SOME (n2w k * n2w ss) /\
       q1.vs_memory = s.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame a off len s q1) /\
       ~q1.vs_halted /\ q1.vs_current_bb = b.cs_current_bb /\
       q1.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule place_store_binary_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[eval_operand_def]) >>
  `lookup_var counter q1 = SOME (n2w k)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_counter] >>
  `?q2. gas_marked_path F ctx func q1 0 (OK q2) /\
       eval_operand doff q2 = SOME (n2w k * n2w ds) /\
       q2.vs_memory = q1.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame b off len q1 q2) /\
       ~q2.vs_halted /\ q2.vs_current_bb = c.cs_current_bb /\
       q2.vs_inst_idx = LENGTH c.cs_current_insts` by
    (irule place_store_binary_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[eval_operand_def]) >>
  `(!x. so = Var x ==> not_fresh_at b x) /\
   (!x. doff = Var x ==> not_fresh_at c x) /\
   (!x. sp = Var x ==> not_fresh_at d x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh] >>
  `eval_operand so q2 = SOME (n2w k * n2w ss) /\
   eval_operand src q2 = SOME sw /\ eval_operand dst q2 = SOME dw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand,
              typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  `?q3. gas_marked_path F ctx func q2 0 (OK q3) /\
       eval_operand sp q3 = SOME (sw + n2w (k * ss)) /\
       q3.vs_memory = q2.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame c off len q2 q3) /\
       ~q3.vs_halted /\ q3.vs_current_bb = d.cs_current_bb /\
       q3.vs_inst_idx = LENGTH d.cs_current_insts` by
    (irule place_store_binary_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[wordsTheory.word_mul_n2w]) >>
  `eval_operand doff q3 = SOME (n2w k * n2w ds) /\
   eval_operand dst q3 = SOME dw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand,
              typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  `?q4. gas_marked_path F ctx func q3 0 (OK q4) /\
       eval_operand dp q4 = SOME (dw + n2w (k * ds)) /\
       q4.vs_memory = q3.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame d off len q3 q4) /\
       ~q4.vs_halted /\ q4.vs_current_bb = e.cs_current_bb /\
       q4.vs_inst_idx = LENGTH e.cs_current_insts` by
    (irule place_store_binary_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[wordsTheory.word_mul_n2w]) >>
  qexists_tac `q4` >>
  `gas_marked_path F ctx func s 0 (OK q2) /\
   gas_marked_path F ctx func q2 0 (OK q4)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  conj_tac >- metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  simp[] >> rpt gen_tac >>
  `typedMemoryCopy$typed_copy_state_frame a off len q1 q2 /\
   typedMemoryCopy$typed_copy_state_frame a off len q2 q3 /\
   typedMemoryCopy$typed_copy_state_frame a off len q3 q4` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_mono] >>
  metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_trans]
QED
Theorem place_store_assign_path:
  emit_inst ASSIGN [op] [counter] a = ((),b) /\
  eval_operand op s = SOME w /\
  (!x. not_fresh_at sa x ==> x <> counter) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      lookup_var counter t = SOME w /\ t.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  `b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\ same_blocks a b` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emitHelperTheory.emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
          emitted_insts_def, same_blocks_def, rich_listTheory.DROP_LENGTH_APPEND] >>
     strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_inst >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK ((update_var counter w s) with vs_inst_idx := LENGTH b.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `a` >>
     simp[mk_inst_def, run_inst_seq_def, venomInstTheory.is_terminator_def,
          step_inst_base_opcode_eqs]) >>
  qexists_tac `(update_var counter w s) with vs_inst_idx := LENGTH b.cs_current_insts` >>
  simp[emitHelperPropsTheory.lookup_var_update_var, update_var_def] >>
  simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
       typedMemoryCopyTheory.typed_copy_frame_def, venom_state_component_equality,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
QED

Theorem place_store_counter_increment_path:
  emit_op ADD [Var counter; Lit 1w] a = (inc,b) /\
  emit_inst ASSIGN [inc] [counter] b = ((),c) /\
  ci_mono sa a /\ ~not_fresh_at sa counter /\ not_fresh_at a counter /\
  lookup_var counter s = SOME (n2w k) /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      lookup_var counter t = SOME (n2w (SUC k)) /\ t.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s t) /\
      ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
      t.vs_inst_idx = LENGTH c.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b` by metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono] >>
  `ci_mono b c` by
    (qspecl_then [`ASSIGN`, `[inc]`, `[counter]`, `b`] mp_tac
       exprLoweringPropsTheory.ci_mono_emit_inst >> simp[]) >>
  `fn_has_code a b func /\ fn_has_code b c func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `?u. gas_marked_path F ctx func s 0 (OK u) /\
       eval_operand inc u = SOME (n2w (SUC k)) /\
       u.vs_memory = s.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame a off len s u) /\
       ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
       u.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule place_store_binary_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[eval_operand_def, wordsTheory.word_add_n2w, ADD1]) >>
  `!x. not_fresh_at sa x ==> x <> counter` by metis_tac[] >>
  drule_all place_store_assign_path >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  simp[] >> rpt gen_tac >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
  qexists_tac `u` >> simp[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

Definition place_store_counted_entry_def:
  place_store_counted_entry cenv ctx dty sty dtv stv v <=>
    !dst src sa sb func s dw sw.
      compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
      (!x. dst = Var x ==> not_fresh_at sa x) /\
      (!x. src = Var x ==> not_fresh_at sa x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      regions_disjoint (w2n sw) (type_memory_size stv)
                       (w2n dw) (type_memory_size dtv) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?t. gas_marked_path F ctx func s 0 (OK t) /\
          val_in_memory dtv v (w2n dw) t.vs_memory /\
          typedMemoryCopy$typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
          ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts
End

Theorem place_store_counted_word_entry:
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v ==>
  place_store_counted_entry cenv ctx dty sty dtv stv v
Proof
  strip_tac >> rw[place_store_counted_entry_def] >>
  drule_all place_store_typed_word_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
       typedMemoryCopyTheory.typed_copy_frame_def] >> metis_tac[ADD_COMM]
QED

Theorem place_store_counted_entry_offset_path:
  place_store_counted_entry cenv ctx dty sty dtv stv v /\
  compile_with_byte_offset dst doff sa = (dp,s1) /\
  compile_with_byte_offset src soff s1 = (sp,s2) /\
  compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  val_in_memory stv v (w2n sw + soff) s.vs_memory /\
  w2n sw + soff + type_memory_size stv < dimword (:256) /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n sw + soff) (type_memory_size stv)
                   (w2n dw + doff) (type_memory_size dtv) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw + doff)
        (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb` by
    metis_tac[typedMemoryCopyTheory.typed_copy_offset_mono,
              cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split,
                                  cs_extends_trans]) >>
  `w2n (dw + n2w doff) = w2n dw + doff /\
   w2n (sw + n2w soff) = w2n sw + soff` by
    (conj_tac >> irule typedMemoryCopyTheory.typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. src = Var x ==> not_fresh_at s1 x) /\
   (!x. dp = Var x ==> not_fresh_at s2 x) /\
   (!x. sp = Var x ==> not_fresh_at s2 x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_offset_fresh,
              typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  qpat_assum `compile_with_byte_offset dst _ _ = _` mp_tac >>
  disch_then (mp_then Any mp_tac place_store_offset_path) >>
  disch_then (qspecl_then [`dw`, `s`, `func`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `q1` strip_assume_tac) >>
  `eval_operand src q1 = SOME sw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  qpat_assum `compile_with_byte_offset src _ _ = _` mp_tac >>
  disch_then (mp_then Any mp_tac place_store_offset_path) >>
  disch_then (qspecl_then [`sw`, `q1`, `func`, `ctx`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `q2` strip_assume_tac) >>
  `(!x. dp = Var x ==> not_fresh_at s1 x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_offset_fresh] >>
  `eval_operand dp q2 = SOME (dw + n2w doff)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  qpat_x_assum `place_store_counted_entry _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[place_store_counted_entry_def] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`func`, `q2`, `dw + n2w doff`, `sw + n2w soff`] mp_tac) >>
  (impl_tac >- metis_tac[ADD_COMM]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >>
  `gas_marked_path F ctx func s 0 (OK q2)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  `ci_mono sa s2` by (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  simp[] >> conj_tac >- metis_tac[ADD_COMM] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
  qexists_tac `q1` >> conj_tac >- metis_tac[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
  qexists_tac `s1` >> simp[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
  qexists_tac `q2` >> conj_tac >- metis_tac[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
  qexists_tac `s2` >> simp[] >> metis_tac[ADD_COMM]
QED

Theorem place_store_index_child_path:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  place_store_counted_entry cenv ctx dty sty dtv stv v /\
  not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  lookup_var counter s = SOME (n2w k) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  val_in_memory stv v (w2n sw + k * type_memory_size stv) s.vs_memory /\
  w2n sw + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
  w2n dw + k * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n sw + k * type_memory_size stv) (type_memory_size stv)
                   (w2n dw + k * type_memory_size dtv) (type_memory_size dtv) /\
  fn_has_code a z func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw + k * type_memory_size dtv) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
        (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = z.cs_current_bb /\
      t.vs_inst_idx = LENGTH z.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e z` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
              cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono a e` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `fn_has_code a e func /\ fn_has_code e z func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `w2n (sw + n2w (k * type_memory_size stv)) = w2n sw + k * type_memory_size stv /\
   w2n (dw + n2w (k * type_memory_size dtv)) = w2n dw + k * type_memory_size dtv` by
    (conj_tac >> irule typedMemoryCopyTheory.typed_copy_offset_nonwrap >> decide_tac) >>
  `(!x. sp = Var x ==> not_fresh_at e x) /\
   (!x. dp = Var x ==> not_fresh_at e x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh,
              typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  drule_all place_store_index_addresses_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `u` strip_assume_tac)) >>
  qpat_x_assum `place_store_counted_entry _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[place_store_counted_entry_def] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`func`, `u`, `dw + n2w (k * type_memory_size dtv)`,
                                        `sw + n2w (k * type_memory_size stv)`] mp_tac) >>
  (impl_tac >- metis_tac[ADD_COMM]) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  conj_tac >- metis_tac[ADD_COMM] >> simp[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
  qexists_tac `u` >> conj_tac >- metis_tac[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
  qexists_tac `e` >> simp[] >> metis_tac[ADD_COMM]
QED

Theorem place_store_index_body_path:
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b = (doff,c) /\
  emit_op ADD [src;so] c = (sp,d) /\ emit_op ADD [dst;doff] d = (dp,e) /\
  compile_store_memory_typed cenv dp dty sp sty e = ((),z) /\
  emit_op ADD [Var counter; Lit 1w] z = (inc,z1) /\
  emit_inst ASSIGN [inc] [counter] z1 = ((),endst) /\
  ci_mono sa a /\ not_fresh_at a counter /\ ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!i. i < N ==> place_store_counted_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  k < N /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  fn_has_code a endst func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC k) t /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
        (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = endst.cs_current_bb /\
      t.vs_inst_idx = LENGTH endst.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e /\ ci_mono e z /\ ci_mono z z1` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
              cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
  `ci_mono z1 endst` by
    (qspecl_then [`ASSIGN`, `[inc]`, `[counter]`, `z1`] mp_tac
       exprLoweringPropsTheory.ci_mono_emit_inst >> simp[]) >>
  `ci_mono a z /\ ci_mono sa z /\ ci_mono z endst` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `fn_has_code a z func /\ fn_has_code z endst func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `not_fresh_at z counter /\
   (!x. src = Var x ==> not_fresh_at a x) /\
   (!x. dst = Var x ==> not_fresh_at a x)` by
    (conj_tac
     >- (gvs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
     conj_tac >> metis_tac[typedMemoryCopyTheory.typed_copy_operand_fresh_mono]) >>
  `w2n sw <= w2n sw + k * type_memory_size stv /\
   w2n sw + k * type_memory_size stv + type_memory_size stv <= w2n sw + N * type_memory_size stv` by
    metis_tac[typedMemoryCopyTheory.typed_copy_array_subinterval] >>
  `w2n dw <= w2n dw + k * type_memory_size dtv /\
   w2n dw + k * type_memory_size dtv + type_memory_size dtv <= w2n dw + N * type_memory_size dtv` by
    metis_tac[typedMemoryCopyTheory.typed_copy_array_subinterval] >>
  `lookup_var counter s = SOME (n2w k) /\
   eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
   val_in_memory stv (f k) (w2n sw + k * type_memory_size stv) s.vs_memory` by
    gvs[typedMemoryCopyTheory.typed_copy_index_inv_def] >>
  `place_store_counted_entry cenv ctx dty sty dtv stv (f k)` by metis_tac[] >>
  `?u. gas_marked_path F ctx func s 0 (OK u) /\
       val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) u.vs_memory /\
       typedMemoryCopy$typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
         (type_memory_size dtv) s u /\
       ~u.vs_halted /\ u.vs_current_bb = z.cs_current_bb /\
       u.vs_inst_idx = LENGTH z.cs_current_insts` by
    (irule place_store_index_child_path >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
     qexists_tac `sw` >> simp[regions_disjoint_def] >>
     gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  `lookup_var counter u = SOME (n2w k)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_counter] >>
  drule_all place_store_counter_increment_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  `typedMemoryCopy$typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
     (type_memory_size dtv) s t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_trans >> qexists_tac `u` >>
     simp[] >> irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
     qexists_tac `a` >> simp[]) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  qexists_tac `t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  simp[] >> mp_tac typedMemoryCopyTheory.typed_copy_index_inv_step >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem place_store_index_back_edge_path:
  emit_inst JMP [Label hdr] [] a = ((),b) /\ fn_has_code a b func /\
  typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k s /\
  eval_operand length s = SOME nw /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  gas_marked_path F ctx func s 0 (OK (jump_to hdr s)) /\
  typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 k (jump_to hdr s) /\
  eval_operand length (jump_to hdr s) = SOME nw /\
  ~(jump_to hdr s).vs_halted /\ (jump_to hdr s).vs_current_bb = hdr /\
  (jump_to hdr s).vs_inst_idx = 0
Proof
  strip_tac >> conj_tac
  >- (irule place_store_branch_path >> simp[] >>
      qexistsl_tac [`[Label hdr]`, `JMP`, `a`, `b`] >>
      simp[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def]) >>
  conj_tac >- metis_tac[typedMemoryCopyTheory.typed_copy_index_inv_jump] >>
  simp[jump_to_def, eval_operand_def, lookup_var_def] >>
  Cases_on `length` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem place_store_index_init_path:
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  ~not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  fn_has_code init st0 func /\ ~s.vs_halted /\
  s.vs_current_bb = init.cs_current_bb /\ s.vs_inst_idx = LENGTH init.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0 t /\
      ~t.vs_halted /\ t.vs_current_bb = st0.cs_current_bb /\
      t.vs_inst_idx = LENGTH st0.cs_current_insts
Proof
  strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `!x. not_fresh_at sa x ==> x <> counter` by metis_tac[] >>
  drule_all place_store_assign_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  qexists_tac `t` >> simp[typedMemoryCopyTheory.typed_copy_index_inv_def,
    typedMemoryCopyTheory.typed_copy_index_prefix_zero]
QED

Theorem place_store_index_loop_path:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] c = ((),d) /\
  ci_mono sa a /\ not_fresh_at a counter /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\ N < dimword (:256) /\
  a.cs_current_insts = [] /\ fn_has_code a d func /\
  (!i q. i < N /\
     typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 i q /\
     eval_operand length q = SOME (n2w N) /\ ~q.vs_halted /\
     q.vs_current_bb = blabel /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path F ctx func q 0 (OK r) /\
         typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 (SUC i) r /\
         eval_operand length r = SOME (n2w N) /\ ~r.vs_halted /\
         r.vs_current_bb = a.cs_current_bb /\ r.vs_inst_idx = 0) /\
  typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 0 s /\
  eval_operand length s = SOME (n2w N) /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = 0 ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 N t /\
      eval_operand length t = SOME (n2w N) /\ ~t.vs_halted /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `Inv = \i q.
    typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 i q /\
    eval_operand length q = SOME (n2w N) /\ ~q.vs_halted /\
    q.vs_current_bb = a.cs_current_bb /\ q.vs_inst_idx = 0` >>
  `!i q. Inv i q ==> ~q.vs_halted` by simp[Abbr `Inv`] >>
  `!i q. i < N /\ Inv i q ==>
      ?r. gas_marked_path F ctx func q 0 (OK r) /\ Inv (SUC i) r` by
    (rpt gen_tac >> strip_tac >>
     `typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 i q /\
      eval_operand length q = SOME (n2w N) /\ ~q.vs_halted /\
      q.vs_current_bb = a.cs_current_bb /\ q.vs_inst_idx = LENGTH a.cs_current_insts` by
       gvs[Abbr `Inv`] >>
     drule_all place_store_index_test_path >>
     disch_then (qspec_then `ctx` (qx_choose_then `u` strip_assume_tac)) >>
     qpat_x_assum `!i q. i < N /\ _ /\ _ ==> _`
       (qspecl_then [`i`, `u`] mp_tac) >>
     simp[] >> disch_then (qx_choose_then `r` strip_assume_tac) >>
     qexists_tac `r` >> simp[Abbr `Inv`] >>
     metis_tac[gas_marked_path_then, ADD_CLAUSES]) >>
  `Inv 0 s` by simp[Abbr `Inv`] >>
  `?u. gas_marked_path F ctx func s 0 (OK u) /\ Inv N u` by
    (irule place_store_counted_iterate >> conj_tac
     >- first_assum ACCEPT_TAC >> conj_tac
     >- first_assum ACCEPT_TAC >> qexists_tac `0` >> simp[]) >>
  `typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s0 N u /\
   eval_operand length u = SOME (n2w N) /\ ~u.vs_halted /\
   u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts` by
     gvs[Abbr `Inv`] >>
  drule_all place_store_index_test_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  qexists_tac `t` >> simp[] >> metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem place_store_fixed_value_path:
  compile_copy_memory dst src n sa = ((),sb) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  n < dimword (:256) /\ val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\ n <= type_memory_size tv /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n dw) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw) (type_memory_size tv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all place_store_copy_fixed_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `(if n = 0 then s else mcopy (w2n dw) (w2n sw) n s)
                 with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  Cases_on `n = 0` >> simp[]
  >- (conj_tac
      >- (irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
          qexistsl_tac [`w2n sw`, `0`, `s.vs_memory`] >> simp[valueEncodingDefsTheory.mem_bytes_at_def]) >>
      simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
           typedMemoryCopyTheory.typed_copy_frame_def, lookup_var_def,
           venom_state_component_equality]) >>
  conj_tac >- (irule valueCopyTheory.mcopy_val_in_memory >> simp[]) >>
  conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
      qexistsl_tac [`w2n dw`, `n`] >>
      simp[typedMemoryCopyTheory.typed_copy_mcopy_state_frame]) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem place_store_counted_index_copy_path:
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [src;so] b2 = (sp,b3) /\ emit_op ADD [dst;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  ci_mono sa init /\ not_fresh_at init counter /\ ~not_fresh_at sa counter /\
  sa.cs_current_bb = init.cs_current_bb /\ sa.cs_current_insts = init.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. length = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==> place_store_counted_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa stx func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s N t /\
      eval_operand length t = SOME (n2w N) /\ ~t.vs_halted /\
      t.vs_current_bb = stx.cs_current_bb /\ t.vs_inst_idx = LENGTH stx.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono init st0 /\ ci_mono st0 st1 /\ ci_mono stj st2 /\
   ci_mono b6 ste /\ ci_mono ste st3` by
    metis_tac[exprLoweringPropsTheory.ci_mono_emit_inst, pairTheory.SND] >>
  `ci_mono st1 sth /\ ci_mono st2 stb /\ ci_mono st3 stx` by
    metis_tac[exprLoweringPropsTheory.ci_mono_new_block, pairTheory.SND] >>
  `ci_mono sth h1 /\ ci_mono h1 stj /\ ci_mono stb b1 /\
   ci_mono b1 b2 /\ ci_mono b2 b3 /\ ci_mono b3 b4 /\ ci_mono b5 b6` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono] >>
  `ci_mono b4 b5` by
    metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
  `!a b c. ci_mono a b /\ ci_mono b c ==> ci_mono a c` by
    (gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `ci_mono sa st0 /\ ci_mono st0 sth /\ ci_mono sth st2 /\ ci_mono stb b4 /\
   ci_mono stb ste /\ ci_mono ste stx` by metis_tac[] >>
  `ci_mono sa sth /\ ci_mono sa stb /\ ci_mono st0 stx /\ ci_mono sth stj` by metis_tac[] >>
  qpat_x_assum `!a b c. ci_mono a b /\ ci_mono b c ==> ci_mono a c` kall_tac >>
  `cs_extends st0 st1 /\ cs_extends stj st2 /\ cs_extends ste st3 /\
   cs_extends st1 sth /\ cs_extends st2 stb /\ cs_extends st3 stx /\
   cs_extends sth stj /\ cs_extends stb ste` by metis_tac[ci_mono_def] >>
  `cs_extends stj stx /\ cs_extends ste stx /\ cs_extends stb stx /\
   cs_extends sth stx /\ cs_extends st0 sth /\ cs_extends sth st2` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code init st0 func /\ fn_has_code st0 st1 func /\
   fn_has_code sth st2 func /\ fn_has_code stb ste func /\ fn_has_code ste st3 func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_trans]) >>
  `sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
   stb.cs_current_bb = blabel /\ stb.cs_current_insts = [] /\
   stx.cs_current_bb = exit /\ stx.cs_current_insts = []` by gvs[new_block_def] >>
  `not_fresh_at sth counter /\ not_fresh_at stb counter` by
    (gvs[not_fresh_at_def, ci_mono_def] >> metis_tac[LESS_LESS_EQ_TRANS, LESS_EQ_TRANS]) >>
  `(!x. src = Var x ==> not_fresh_at sth x) /\
   (!x. dst = Var x ==> not_fresh_at sth x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  `?u. gas_marked_path F ctx func s 0 (OK u) /\
       typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s 0 u /\
       ~u.vs_halted /\ u.vs_current_bb = st0.cs_current_bb /\
       u.vs_inst_idx = LENGTH st0.cs_current_insts` by
    (irule place_store_index_init_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_inst ASSIGN _ _ init = _`)) >> simp[]) >>
  `eval_operand length u = SOME (n2w N)` by
    (`typedMemoryCopy$typed_copy_state_frame sa (w2n dw)
        (N * type_memory_size dtv) s u` by
       gvs[typedMemoryCopyTheory.typed_copy_index_inv_def] >>
     metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand]) >>
  drule_all place_store_index_back_edge_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `!i q. i < N /\
     typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s i q /\
     eval_operand length q = SOME (n2w N) /\ ~q.vs_halted /\
     q.vs_current_bb = blabel /\ q.vs_inst_idx = 0 ==>
     ?r. gas_marked_path F ctx func q 0 (OK r) /\
         typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s (SUC i) r /\
         eval_operand length r = SOME (n2w N) /\ ~r.vs_halted /\
         r.vs_current_bb = sth.cs_current_bb /\ r.vs_inst_idx = 0` by
    (rpt gen_tac >> strip_tac >>
     `q.vs_current_bb = stb.cs_current_bb /\
      q.vs_inst_idx = LENGTH stb.cs_current_insts` by simp[] >>
     drule_all place_store_index_body_path >>
     disch_then (qx_choose_then `r` strip_assume_tac) >>
     `eval_operand length r = SOME (n2w N)` by
       metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
     drule_all place_store_index_back_edge_path >>
     disch_then (qspec_then `ctx` strip_assume_tac) >>
     qexists_tac `jump_to hdr r` >> simp[] >>
     metis_tac[gas_marked_path_then, ADD_CLAUSES]) >>
  `?t. gas_marked_path F ctx func (jump_to hdr u) 0 (OK t) /\
       typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s N t /\
       eval_operand length t = SOME (n2w N) /\ ~t.vs_halted /\
       t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by
    (irule place_store_index_loop_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >> simp[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem place_store_counted_sarray_slow_path:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  ~(type_memory_size dtv = type_memory_size stv /\
    ~is_abi_dynamic cenv.ce_struct_fields dty) /\
  N < dimword (:256) /\
  (!i. i < N ==> place_store_counted_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  (!i. i < N ==> val_in_memory stv (f i)
     (w2n sw + i * type_memory_size stv) s.vs_memory) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!i. i < N ==> val_in_memory dtv (f i)
         (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  rename1 `fresh_label "typed_sa_cond" sa = (hdr,l1)` >>
  rename1 `fresh_label "typed_sa_body" l1 = (blabel,l2)` >>
  rename1 `fresh_label "typed_sa_exit" l2 = (exit,l3)` >>
  rename1 `fresh_var l3 = (counter,init)` >>
  rename1 `emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0)` >>
  rename1 `emit_inst JMP [Label hdr] [] st0 = ((),st1)` >>
  rename1 `new_block hdr st1 = (u1,sth)` >>
  rename1 `emit_op LT [Var counter; Lit (n2w N)] sth = (lt,h1)` >>
  rename1 `emit_op ISZERO [lt] h1 = (done,stj)` >>
  rename1 `emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2)` >>
  rename1 `new_block blabel st2 = (u2,stb)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2)` >>
  rename1 `emit_op ADD [src;so] b2 = (sp,b3)` >>
  rename1 `emit_op ADD [dst;doff] b3 = (dp,b4)` >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5)` >>
  rename1 `emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6)` >>
  rename1 `emit_inst ASSIGN [inc] [counter] b6 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `new_block exit st3 = (u3,stx)` >>
  drule_all typedMemoryCopyTheory.typed_copy_sarray_slow_layout >> strip_tac >>
  `not_fresh_at init counter` by
    gvs[fresh_var_def, not_fresh_at_def] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       typedMemoryCopy$typed_copy_index_inv sa counter src dst sw dw f stv dtv N s N t /\
       eval_operand (Lit (n2w N)) t = SOME (n2w N) /\ ~t.vs_halted /\
       t.vs_current_bb = stx.cs_current_bb /\
       t.vs_inst_idx = LENGTH stx.cs_current_insts` by
    (irule place_store_counted_index_copy_path >> simp[eval_operand_def] >>
     goal_assum (drule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  gvs[typedMemoryCopyTheory.typed_copy_index_inv_def,
      typedMemoryCopyTheory.typed_copy_index_prefix_complete]
QED

Theorem place_store_counted_sarray_path:
  compile_copy_sarray_typed cenv dst dty src sty N sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
  (!i. i < N ==> place_store_counted_entry cenv ctx dty sty dtv stv
     (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  N < dimword (:256) /\
  val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n sw) s.vs_memory /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n dw) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\
            ~is_abi_dynamic cenv.ce_struct_fields dty`
  >- (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once contextTheory.compile_store_memory_typed_def] >> strip_tac >>
      `stv = dtv` by metis_tac[typedMemoryCopyTheory.typed_copy_static_widening] >>
      qpat_x_assum `stv = dtv` (SUBST_ALL_TAC o SYM) >>
      `val_footprint (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) <= N * type_memory_size stv` by
        simp[val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
      drule place_store_fixed_value_path >>
      disch_then (qspecl_then [`ArrayV (SArrayV kvs)`, `ArrayTV stv (Fixed N)`] mp_tac) >>
      simp[valueEncodingTheory.type_memory_size_def] >>
      disch_then irule >> simp[] >>
      gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  drule_all typedMemoryCopyTheory.typed_copy_sarray_representation >> strip_tac >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       (!i. i < N ==> val_in_memory dtv
         (case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)
         (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
       typedMemoryCopy$typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (ho_match_mp_tac place_store_counted_sarray_slow_path >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem place_store_counted_sarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Fixed cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Fixed cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Fixed cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      place_store_counted_entry cenv ctx cd cs cdt cst cv) ==>
    place_store_counted_entry cenv ctx (ArrayT de (Fixed cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typedMemoryCopyTheory.typed_copy_array_source >> strip_tac >> gvs[] >>
  `sb = Fixed cap` by
    (drule typedMemoryCopyTheory.typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Fixed cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `default_value tv = default_value tv'` by
    metis_tac[typedMemoryCopyTheory.typed_copy_default_widening] >>
  `!i. i < cap ==> place_store_counted_entry cenv ctx de se tv' tv
      (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once typedCopyDomainTheory.type_rank_def] >>
     `val_wf tv (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (irule typedMemoryCopyTheory.typed_copy_sparse_lookup_wf >>
        qexists_tac `cap` >> fs[valueEncodingDefsTheory.val_wf_def]) >>
     `val_wf tv' (case ALOOKUP l i of NONE => default_value tv | SOME v => v)` by
       (asm_rewrite_tac[] >> irule typedMemoryCopyTheory.typed_copy_sparse_lookup_wf >>
        qexists_tac `cap` >> fs[valueEncodingDefsTheory.val_wf_def]) >>
     Cases_on `ALOOKUP l i` >> gvs[]
     >- metis_tac[vyperTypingTheory.default_value_well_typed,
                 cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  simp[place_store_counted_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  simp[valueEncodingTheory.type_memory_size_def] >>
  irule place_store_counted_sarray_path >> simp[] >>
  (conj_tac >- gvs[valueEncodingTheory.type_memory_size_def]) >>
  (conj_tac >- simp[vyperTypingTheory.value_has_type_def]) >>
  goal_assum (drule_at (Pat `compile_copy_sarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`tv`, `sw`, `tenv`] >>
  gvs[valueEncodingTheory.type_memory_size_def, regions_disjoint_def,
      vyperTypingTheory.value_has_type_def]
QED

Theorem place_store_counted_dynarray_prefix_path:
  emit_op MLOAD [src] a = (length,a1) /\
  emit_op GT [length; Lit (n2w C)] a1 = (too_long,a2) /\
  emit_op ISZERO [too_long] a2 = (ok,a3) /\
  emit_void ASSERT [ok] a3 = ((),a4) /\
  emit_void MSTORE [dst; length] a4 = ((),a5) /\
  emit_op ADD [src; Lit 32w] a5 = (sd,a6) /\
  emit_op ADD [dst; Lit 32w] a6 = (dd,b) /\
  (!x. src = Var x ==> not_fresh_at a x) /\
  (!x. dst = Var x ==> not_fresh_at a x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  LENGTH vs <= C /\ C < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand length t = SOME (n2w (LENGTH vs)) /\
      eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
      mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w (LENGTH vs) : bytes32) T /\
      (!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
         (w2n sw + 32 + i * type_memory_size stv) t.vs_memory) /\
      typedMemoryCopy$typed_copy_state_frame a (w2n dw) 32 s t /\
      ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
      t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  `!out. step_inst_base (mk_inst a.cs_next_id MLOAD [src] [out]) s =
     OK (update_var out (n2w (LENGTH vs)) s)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_dynarray_mload_step] >>
  `?u. run_inst_seq (emitted_insts a b) s = OK u /\
       eval_operand length u = SOME (n2w (LENGTH vs)) /\
       eval_operand sd u = SOME (sw + 32w) /\
       eval_operand dd u = SOME (dw + 32w) /\
       mem_bytes_at (w2n dw) 32 u.vs_memory = word_to_bytes (n2w (LENGTH vs) : bytes32) T /\
       typedMemoryCopy$typed_copy_state_frame a (w2n dw) 32 s u /\
       ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    suspend "raw_sequence" >>
  `b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   same_blocks a b /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts a b) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts a b)) = 0` by
    (gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def] >>
     simp[same_blocks_def, emitted_insts_def] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.DROP_LENGTH_APPEND, listTheory.APPEND] >>
     simp[mk_inst_def, is_terminator_def]) >>
  `gas_marked_path F ctx func s 0
    (OK (u with vs_inst_idx := LENGTH b.cs_current_insts))` by
    (irule place_store_emitted_seq_path >> simp[] >> qexists_tac `a` >>
     metis_tac[listTheory.LENGTH_NIL]) >>
  `val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
      (w2n sw) u.vs_memory` by
    (irule typedMemoryCopyTheory.typed_copy_frame_preserves_source >>
     conj_tac >- simp[] >>
     qexistsl_tac [`32`, `w2n dw`, `s.vs_memory`] >>
     gvs[typedMemoryCopyTheory.typed_copy_state_frame_def, valueEncodingTheory.type_memory_size_def]) >>
  qexists_tac `u with vs_inst_idx := LENGTH b.cs_current_insts` >>
  gvs[same_blocks_def, eval_operand_def, lookup_var_def,
      typedMemoryCopyTheory.typed_copy_dynarray_representation,
      typedMemoryCopyTheory.typed_copy_state_frame_def]
QED

Resume place_store_counted_dynarray_prefix_path[raw_sequence]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `val_wf _ _` kall_tac >>
  qpat_x_assum `val_in_memory _ _ _ _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  gvs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def] >>
  `!j v u. a.cs_next_var <= j ==>
    eval_operand src (update_var (STRING #"%" (toString j)) v u) = eval_operand src u /\
    eval_operand dst (update_var (STRING #"%" (toString j)) v u) = eval_operand dst u` by
    (rpt gen_tac >> strip_tac >> conj_tac >>
     Cases_on `src` >> Cases_on `dst` >>
     simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
     rpt strip_tac >> IF_CASES_TAC >> gvs[not_fresh_at_def]) >>
  pure_rewrite_tac[emitted_insts_def] >> simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,
                  rich_listTheory.DROP_LENGTH_APPEND, listTheory.APPEND] >>
  simp[Once run_inst_seq_def] >>
  `LENGTH vs < dimword (:256)` by
    (gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, emitHelperPropsTheory.lookup_var_update_var,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD, bool_to_word_def,
       arithmeticTheory.NOT_LESS] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure1_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var, bool_to_word_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
       emitHelperPropsTheory.eval_operand_mstore, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
       emitHelperPropsTheory.eval_operand_mstore, eval_operand_def] >>
  simp[run_inst_seq_def] >> suspend "raw_frame"
QED

Resume place_store_counted_dynarray_prefix_path[raw_frame]:
  markerLib.RESUME_TAC >>
  `typedMemoryCopy$typed_copy_state_frame a (w2n dw) 32 s
    ((mstore (w2n dw) (n2w (LENGTH vs)) s) with vs_inst_idx := s.vs_inst_idx)` by
    irule typedMemoryCopyTheory.typed_copy_mstore_state_frame >>
  `mem_bytes_at (w2n dw) 32 (mstore (w2n dw) (n2w (LENGTH vs)) s).vs_memory =
    word_to_bytes (n2w (LENGTH vs) : bytes32) T` by
    simp[valueEncodingPropsTheory.mem_bytes_at_mstore_same] >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      emitHelperPropsTheory.lookup_var_update_var, update_var_def,
      mstore_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[not_fresh_at_def]
QED

Finalise place_store_counted_dynarray_prefix_path

Theorem place_store_counted_dynarray_bulk_data_path:
  emit_op MUL [length; Lit (n2w (type_memory_size tv))] sa = (bytes,b) /\
  compile_copy_memory_dynamic dst src bytes b = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand length s = SOME (n2w N) /\
  (!i. i < N ==> val_wf tv (f i) /\
    val_in_memory tv (f i) (w2n sw + i * type_memory_size tv) s.vs_memory) /\
  w2n sw + N * type_memory_size tv < dimword (:256) /\
  w2n dw + N * type_memory_size tv < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!i. i < N ==> val_in_memory tv (f i)
        (w2n dw + i * type_memory_size tv) t.vs_memory) /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw) (N * type_memory_size tv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `N * type_memory_size tv < dimword (:256)` by decide_tac >>
  `ci_mono sa b /\ ci_mono b sb` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
      contextTheory.compile_copy_memory_dynamic_def,
      exprLoweringPropsTheory.ci_mono_emit_void, pairTheory.SND] >>
  `fn_has_code sa b func /\ fn_has_code b sb func` by
    (gvs[ci_mono_def] >>
     metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_refl]) >>
  `?u. gas_marked_path F ctx func s 0 (OK u) /\
       eval_operand bytes u = SOME (n2w (N * type_memory_size tv)) /\
       u.vs_memory = s.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s u) /\
       ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
       u.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[] >>
     qexistsl_tac [`[length; Lit (n2w (type_memory_size tv))]`, `MUL`] >>
     simp[venomInstTheory.is_terminator_def, step_inst_base_opcode_eqs,
       mk_inst_def, exec_pure2_def, eval_operand_def, GSYM wordsTheory.word_mul_n2w]) >>
  `eval_operand src u = SOME sw /\ eval_operand dst u = SOME dw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  drule_all place_store_copy_dynamic_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `(mcopy (w2n dw) (w2n sw) (N * type_memory_size tv) u)
     with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `gas_marked_path F ctx func s 0
     (OK ((mcopy (w2n dw) (w2n sw) (N * type_memory_size tv) u)
       with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qpat_x_assum `gas_marked_path F ctx func u _ _` mp_tac >>
     simp[wordsTheory.w2n_n2w, LESS_MOD] >>
     metis_tac[gas_marked_path_then, ADD_CLAUSES]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      irule valueCopyTheory.val_in_memory_relocate >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`w2n sw + i * type_memory_size tv`,
                    `type_memory_size tv`, `u.vs_memory`] >>
      simp[] >> conj_tac
      >- metis_tac[exprSimPropsTheory.val_footprint_le] >>
      irule valueEncodingProofsTheory.mem_bytes_at_translated_window >>
      qexists_tac `N * type_memory_size tv` >>
      simp[valueEncodingProofsTheory.mcopy_mem_bytes_at_same] >>
      `SUC i <= N` by decide_tac >>
      `SUC i * type_memory_size tv <= N * type_memory_size tv` by
        simp[arithmeticTheory.LE_MULT_RCANCEL] >>
      qpat_x_assum `SUC i * _ <= _` mp_tac >>
      pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_state_frame_trans >>
      qexists_tac `u` >>
      simp[typedMemoryCopyTheory.typed_copy_mcopy_state_frame]) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem place_store_counted_dynarray_path:
  compile_copy_dynarray_typed cenv dst dty C src sty sa = ((),sb) /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  (dty = sty ==> dtv = stv) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  LENGTH vs <= C /\ C < dimword (:256) /\
  val_wf (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) /\
  val_wf (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs))
    (w2n sw) s.vs_memory /\
  (!i. i < LENGTH vs ==> place_store_counted_entry cenv ctx dty sty dtv stv (EL i vs)) /\
  w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) < dimword (:256) /\
  (w2n sw + type_memory_size (ArrayTV stv (Dynamic scap)) <= w2n dw \/
   w2n dw + type_memory_size (ArrayTV dtv (Dynamic C)) <= w2n sw) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs))
        (w2n dw) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw)
        (type_memory_size (ArrayTV dtv (Dynamic C))) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >>
  rename1 `emit_op ADD [dst; Lit 32w] a6 = (dd,b)` >>
  rename1 `emit_op ADD [src; Lit 32w] a5 = (sd,a6)` >> disch_tac >>
  drule_all typedMemoryCopyTheory.typed_copy_dyn_prefix_mono >> strip_tac >>
  `ci_mono b sb` by suspend "suffix_mono" >>
  `fn_has_code sa b func /\ fn_has_code b sb func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_mid, cs_extends_refl]) >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       eval_operand length t = SOME (n2w (LENGTH vs)) /\
       eval_operand sd t = SOME (sw + 32w) /\ eval_operand dd t = SOME (dw + 32w) /\
       mem_bytes_at (w2n dw) 32 t.vs_memory = word_to_bytes (n2w (LENGTH vs) : bytes32) T /\
       (!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
          (w2n sw + 32 + i * type_memory_size stv) t.vs_memory) /\
       typedMemoryCopy$typed_copy_state_frame sa (w2n dw) 32 s t /\
       ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
       t.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule place_store_counted_dynarray_prefix_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op GT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ a5 = _`)) >>
     goal_assum (drule_at Any) >> qexistsl_tac [`dtv`, `scap`] >> simp[]) >>
  suspend "suffix"
QED

Resume place_store_counted_dynarray_path[suffix_mono]:
  qmatch_asmsub_abbrev_tac `suffix b = ((),sb)` >>
  `ci_mono b (SND (suffix b))` suffices_by gvs[] >>
  unabbrev_all_tac >> IF_CASES_TAC >>
  rpt (FIRST [irule exprLoweringPropsTheory.ci_mono_bind,
              irule exprLoweringPropsTheory.ci_mono_ignore_bind] >>
       rpt conj_tac >> rpt gen_tac >> BETA_TAC) >>
  simp[exprLoweringPropsTheory.ci_mono_emit_op, exprLoweringPropsTheory.ci_mono_emit_inst,
       exprLoweringPropsTheory.ci_mono_new_block, exprLoweringPropsTheory.ci_mono_fresh_label,
       exprLoweringPropsTheory.ci_mono_fresh_var, exprLoweringPropsTheory.ci_mono_comp_return,
       cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family,
       contextTheory.compile_copy_memory_dynamic_def, exprLoweringPropsTheory.ci_mono_emit_void]
QED

Resume place_store_counted_dynarray_path[suffix]:
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_void _ _ _ = _` kall_tac) >>
  `LENGTH vs <= scap` by gvs[typedMemoryCopyTheory.typed_copy_dynarray_wf] >>
  `LENGTH vs * type_memory_size stv <= scap * type_memory_size stv /\
   LENGTH vs * type_memory_size dtv <= C * type_memory_size dtv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `w2n (sw + 32w) = w2n sw + 32 /\ w2n (dw + 32w) = w2n dw + 32` by
    (fs[valueEncodingTheory.type_memory_size_def] >> simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, LESS_MOD]) >>
  `w2n (sw + 32w) + LENGTH vs * type_memory_size stv < dimword (:256) /\
   w2n (dw + 32w) + LENGTH vs * type_memory_size dtv < dimword (:256) /\
   (w2n (sw + 32w) + LENGTH vs * type_memory_size stv <= w2n (dw + 32w) \/
    w2n (dw + 32w) + LENGTH vs * type_memory_size dtv <= w2n (sw + 32w))` by
    (gns[valueEncodingTheory.type_memory_size_def, Excl "LE_MULT_RCANCEL"] >> decide_tac) >>
  `?u. gas_marked_path F ctx func t 0 (OK u) /\
       (!i. i < LENGTH vs ==> val_in_memory dtv (EL i vs)
          (w2n (dw + 32w) + i * type_memory_size dtv) u.vs_memory) /\
       typedMemoryCopy$typed_copy_state_frame b (w2n (dw + 32w))
         (LENGTH vs * type_memory_size dtv) t u /\
       ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts` by suspend "data" >>
  suspend "reconstruct"
QED

Resume place_store_counted_dynarray_path[data]:
  markerLib.RESUME_TAC >>
  rpt (qpat_x_assum `ci_mono _ _` kall_tac) >>
  qpat_x_assum `val_in_memory _ _ _ s.vs_memory` kall_tac >>
  qpat_x_assum `typedMemoryCopy$typed_copy_state_frame sa _ _ s t` kall_tac >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` kall_tac >>
  `LENGTH vs < dimword (:256)` by
    (gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  Cases_on `type_memory_size dtv = type_memory_size stv /\ dty = sty` >>
  IF (qpat_assum `type_memory_size dtv = type_memory_size stv /\ dty = sty` kall_tac)
    (suspend "bulk_data") (suspend "slow_data")
QED

Resume place_store_counted_dynarray_path[bulk_data]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n (dw + 32w) = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  `dtv = stv` by simp[] >> gvs[] >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> strip_tac >>
  ho_match_mp_tac (GEN_ALL place_store_counted_dynarray_bulk_data_path) >> simp[] >>
  goal_assum (drule_at (Pat `emit_op MUL _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_copy_memory_dynamic _ _ _ _ = _`)) >>
  qexists_tac `sw + 32w` >> simp[] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (fs[valueEncodingTheory.type_memory_size_def] >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, LESS_MOD]) >>
  gvs[typedMemoryCopyTheory.typed_copy_dynarray_wf]
QED

Resume place_store_counted_dynarray_path[slow_data]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `w2n (dw + 32w) = _` kall_tac >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  qpat_x_assum `_ b = ((),sb)` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >>
    pop_assum (fn th => assume_tac th >> pure_rewrite_tac [th]) >>
    CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV)) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gnvs[] >>
  rename1 `fresh_label "typed_dyn_cond" b = (hdr,l1)` >>
  rename1 `fresh_label "typed_dyn_body" l1 = (blabel,l2)` >>
  rename1 `fresh_label "typed_dyn_exit" l2 = (exit,l3)` >>
  rename1 `fresh_var l3 = (counter,init)` >>
  rename1 `emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0)` >>
  rename1 `emit_inst JMP [Label hdr] [] st0 = ((),st1)` >>
  rename1 `new_block hdr st1 = (u1,sth)` >>
  rename1 `emit_op LT [Var counter; length] sth = (lt,h1)` >>
  rename1 `emit_op ISZERO [lt] h1 = (done,stj)` >>
  rename1 `emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2)` >>
  rename1 `new_block blabel st2 = (u2,stb)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1)` >>
  rename1 `emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2)` >>
  rename1 `emit_op ADD [sd;so] b2 = (sp,b3)` >>
  rename1 `emit_op ADD [dd;doff] b3 = (dp,b4)` >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5)` >>
  rename1 `emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6)` >>
  rename1 `emit_inst ASSIGN [inc] [counter] b6 = ((),ste)` >>
  rename1 `emit_inst JMP [Label hdr] [] ste = ((),st3)` >>
  rename1 `new_block exit st3 = (u3,stx)` >>
  drule_all typedMemoryCopyTheory.typed_copy_dynarray_slow_layout >> strip_tac >>
  `not_fresh_at init counter` by gvs[fresh_var_def, not_fresh_at_def] >>
  `!i. i < LENGTH vs ==> place_store_counted_entry cenv ctx dty sty dtv stv (EL i vs) /\
       val_wf stv (EL i vs) /\ val_wf dtv (EL i vs)` by
    gvs[typedMemoryCopyTheory.typed_copy_dynarray_wf] >>
  `w2n (sw + 32w) = w2n sw + 32` by
    (fs[valueEncodingTheory.type_memory_size_def] >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, LESS_MOD]) >>
  `!i. i < LENGTH vs ==> val_in_memory stv (EL i vs)
     (w2n (sw + 32w) + i * type_memory_size stv) t.vs_memory` by
    (qpat_assum `w2n (sw + 32w) = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `!i. _ ==> val_in_memory _ _ _ _` mp_tac >>
     simp_tac std_ss [AC ADD_ASSOC ADD_COMM]) >>
  qpat_x_assum `w2n (sw + 32w) = _` kall_tac >>
  suspend "slow_loop"
QED

Resume place_store_counted_dynarray_path[slow_loop]:
  markerLib.RESUME_TAC >>
  `?u. gas_marked_path F ctx func t 0 (OK u) /\
       typedMemoryCopy$typed_copy_index_inv b counter sd dd (sw + 32w) (dw + 32w)
         (\i. EL i vs) stv dtv (LENGTH vs) t (LENGTH vs) u /\
       eval_operand length u = SOME (n2w (LENGTH vs)) /\ ~u.vs_halted /\
       u.vs_current_bb = stx.cs_current_bb /\
       u.vs_inst_idx = LENGTH stx.cs_current_insts` by
    (irule place_store_counted_index_copy_path >> simp[] >>
     goal_assum (drule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `u` >> simp[] >>
  gvs[typedMemoryCopyTheory.typed_copy_index_inv_def,
      typedMemoryCopyTheory.typed_copy_index_prefix_complete]
QED

Resume place_store_counted_dynarray_path[reconstruct]:
  markerLib.RESUME_TAC >> (
  qpat_x_assum `_ b = ((),sb)` kall_tac >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  `typedMemoryCopy$typed_copy_state_frame b (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv) t u` by metis_tac[] >>
  qexists_tac `u` >> simp[] >>
  conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_dynarray_reconstruct >> conj_tac
      >- (qpat_x_assum `!i. _ ==> val_in_memory _ _ _ u.vs_memory` mp_tac >>
          qpat_assum `w2n (dw + 32w) = _` (fn th => rewrite_tac[th]) >>
          simp_tac std_ss [AC ADD_ASSOC ADD_COMM]) >>
      goal_assum (drule_at (Pat `typedMemoryCopy$typed_copy_state_frame _ _ _ _ _`)) >>
      simp[valueEncodingDefsTheory.mem_word_at_def, GSYM valueEncodingDefsTheory.mem_bytes_at_def]) >>
  `typedMemoryCopy$typed_copy_state_frame sa (w2n dw + 32)
      (LENGTH vs * type_memory_size dtv) t u` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  irule (GEN_ALL typedMemoryCopyTheory.typed_copy_state_frame_trans) >>
  qexists_tac `t` >> conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
      goal_assum (drule_at (Pat `typedMemoryCopy$typed_copy_state_frame _ _ _ s t`)) >>
      simp[valueEncodingTheory.type_memory_size_def]) >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
  goal_assum (drule_at (Pat `typedMemoryCopy$typed_copy_state_frame sa _ _ t _`)) >>
  simp[valueEncodingTheory.type_memory_size_def, Excl "LE_MULT_RCANCEL"])
QED
Finalise place_store_counted_dynarray_path

Theorem place_store_counted_dynarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      place_store_counted_entry cenv ctx cd cs cdt cst cv) ==>
    place_store_counted_entry cenv ctx (ArrayT de (Dynamic cap)) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typedMemoryCopyTheory.typed_copy_array_source >> strip_tac >> gvs[] >>
  `?scap. sb = Dynamic scap /\ scap <= cap` by
    (drule typedMemoryCopyTheory.typed_copy_array_widening >> strip_tac >> gvs[]) >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  `type_widens_to tenv se de` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     simp[type_widens_to_def, arg_type_fits_def, well_formed_type_def,
          evaluate_type_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
  `cap < dimword (:256)` by
    (qpat_x_assum `type_slot_size (ArrayTV tv' (Dynamic cap)) < _` mp_tac >>
     simp[type_slot_size_def] >>
     `cap <= cap * type_slot_size tv'` by
       (Cases_on `type_slot_size tv'` >> gvs[MULT_CLAUSES]) >> decide_tac) >>
  `type_memory_bytes cenv de = type_memory_size tv' /\
   type_memory_bytes cenv se = type_memory_size tv` by
    (conj_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `!i. i < LENGTH l ==> place_store_counted_entry cenv ctx de se tv' tv (EL i l)` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Once typedCopyDomainTheory.type_rank_def] >>
     gvs[typedMemoryCopyTheory.typed_copy_dynarray_wf, vyperTypingTheory.all_have_type_EVERY,
         listTheory.EVERY_EL]) >>
  simp[place_store_counted_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  irule place_store_counted_dynarray_path >> simp[] >>
  goal_assum (drule_at (Pat `compile_copy_dynarray_typed _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`scap`, `tv`, `sw`] >> simp[] >>
  gvs[valueEncodingTheory.type_memory_size_def, regions_disjoint_def,
      vyperTypingTheory.value_has_type_def] >> strip_tac >> gvs[]
QED

Theorem place_store_counted_tuple_path:
  !dtys stys dtvs stvs vs dst src doff soff sa sb s dw sw.
  LIST_REL (\(dty,dtv) (sty,stv,v).
    type_memory_bytes cenv dty = type_memory_size dtv /\
    type_memory_bytes cenv sty = type_memory_size stv /\
    place_store_counted_entry cenv ctx dty sty dtv stv v)
    (ZIP (dtys,dtvs)) (ZIP (stys,ZIP (stvs,vs))) /\
  LENGTH dtys = LENGTH dtvs /\ LENGTH stys = LENGTH stvs /\ LENGTH stvs = LENGTH vs /\
  tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
  compile_typed_copy_fields cenv dst src dtys stys doff soff sa = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  tuple_in_memory vs stvs (w2n sw + soff) s.vs_memory /\
  w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
  w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
  (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
   w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typedMemoryCopy$typed_copy_state_frame sa (w2n dw + doff)
        (type_memory_size_list dtvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `vs` >>
      gvs[contextTheory.compile_store_memory_typed_def, comp_return_def,
          valueEncodingDefsTheory.val_wf_def,
          valueEncodingDefsTheory.val_in_memory_def, valueEncodingTheory.type_memory_size_def] >>
      qexists_tac `s` >>
      simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules,
           typedMemoryCopyTheory.typed_copy_state_frame_def,
           typedMemoryCopyTheory.typed_copy_frame_def,
           venom_state_component_equality]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `stys` >> Cases_on `dtvs` >> Cases_on `stvs` >> Cases_on `vs` >>
  gnvs[] >>
  rename1 `place_store_counted_entry cenv ctx dty sty dtv stv v` >>
  gnvs[valueEncodingDefsTheory.val_wf_def, valueEncodingDefsTheory.val_in_memory_def,
       valueEncodingTheory.type_memory_size_def] >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty cs2 = (u,sc)` >>
  Cases_on `u` >>
  rename1 `compile_typed_copy_fields cenv dst src dtys stys _ _ sc = ((),sb)` >>
  rename1 `LIST_REL _ (ZIP (dtys,dtvs)) (ZIP (stys,ZIP (stvs,vs)))` >>
  `ci_mono sa sc /\ ci_mono sc sb` by
    (qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' cs2` by
       metis_tac[typedMemoryCopyTheory.typed_copy_offset_mono] >>
     `ci_mono cs2 sc` by
       metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
     `ci_mono sc sb` by
       metis_tac[cj 2 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  qpat_assum `compile_with_byte_offset dst _ _ = _` mp_tac >>
  disch_then (mp_then (Pat `compile_with_byte_offset _ _ _ = _`) mp_tac
    place_store_counted_entry_offset_path) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`sw`, `s`, `func`, `dw`] mp_tac) >>
  (impl_tac >- (simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qpat_x_assum `compile_with_byte_offset dst _ _ = _` kall_tac >>
  qpat_x_assum `compile_with_byte_offset src _ _ = _` kall_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `place_store_counted_entry _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `val_in_memory stv _ _ _` kall_tac >>
  `tuple_in_memory vs stvs (soff + (type_memory_size stv + w2n sw)) t.vs_memory` by
    (irule typedMemoryCopyTheory.typed_copy_tuple_frame >> simp[] >>
     qexistsl_tac [`w2n dw + doff`, `type_memory_size dtv`, `s.vs_memory`] >>
     gvs[typedMemoryCopyTheory.typed_copy_state_frame_def] >> decide_tac) >>
  `eval_operand dst t = SOME dw /\ eval_operand src t = SOME sw` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  `(!x. dst = Var x ==> not_fresh_at sc x) /\
   (!x. src = Var x ==> not_fresh_at sc x)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
  qpat_x_assum `!stys dtvs stvs vs dst src doff soff sa sb s dw sw. _` drule >>
  disch_then (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`t`, `dw`, `sw`] mp_tac) >>
  (impl_tac >- (pure_asm_rewrite_tac[GSYM ADD_ASSOC] >> decide_tac)) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists_tac `u` >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  pure_asm_rewrite_tac[GSYM ADD_ASSOC] >> simp[] >> conj_tac
  >- (conj_tac
      >- (irule typedMemoryCopyTheory.typed_copy_frame_preserves_source >>
      conj_tac >- (first_assum ACCEPT_TAC) >>
      qexistsl_tac [`type_memory_size_list dtvs`,
        `doff + type_memory_size dtv + w2n dw`, `t.vs_memory`] >>
      gvs[typedMemoryCopyTheory.typed_copy_state_frame_def] >> decide_tac) >>
      metis_tac[ADD_ASSOC]) >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_trans >> qexists_tac `t` >>
  conj_tac
  >- (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
      qexistsl_tac [`w2n dw + doff`, `type_memory_size dtv`] >>
      simp[ADD_COMM]) >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_mono >> qexists_tac `sc` >> simp[] >>
  irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
  qexistsl_tac [`doff + type_memory_size dtv + w2n dw`,
    `type_memory_size_list dtvs`] >> simp[]
QED

Theorem place_store_counted_fields_from_semantics:
  !dtys stys dtvs stvs vs.
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    LIST_REL (type_widens_to tenv) stys dtys /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs /\
    OPT_MMAP (evaluate_type tenv) stys = SOME stvs /\
    values_have_types dtvs vs /\ values_have_types stvs vs /\
    tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
    (!cd cs cdt cst cv. MEM cd dtys ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      place_store_counted_entry cenv ctx cd cs cdt cst cv) ==>
    LIST_REL (\(dty,dtv) (sty,stv,v).
      type_memory_bytes cenv dty = type_memory_size dtv /\
      type_memory_bytes cenv sty = type_memory_size stv /\
      place_store_counted_entry cenv ctx dty sty dtv stv v)
      (ZIP (dtys,dtvs)) (ZIP (stys,ZIP (stvs,vs))) /\
    LENGTH dtys = LENGTH dtvs /\ LENGTH stys = LENGTH stvs /\ LENGTH stvs = LENGTH vs
Proof
  Induct >> Cases_on `stys` >> Cases_on `dtvs` >>
  Cases_on `stvs` >> Cases_on `vs` >>
  simp[AllCaseEqs(),
       vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def] >>
  rpt strip_tac >> gvs[] >>
  (* FIRST_PROVE gives each of the six goals its own timed step. *)
  FIRST_PROVE [metis_tac[typedMemoryCopyTheory.typed_copy_memory_size]]
QED

Theorem place_store_tuple_children_widen:
  !stys dtys dtvs.
    (stys = dtys \/ arg_types_fit stys dtys) /\
    OPT_MMAP (evaluate_type tenv) dtys = SOME dtvs ==>
    LIST_REL (type_widens_to tenv) stys dtys
Proof
  Induct >> Cases_on `dtys` >>
  simp[vyperTypeSystemTheory.arg_type_fits_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[type_widens_to_def, well_formed_type_def] >> metis_tac[]
QED

Theorem place_store_counted_tuple_entry:
  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      place_store_counted_entry cenv ctx cd cs cdt cst cv) ==>
    place_store_counted_entry cenv ctx (TupleT dtys) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  `?stys. sty = TupleT stys` by
    metis_tac[typedMemoryCopyTheory.typed_copy_tuple_widening] >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs(), vyperValueTheory.evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (irule place_store_tuple_children_widen >>
     conj_tac >- metis_tac[] >>
     drule typedMemoryCopyTheory.typed_copy_tuple_widening >> simp[]) >>
  `LIST_REL (\(dty,dtv) (sty,stv,v).
      type_memory_bytes cenv dty = type_memory_size dtv /\
      type_memory_bytes cenv sty = type_memory_size stv /\
      place_store_counted_entry cenv ctx dty sty dtv stv v)
      (ZIP (dtys,tvs')) (ZIP (stys,ZIP (tvs,l))) /\
   LENGTH dtys = LENGTH tvs' /\ LENGTH stys = LENGTH tvs /\ LENGTH tvs = LENGTH l` by
    (irule place_store_counted_fields_from_semantics >>
     (conj_tac >- gvs[valueEncodingDefsTheory.val_wf_def]) >>
     (conj_tac >- gvs[valueEncodingDefsTheory.val_wf_def]) >>
     (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
     qexists_tac `tenv` >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     rpt strip_tac >> first_x_assum irule >> simp[] >>
     metis_tac[typedCopyDomainTheory.member_rank_lt_tuple]) >>
  simp[place_store_counted_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    place_store_counted_tuple_path >> disch_then drule >>
  disch_then (qspecl_then [`func`, `s`, `dw`, `sw`] mp_tac) >>
  simp[valueEncodingTheory.type_memory_size_def, valueEncodingDefsTheory.val_in_memory_def] >>
  (impl_tac >- (gvs[valueEncodingDefsTheory.val_wf_def,
    valueEncodingTheory.type_memory_size_def, valueEncodingDefsTheory.val_in_memory_def,
    loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >> simp[]
QED

Theorem place_store_struct_tuple_values:
  !names tvs fields.
    LENGTH names = LENGTH tvs /\
    struct_has_type (ZIP (names,tvs)) fields /\
    fields_val_wf fields (ZIP (names,tvs)) ==>
    values_have_types tvs (MAP SND fields) /\
    tuple_val_wf (MAP SND fields) tvs /\
    LENGTH fields = LENGTH tvs /\ MAP FST fields = names
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fields` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def] >>
  PairCases_on `h'` >>
  simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def] >>
  rpt strip_tac >> first_x_assum drule >> disch_then drule_all >>
  strip_tac >> simp[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def]
QED

Theorem place_store_struct_layout:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields /\
    (!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv) ==>
    EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields /\
    SUM (MAP (SND o SND) fields) = type_memory_size_list tvs
Proof
  Induct >> simp[valueEncodingTheory.type_memory_size_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[AllCaseEqs(), valueEncodingTheory.type_memory_size_def] >>
  rpt strip_tac >> gvs[valueEncodingTheory.type_memory_size_def] >> metis_tac[]
QED

Theorem place_store_counted_struct_entry:
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      place_store_counted_entry cenv ctx cd cs cdt cst cv) ==>
    place_store_counted_entry cenv ctx (StructT name) sty dtv stv v
Proof
  rpt gen_tac >> strip_tac >>
  drule typedMemoryCopyTheory.typed_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def] >>
  `values_have_types tvs (MAP SND l) /\ tuple_val_wf (MAP SND l) tvs /\
   LENGTH l = LENGTH tvs /\ MAP FST l = MAP FST args` by
    metis_tac[place_store_struct_tuple_values, listTheory.LENGTH_MAP] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
  `LIST_REL (type_widens_to tenv) (MAP (FST o SND) fields)
      (MAP (FST o SND) fields)` by
    (irule place_store_tuple_children_widen >> simp[] >> metis_tac[]) >>
  `LIST_REL (\(dty,dtv) (sty,stv,v).
      type_memory_bytes cenv dty = type_memory_size dtv /\
      type_memory_bytes cenv sty = type_memory_size stv /\
      place_store_counted_entry cenv ctx dty sty dtv stv v)
      (ZIP (MAP (FST o SND) fields,tvs))
      (ZIP (MAP (FST o SND) fields,ZIP (tvs,MAP SND l))) /\
   LENGTH (MAP (FST o SND) fields) = LENGTH tvs /\
   LENGTH (MAP (FST o SND) fields) = LENGTH tvs /\ LENGTH tvs = LENGTH (MAP SND l)` by
    (irule place_store_counted_fields_from_semantics >> simp[] >>
     qexists_tac `tenv` >> gvs[vyperValueTheory.evaluate_types_OPT_MMAP] >>
     (conj_tac >- metis_tac[]) >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     `MEM cd (MAP (FST o SND) fields)` by metis_tac[] >>
     qpat_x_assum `MEM cd (MAP SND args)` kall_tac >>
     fs[listTheory.MEM_MAP] >> PairCases_on `y` >> gvs[] >>
     `MEM (y0,cd,y2) (get_struct_fields cenv.ce_struct_fields
         (nsid_to_string name))` by simp[get_struct_fields_def] >>
     drule_all typedCopyDomainTheory.member_rank_lt_struct >>
     simp[typedCopyDomainTheory.type_rank_def, nsid_to_string_def]) >>
  `EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields /\
   SUM (MAP (SND o SND) fields) = type_memory_size_list tvs` by
    (irule place_store_struct_layout >> qexists_tac `tenv` >> simp[] >>
     (conj_tac >- (rpt strip_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
       qexists_tac `tenv` >> simp[] >> metis_tac[])) >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST fields)` by metis_tac[] >>
  simp[place_store_counted_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, get_struct_fields_def] >> strip_tac >>
  `MAP (\(name,ty,sz). ty) fields = MAP (FST o SND) fields` by
    (irule listTheory.MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[typedMemoryCopyTheory.typed_copy_struct_fields_producer, listTheory.EVERY_MEM] >> strip_tac >>
  qpat_x_assum `LIST_REL _ (ZIP _) (ZIP _)` mp_tac >> simp[] >> strip_tac >>
  drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)
    place_store_counted_tuple_path >> disch_then drule >>
  disch_then (qspecl_then [`func`, `s`, `dw`, `sw`] mp_tac) >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (irule exprSimHypsTheory.struct_layout_size_zip >>
     pure_rewrite_tac[listTheory.LENGTH_MAP] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!cd cs cdt cst cv. _` kall_tac >>
  qpat_x_assum `!name fields. _` kall_tac >>
  qpat_x_assum `LIST_REL _ (ZIP _) (ZIP _)` kall_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE
    [valueEncodingTheory.type_memory_size_def, valueEncodingDefsTheory.val_in_memory_def,
     valueEncodingProofsTheory.fields_in_memory_tuple, loweringStateRelDefsTheory.regions_disjoint_def]) >>
  pure_rewrite_tac[valueEncodingTheory.type_memory_size_def,
      valueEncodingDefsTheory.val_in_memory_def, valueEncodingProofsTheory.fields_in_memory_tuple,
      listTheory.LENGTH_MAP, arithmeticTheory.ADD_0] >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by
    (qpat_x_assum `LENGTH args = LENGTH tvs` mp_tac >>
     simp[NoAsms, listTheory.MAP_ZIP]) >>
  qpat_x_assum `type_memory_size_fields _ = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> pure_rewrite_tac[th]) >>
  qpat_x_assum `MAP SND (ZIP _) = _` (fn th =>
    RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [NoAsms, th]) >>
    simp[NoAsms, th]) >>
  (impl_tac >- (rpt conj_tac >> metis_tac[arithmeticTheory.ADD_COMM])) >>
  strip_tac >> qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* compile_assign_value into (transient) storage, not a DynArray. *)
Theorem place_store_typed_rank_path:
  !n cenv tenv ctx dty sty dtv stv v.
    type_rank cenv.ce_struct_fields dty = n /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v ==>
    place_store_counted_entry cenv ctx dty sty dtv stv v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dty`
  >- (irule place_store_counted_word_entry >> simp[] >> qexists_tac `tenv` >> simp[]) >>
  Cases_on `is_bytestring_type dty` >- suspend "bytes" >>
  Cases_on `dty`
  >~ [`BaseT bt`]
  >- (Cases_on `bt` >> gvs[is_word_type_def, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_word_type_def, is_bytestring_type_def, evaluate_type_def, AllCaseEqs()])
  >~ [`ArrayT de db`]
  >- (Cases_on `db`
      >- (irule place_store_counted_sarray_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
          (conj_tac >- metis_tac[]) >> (rpt strip_tac >>
           qpat_x_assum `!k. k < _ ==> _`
             (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
           simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[])) >>
      irule place_store_counted_dynarray_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> (rpt strip_tac >>
           qpat_x_assum `!k. k < _ ==> _`
             (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
           simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]))
  >~ [`TupleT dtys`]
  >- (irule place_store_counted_tuple_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> (rpt strip_tac >>
           qpat_x_assum `!k. k < _ ==> _`
             (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
           simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[]))
  >~ [`StructT name`]
  >- (irule place_store_counted_struct_entry >> simp[] >> qexists_tac `tenv` >> simp[] >>
      (conj_tac >- metis_tac[]) >> (rpt strip_tac >>
           qpat_x_assum `!k. k < _ ==> _`
             (qspec_then `type_rank cenv.ce_struct_fields cd` mp_tac) >>
           simp[] >> disch_then irule >> simp[] >> qexists_tac `tenv` >> simp[] >> metis_tac[])) >>
  gvs[is_word_type_def, evaluate_type_def] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >> gvs[] >>
  simp[place_store_counted_entry_def] >> rpt strip_tac >>
  gvs[Once contextTheory.compile_store_memory_typed_def, is_word_type_def,
      is_bytestring_type_def, compileEnvTheory.type_memory_bytes_def,
      contextTheory.compile_copy_memory_def, comp_return_def] >>
  qexists_tac `s` >>
  simp[gas_marked_path_def, fragGasPathTheory.gas_path_rules,
       valueEncodingDefsTheory.val_in_memory_def,
       typedMemoryCopyTheory.typed_copy_state_frame_def,
       typedMemoryCopyTheory.typed_copy_frame_def, venom_state_component_equality]
QED

Resume place_store_typed_rank_path[bytes]:
  drule_all typedMemoryCopyTheory.typed_copy_bytestring_source >> strip_tac >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  simp[place_store_counted_entry_def] >> rpt strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def] >> strip_tac >>
  `!ty tv. is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
     (?cap. tv = BaseTV (BytesT (Dynamic cap))) \/
     (?cap. tv = BaseTV (StringT cap))` by
    (Cases >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (Cases_on `bd` >> rw[is_bytestring_type_def, evaluate_type_def]) >>
     rw[evaluate_type_def]) >>
  `(?cap. stv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. stv = BaseTV (StringT cap))` by metis_tac[] >>
  `(?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. dtv = BaseTV (StringT cap))` by metis_tac[] >>
  gvs[] >> Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  (irule place_store_bytestring_path >> simp[] >>
   goal_assum (drule_at (Pat `compile_store_bytestring _ _ _ = _`)) >>
   FIRST [rename1 `StringV str` >> qexistsl_tac [`STRLEN str`, `sw`],
          rename1 `BytesV bs` >> qexistsl_tac [`LENGTH bs`, `sw`]] >>
   gvs[valueEncodingDefsTheory.val_in_memory_def, loweringPostsTheory.val_footprint_def,
       valueEncodingTheory.type_memory_size_def] >>
   qmatch_goalsub_abbrev_tac `word_size len <= word_size capacity` >>
   `word_size len <= word_size capacity` by
     (irule exprSimHypsTheory.word_size_monotone >> simp[Abbr `len`]) >>
   qspec_then `len` assume_tac exprSimPropsTheory.le_word_size_mul >> decide_tac)
QED
Finalise place_store_typed_rank_path

Theorem place_store_memory_typed_path:
  !cenv tenv dst dty src sty dtv stv v sa sb ctx func s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((), sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `place_store_counted_entry cenv ctx dty sty dtv stv v` by
    (irule place_store_typed_rank_path >> simp[] >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `place_store_counted_entry _ _ _ _ _ _ _` mp_tac >>
  simp[place_store_counted_entry_def] >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`func`, `s`, `dw`, `sw`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists_tac `u` >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def] >> metis_tac[]
QED

(* Allocation plus the counted typed-copy path.  The source need not be
   contained in an old allocation: the assignment's future-allocation bound
   is sufficient, including when ALLOCA reuses an existing allocation. *)
Theorem place_store_normalize_path:
  !cenv cx ctx func es sa sm sc buf dty sty dtv stv v src sw s.
    compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
    compile_store_memory_typed cenv buf.buf_operand dty src sty sm = ((),sc) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
      w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t dw. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME dw /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      t.vs_labels = s.vs_labels /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa sm` by
    (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by gvs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  drule_all place_store_alloc_buffer_path >>
  disch_then (qx_choose_then `u` (qx_choose_then `w`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  qpat_x_assum `?p. buf.buf_operand = Var p /\ not_fresh_at sm p`
    strip_assume_tac >>
  `eval_operand src u = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `regions_disjoint (w2n sw) (type_memory_size stv)
     (w2n w) (type_memory_size dtv)` by
    (irule place_store_alloc_source_disjoint >>
     qexistsl_tac [`s`, `sa`] >> simp[Once ADD_COMM] >>
     rpt strip_tac >> qpat_x_assum `!aid b sz. _` drule_all >> simp[ADD_COMM]) >>
  `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
     simp[regions_disjoint_def]) >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    place_store_memory_typed_path >>
  disch_then (qspecl_then [`get_tenv cx`, `dtv`, `stv`, `v`] mp_tac) >>
  disch_then (qspecl_then [`ctx`, `func`, `u`, `w`, `sw`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `exprSimStorageCopy$copy_static t = exprSimStorageCopy$copy_static u` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[exprSimStorageCopyTheory.copy_static_def, venom_state_component_equality]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  `stmt_state_rel ctx func cenv cx es t` by suspend "state" >>
  qexistsl_tac [`t`, `w`] >> asm_rewrite_tac[] >>
  suspend "post"
QED
Resume place_store_normalize_path[state]:
  markerLib.RESUME_TAC >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `!name lb len. local_region cenv es.scopes u name lb len ==>
     w2n w + type_memory_size dtv <= lb \/ lb + len <= w2n w` by
    metis_tac[regions_disjoint_def] >>
  irule exprSimCopyTheory.copy_buffer_state_rel_frame >>
  qexistsl_tac [`w2n w`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
       [STRING #"%" (toString sa.cs_next_var)]`, `u`, `sm`, `type_memory_size dtv`] >>
  asm_rewrite_tac[mk_inst_def] >> simp[]
QED
Resume place_store_normalize_path[post]:
  markerLib.RESUME_TAC >>
  drule_all exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  asm_rewrite_tac[] >>
  simp[eval_operand_def] >> metis_tac[eval_operand_def]
QED
Finalise place_store_normalize_path

Theorem place_store_storage_destination:
  (loc = LocStorage \/ loc = LocTransient) /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  storage_place_region cx p ==>
  ?tr dtv mid var_name keys root tv path delta.
    p = StoragePlace tr w dtv /\ loc = slot_loc tr /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    declared_storage_region cx mid var_name keys = SOME (tr,root,tv) /\
    storage_subregion tv path delta dtv /\ w = root + n2w delta
Proof
  strip_tac >> Cases_on `p` >>
  gvs[place_ptr_rel_def, vyperStoragePlaceProvenanceTheory.storage_place_region_def] >>
  metis_tac[]
QED

Theorem place_store_storage_compile:
  (!et n. dty <> ArrayT et (Dynamic n)) /\
  compile_assign_value cenv dst (slot_loc tr) src (is_word_type dty)
    src_loc dty sty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
     | _ => NONE) (type_memory_bytes cenv dty) sa = ((), sb) ==>
  ?src' sc.
    (((~is_word_type dty /\ dty <> sty /\
       ~(is_bytestring_type dty /\ is_bytestring_type sty)) /\
      ?a sm. compile_alloc_buffer (type_memory_bytes cenv dty) sa = (a,sm) /\
        compile_store_memory_typed cenv a.buf_operand dty src sty sm = ((),sc) /\
        src' = a.buf_operand) \/
     ((is_word_type dty \/ dty = sty \/
       (is_bytestring_type dty /\ is_bytestring_type sty)) /\ src' = src /\ sc = sa)) /\
    (if is_word_type dty then
       emit_void (if tr then TSTORE else SSTORE) [dst;src'] sc = ((),sb)
     else if (if is_bytestring_type dty then type_memory_bytes cenv sty
              else type_memory_bytes cenv dty) <= 32 then
       ?loaded sd. emit_op MLOAD [src'] sc = (loaded,sd) /\
         emit_void (if tr then TSTORE else SSTORE) [dst;loaded] sd = ((),sb)
     else ?r. (if tr then compile_memory_to_transient else compile_memory_to_storage)
       src' dst ((if is_bytestring_type dty then type_memory_bytes cenv sty
                  else type_memory_bytes cenv dty) DIV 32) sc = (r,sb))
Proof
  strip_tac >>
  `!et bd. dty = ArrayT et bd ==> !n. bd <> Dynamic n` by metis_tac[] >>
  ` (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
     | _ => NONE) = NONE` by
    (Cases_on `dty` >> simp[] >> rename1 `ArrayT et bd` >>
     Cases_on `bd` >> gvs[]) >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `tr` >>
  simp[slot_loc_def, stmtLoweringTheory.compile_assign_value_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `~is_word_type dty /\ dty <> sty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty)` >>
  gvs[] >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_word_type dty` >> gvs[] >>
  Cases_on `(if is_bytestring_type dty then type_memory_bytes cenv sty
             else type_memory_bytes cenv dty) <= 32` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  IF_CASES_TAC >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

Theorem place_store_storage_replace:
  !ctx func cenv cx es s tr stor mt.
    stmt_state_rel ctx func cenv cx es s /\
    storage_agree (storage_dead cx tr stor) stor mt ==>
    stmt_state_rel ctx func cenv cx (set_storage cx es tr stor)
      (if tr then s with vs_transient :=
         (s.vs_call_ctx.cc_address =+ mt) s.vs_transient
       else s with vs_accounts :=
         (s.vs_call_ctx.cc_address =+
           (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage := mt))
           s.vs_accounts)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  Cases_on `tr` >>
  fs[stmt_state_rel_def, state_rel_def, vyperStorageBackendTheory.set_storage_def,
     accounts_rel_def, accounts_agree_def, transient_agree_def,
     storage_rel_def, transient_rel_def, contract_storage_def,
     contract_transient_def, vfmStateTheory.lookup_account_def,
     combinTheory.APPLY_UPDATE_THM] >>
  simp[local_ptrs_rel_def, local_backed_def, local_region_def,
     lookup_var_def, immutables_rel_def, logs_rel_def,
     venomMemDefsTheory.alloca_inv_def, alloca_room_def, pending_alloca_size_def,
     fmp_room_def, immutable_alloca_sep_def, immutable_base_zero_def,
     venomMemDefsTheory.allocas_non_overlapping_def,
     venomMemDefsTheory.alloca_next_valid_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (strip_assume_tac o SIMP_RULE (boss_ss())
      [local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def]) >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _`
    (assume_tac o SIMP_RULE (boss_ss()) [immutables_rel_def]) >>
  qpat_x_assum `logs_rel _ _ _ _`
    (strip_assume_tac o SIMP_RULE (boss_ss()) [logs_rel_def]) >>
  qpat_x_assum `alloca_inv _`
    (strip_assume_tac o SIMP_RULE (boss_ss())
      [venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def]) >>
  qpat_x_assum `alloca_room _ _ _`
    (strip_assume_tac o SIMP_RULE (boss_ss())
      [alloca_room_def, pending_alloca_size_def]) >>
  qpat_x_assum `fmp_room _ _ _`
    (assume_tac o SIMP_RULE (boss_ss())
      [fmp_room_def, pending_alloca_size_def]) >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
    (assume_tac o SIMP_RULE (boss_ss())
      [immutable_alloca_sep_def, local_region_def, lookup_var_def]) >>
  `es.accounts cx.txn.target with storage := mt =
   s.vs_accounts cx.txn.target with storage := mt` by
    (qpat_assum `es.accounts _ with storage := _ = _`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `immutable_base_zero _ _`
    (fn th => POP_ASSUM_LIST (K ALL_TAC) >> mp_tac th) >>
  simp[immutable_base_zero_def] >> strip_tac >>
  qx_gen_tac `operand` >> strip_tac >> Cases_on `operand` >>
  fs[eval_operand_def, lookup_var_def]
QED

Theorem place_store_root_layout:
  expr_sim_inv cenv cx env ee /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) ==>
  w2n rootk + type_slot_size root <= dimword (:256) /\
  (!mid' name' subs' k' tv'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
    (k',tv') <> (rootk,root) ==>
    ranges_disjoint (w2n rootk) (type_slot_size root)
                    (w2n k') (type_slot_size tv'))
Proof
  strip_tac >>
  `storage_layout_safe cx` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     simp[expr_sim_inv_def]) >>
  conj_tac
  >- (drule_all vyperStorageLayoutSafetyTheory.storage_layout_safe_region_nonoverflow >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  `(mid,name,subs) <> (mid',name',subs')` by
    (strip_tac >> gvs[]) >>
  drule_all vyperStorageLayoutSafetyTheory.storage_layout_safe_region_separation >>
  simp[]
QED

Theorem place_store_update_identity[local]:
  !a (f:'a -> 'b). (a =+ f a) f = f
Proof
  rpt gen_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `x = a` >> simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem place_store_encoded_leaf_state:
  !cenv cx env ee ctx func s mid name subs tr rootk root path delta tv
   start writes v n rd.
  expr_sim_inv cenv cx env ee /\
  stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\
  start = w2n rootk + delta /\ 0 < type_slot_size tv /\
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\ n <= type_slot_size tv /\
  (!i b. i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
       start tv (start+i) b ==>
    i < n /\
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (rd i) T)) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\t i. (if tr then tstore else sstore)
       (n2w (start+i)) (rd i) t) s (COUNT_LIST n))
Proof
  rpt gen_tac >> strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx ee tr))
    (get_storage cx ee tr)
    (if tr then contract_transient s else contract_storage s)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     Cases_on `tr` >>
     simp[stmt_state_rel_def, state_rel_def, accounts_rel_def,
          accounts_agree_def, transient_agree_def,
          vyperStorageBackendTheory.get_storage_def,
          vfmStateTheory.lookup_account_def,
          contract_storage_def, contract_transient_def,
          call_ctx_rel_def] >> metis_tac[]) >>
  drule_all place_store_root_layout >> strip_tac >>
  `storage_agree
    (storage_dead cx tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (apply_writes (n2w start) writes (get_storage cx ee tr))
    (FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
      (if tr then contract_transient s else contract_storage s) (COUNT_LIST n))` by
    (irule place_store_encoded_copy_agree >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     gvs[] >> metis_tac[]) >>
  `!is s. FOLDL (\t i. (if tr then tstore else sstore)
        (n2w (start+i)) (rd i) t) s is =
     if tr then s with vs_transient :=
       (s.vs_call_ctx.cc_address =+
         FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
           (contract_transient s) is) s.vs_transient
     else s with vs_accounts :=
       (s.vs_call_ctx.cc_address =+
         (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
           FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
             (contract_storage s) is)) s.vs_accounts` by
    (Induct
     >- (gen_tac >> pure_rewrite_tac[listTheory.FOLDL] >> Cases_on `tr` >>
         simp[contract_storage_def, contract_transient_def,
              vfmStateTheory.lookup_account_def, place_store_update_identity]) >>
     map_every qx_gen_tac [`h`, `acc`] >>
     once_rewrite_tac[listTheory.FOLDL] >>
     first_x_assum (qspec_then `(if tr then tstore else sstore)
       (n2w (start+h)) (rd h) acc` mp_tac) >>
     Cases_on `tr` >>
     simp[sstore_def, tstore_def, contract_storage_def, contract_transient_def,
          vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
          combinTheory.UPDATE_EQ]) >>
  drule_all place_store_storage_replace >> Cases_on `tr` >> gvs[]
QED

Theorem place_store_operand_update[local]:
  eval_operand op (update_var x v s) =
    if op = Var x then SOME v else eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def,
    emitHelperPropsTheory.lookup_var_update_var] >> metis_tac[]
QED

Theorem place_store_mload_update[local]:
  mload a (update_var x v s) = mload a s
Proof
  simp[mload_def, update_var_def]
QED

Theorem place_store_slot_operand_frame[local]:
  eval_operand op ((if tr then tstore else sstore) a v s) = eval_operand op s
Proof
  Cases_on `tr` >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, tstore_def, sstore_def]
QED

Theorem place_store_update_static[local]:
  (update_var x v s).vs_call_ctx.cc_static = s.vs_call_ctx.cc_static
Proof
  simp[update_var_def]
QED

(* The straight-line part of a forward-copy iteration, before its JMP. *)
Theorem place_store_forward_body_run:
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [cv;mv;sv;vv;dv;nv]) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var cv s = SOME k /\ ~s.vs_call_ctx.cc_static ==>
  let a = sw + k * 32w;
      w = mload (w2n a) s;
      s1 = update_var mv (k * 32w) s;
      s2 = update_var sv a s1;
      s3 = update_var vv w s2;
      s4 = update_var dv (dw + k) s3;
      s5 = (if tr then tstore else sstore) (dw + k) w s4;
      s6 = update_var nv (k + 1w) s5;
      s7 = update_var cv (k + 1w) s6
  in run_inst_seq
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) ADD [dst; Var cv] [dv];
     mk_inst (id+4) (if tr then TSTORE else SSTORE) [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s = OK s7
Proof
  strip_tac >> gvs[] >>
  `eval_operand (Var cv) s = SOME k` by simp[eval_operand_def] >>
  simp_tac (srw_ss()) [LET_THM] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
    exec_pure2_def, place_store_operand_update,
    emitHelperPropsTheory.eval_operand_lit] >>
  `src <> Var mv /\ src <> Var sv /\ src <> Var vv /\
   dst <> Var mv /\ dst <> Var sv /\ dst <> Var vv /\ dst <> Var dv` by metis_tac[] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
    place_store_operand_update] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_read1_def,
    place_store_operand_update, place_store_mload_update] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
    place_store_operand_update] >>
  (* One case per step: both cases together are too slow for one step. *)
  Cases_on `tr`
  >- (
    simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
      eval_operands_def, place_store_operand_update, place_store_update_static] >>
    qmatch_goalsub_abbrev_tac `run_inst_seq _ post` >>
    `eval_operand (Var cv) post = SOME k` by
      (simp[Abbr `post`, place_store_operand_update,
        SIMP_RULE (srw_ss()) [] (Q.INST [`tr` |-> `T`] place_store_slot_operand_frame),
        SIMP_RULE (srw_ss()) [] (Q.INST [`tr` |-> `F`] place_store_slot_operand_frame)]) >>
    simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
      emitHelperPropsTheory.eval_operand_lit] >>
    simp[run_inst_seq_def, step_inst_base_def, place_store_operand_update])
  >> (
    simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
      eval_operands_def, place_store_operand_update, place_store_update_static] >>
    qmatch_goalsub_abbrev_tac `run_inst_seq _ post` >>
    `eval_operand (Var cv) post = SOME k` by
      (simp[Abbr `post`, place_store_operand_update,
        SIMP_RULE (srw_ss()) [] (Q.INST [`tr` |-> `T`] place_store_slot_operand_frame),
        SIMP_RULE (srw_ss()) [] (Q.INST [`tr` |-> `F`] place_store_slot_operand_frame)]) >>
    simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
      emitHelperPropsTheory.eval_operand_lit] >>
    simp[run_inst_seq_def, step_inst_base_def, place_store_operand_update])
QED

(* Forward-copy layout shares names, initialization and test with slot copying.
   Only the body order and load/store direction differ. *)
Definition place_store_copy_body_insts_def:
  place_store_copy_body_insts cs src dst tr =
    [mk_inst (cs.cs_next_id + 4) MUL
       [Var (slot_copy_var cs 0); Lit 32w] [slot_copy_var cs 2];
     mk_inst (cs.cs_next_id + 5) ADD [src; Var (slot_copy_var cs 2)]
       [slot_copy_var cs 3];
     mk_inst (cs.cs_next_id + 6) MLOAD [Var (slot_copy_var cs 3)]
       [slot_copy_var cs 4];
     mk_inst (cs.cs_next_id + 7) ADD [dst; Var (slot_copy_var cs 0)]
       [slot_copy_var cs 5];
     mk_inst (cs.cs_next_id + 8) (if tr then TSTORE else SSTORE)
       [Var (slot_copy_var cs 5); Var (slot_copy_var cs 4)] [];
     mk_inst (cs.cs_next_id + 9) ADD [Var (slot_copy_var cs 0); Lit 1w]
       [slot_copy_var cs 6];
     mk_inst (cs.cs_next_id + 10) ASSIGN [Var (slot_copy_var cs 6)]
       [slot_copy_var cs 0];
     mk_inst (cs.cs_next_id + 11) JMP [Label (slot_copy_cond cs)] []]
End

Definition place_store_copy_blocks_def:
  place_store_copy_blocks cs src dst n tr =
    [<|bb_label := slot_copy_body cs;
       bb_instructions := place_store_copy_body_insts cs src dst tr|>;
     <|bb_label := slot_copy_cond cs;
       bb_instructions := slot_copy_cond_insts cs n|>;
     <|bb_label := cs.cs_current_bb;
       bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>]
End

Definition place_store_copy_final_def:
  place_store_copy_final cs src dst n tr =
    cs with <|cs_next_label := cs.cs_next_label + 3;
              cs_next_var := cs.cs_next_var + 7;
              cs_next_id := cs.cs_next_id + 12;
              cs_blocks := place_store_copy_blocks cs src dst n tr ++ cs.cs_blocks;
              cs_current_bb := slot_copy_exit cs;
              cs_current_insts := []|>
End

Theorem place_store_copy_shape:
  compile_word_copy_loop src dst n LocMemory
    (if tr then LocTransient else LocStorage) F cs =
  (slot_copy_body cs, place_store_copy_final cs src dst n tr)
Proof
  Cases_on `tr` >>
  simp[contextTheory.compile_word_copy_loop_def, contextTheory.compile_word_copy_loop_op_def, contextTheory.compile_word_copy_loop_base_def, word_scale_def,
       contextTheory.compile_ptr_load_def, contextTheory.compile_ptr_store_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emitHelperTheory.emit_inst_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def, emit_def, new_block_def,
       place_store_copy_final_def, place_store_copy_blocks_def,
       place_store_copy_body_insts_def, slot_copy_init_insts_def,
       slot_copy_cond_insts_def, slot_copy_var_def,
       slot_copy_body_def, slot_copy_cond_def, slot_copy_exit_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> REFL_TAC
QED

Theorem place_store_copy_boundary:
  compile_word_copy_loop src dst n LocMemory
    (if tr then LocTransient else LocStorage) F cs = (result,cs') ==>
  result = slot_copy_body cs /\
  cs' = place_store_copy_final cs src dst n tr /\
  cs_extends cs cs' /\
  cs'.cs_current_bb = slot_copy_exit cs /\
  cs'.cs_current_insts = [] /\
  cs'.cs_next_var = cs.cs_next_var + 7 /\
  cs'.cs_next_label = cs.cs_next_label + 3 /\
  cs'.cs_next_id = cs.cs_next_id + 12
Proof
  simp[place_store_copy_shape] >> strip_tac >> gvs[] >>
  simp[cs_extends_def, place_store_copy_final_def,
       place_store_copy_blocks_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem place_store_copy_lookup:
  fn_has_code cs (place_store_copy_final cs src dst n tr) fn ==>
  lookup_block (slot_copy_body cs) fn.fn_blocks =
    SOME <|bb_label := slot_copy_body cs;
           bb_instructions := place_store_copy_body_insts cs src dst tr|> /\
  lookup_block (slot_copy_cond cs) fn.fn_blocks =
    SOME <|bb_label := slot_copy_cond cs;
           bb_instructions := slot_copy_cond_insts cs n|> /\
  lookup_block cs.cs_current_bb fn.fn_blocks =
    SOME <|bb_label := cs.cs_current_bb;
           bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|> /\
  ?bb. lookup_block (slot_copy_exit cs) fn.fn_blocks = SOME bb
Proof
  simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
       place_store_copy_final_def,
       place_store_copy_blocks_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem place_store_copy_old_var:
  not_fresh_at cs x ==> x <> slot_copy_var cs k
Proof
  simp[not_fresh_at_def, slot_copy_var_def] >> strip_tac >>
  first_x_assum (qspec_then `cs.cs_next_var + k` mp_tac) >> simp[]
QED

(* Finite control-flow boundaries for the forward slot-copy loop. *)
Theorem place_store_copy_jump_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_marked_path F ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_edge ctx func s 0 (OK (jump_to lbl s))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def,
          is_terminator_def] >>
     metis_tac[]) >>
  simp[gas_marked_path_def] >>
  metis_tac[gas_path_rules, gas_path_edge_normal, ADD_0]
QED

Theorem place_store_copy_entry_path:
  fn_has_code cs (place_store_copy_final cs src dst n tr) func /\
  ~s.vs_halted /\ s.vs_current_bb = cs.cs_current_bb /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to (slot_copy_cond cs) (update_var (slot_copy_var cs 0) 0w s)))
Proof
  strip_tac >> drule place_store_copy_lookup >> strip_tac >>
  `get_instruction
     <|bb_label := cs.cs_current_bb;
       bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>
     s.vs_inst_idx =
     SOME (mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0])` by
    simp[get_instruction_def, slot_copy_init_insts_def, listTheory.EL_APPEND_EQN] >>
  `step_inst_base
     (mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0]) s =
     OK (update_var (slot_copy_var cs 0) 0w s)` by
    simp[step_inst_base_def, mk_inst_def, exec_read1_def,
         eval_operands_def, eval_operand_def] >>
  `gas_path_edge ctx func s 0
     (OK ((update_var (slot_copy_var cs 0) 0w s)
       with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `get_instruction _ _ = _`) tuple_straight_line_edge >>
     simp[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_edge ctx func s 0 (OK u)` >>
  `gas_marked_path F ctx func u 0 (OK (jump_to (slot_copy_cond cs) u))` by
    (irule place_store_copy_jump_path >>
     (conj_tac >- simp[Abbr `u`, update_var_def]) >>
     qexistsl_tac
       [`<|bb_label := cs.cs_current_bb;
           bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>`,
        `mk_inst (cs.cs_next_id + 1) JMP [Label (slot_copy_cond cs)] []`] >>
     simp[Abbr `u`, update_var_def, get_instruction_def,
          slot_copy_init_insts_def, listTheory.EL_APPEND_EQN,
          step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  `jump_to (slot_copy_cond cs) u =
   jump_to (slot_copy_cond cs) (update_var (slot_copy_var cs 0) 0w s)` by
    simp[Abbr `u`, jump_to_def] >>
  gvs[gas_marked_path_def] >>
  metis_tac[gas_path_rules, ADD_0]
QED

Theorem place_store_copy_test_path:
  fn_has_code cs (place_store_copy_final cs src dst n tr) func /\
  ~s.vs_halted /\ s.vs_current_bb = slot_copy_cond cs /\ s.vs_inst_idx = 0 /\
  lookup_var (slot_copy_var cs 0) s = SOME (n2w k) /\
  k <= n /\ n < dimword (:256) ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to (if k = n then slot_copy_exit cs else slot_copy_body cs)
      (update_var (slot_copy_var cs 1) (bool_to_word (k = n)) s)))
Proof
  strip_tac >> drule place_store_copy_lookup >> strip_tac >>
  `n2w k = (n2w n : 256 word) <=> k = n` by
    (`k < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.dimword_def] >>
     simp_tac (srw_ss()) [wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]) >>
  `get_instruction
     <|bb_label := slot_copy_cond cs; bb_instructions := slot_copy_cond_insts cs n|>
     s.vs_inst_idx = SOME (mk_inst (cs.cs_next_id + 2) EQ
       [Var (slot_copy_var cs 0); Lit (n2w n)] [slot_copy_var cs 1])` by
    simp[get_instruction_def, slot_copy_cond_insts_def] >>
  `step_inst_base (mk_inst (cs.cs_next_id + 2) EQ
     [Var (slot_copy_var cs 0); Lit (n2w n)] [slot_copy_var cs 1]) s =
     OK (update_var (slot_copy_var cs 1) (bool_to_word (k = n)) s)` by
    simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
         eval_operands_def, eval_operand_def] >>
  `gas_path_edge ctx func s 0
     (OK ((update_var (slot_copy_var cs 1) (bool_to_word (k = n)) s)
       with vs_inst_idx := 1))` by
    (drule_at (Pat `get_instruction _ _ = _`) tuple_straight_line_edge >>
     simp[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `gas_path_edge ctx func s 0 (OK u)` >>
  `gas_marked_path F ctx func u 0
     (OK (jump_to (if k = n then slot_copy_exit cs else slot_copy_body cs) u))` by
    (irule place_store_copy_jump_path >>
     (conj_tac >- simp[Abbr `u`, update_var_def]) >>
     qexistsl_tac
       [`<|bb_label := slot_copy_cond cs; bb_instructions := slot_copy_cond_insts cs n|>`,
        `mk_inst (cs.cs_next_id + 3) JNZ
           [Var (slot_copy_var cs 1); Label (slot_copy_exit cs);
            Label (slot_copy_body cs)] []`] >>
     Cases_on `k = n`
     >- simp[Abbr `u`, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
             get_instruction_def, slot_copy_cond_insts_def, step_inst_base_def,
             mk_inst_def, eval_operand_def, bool_to_word_def, jump_to_def] >>
     simp[Abbr `u`, update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          get_instruction_def, slot_copy_cond_insts_def, step_inst_base_def,
          mk_inst_def, eval_operand_def, bool_to_word_def, jump_to_def]) >>
  `jump_to (if k = n then slot_copy_exit cs else slot_copy_body cs) u =
   jump_to (if k = n then slot_copy_exit cs else slot_copy_body cs)
     (update_var (slot_copy_var cs 1) (bool_to_word (k = n)) s)` by
    simp[Abbr `u`, jump_to_def] >>
  gvs[gas_marked_path_def] >> metis_tac[gas_path_rules, ADD_0]
QED

Theorem place_store_copy_body_path:
  fn_has_code cs (place_store_copy_final cs src dst n tr) func /\
  ~s.vs_halted /\ s.vs_current_bb = slot_copy_body cs /\ s.vs_inst_idx = 0 /\
  run_inst_seq (TAKE 7 (place_store_copy_body_insts cs src dst tr)) s = OK t ==>
  gas_marked_path F ctx func s 0 (OK (jump_to (slot_copy_cond cs) t))
Proof
  strip_tac >> drule place_store_copy_lookup >> strip_tac >>
  `gas_path ctx func s 0 (OK (t with vs_inst_idx := 7))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) tuple_run_inst_seq_gas_path >>
     disch_then (qspecl_then
       [`ctx`, `func`,
        `<|bb_label := slot_copy_body cs;
           bb_instructions := place_store_copy_body_insts cs src dst tr|>`] mp_tac) >>
     Cases_on `tr` >>
     simp[place_store_copy_body_insts_def, mk_inst_def, is_terminator_def,
          rich_listTheory.IS_PREFIX_APPEND]) >>
  `~t.vs_halted` by
    (drule gas_path_normal >> simp[]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\u:venom_state. u.vs_current_bb` run_inst_seq_preserves_field)) >>
     goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (Cases_on `tr` >> gvs[place_store_copy_body_insts_def, mk_inst_def, is_terminator_def]) >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     metis_tac[venomInstProofsTheory.step_preserves_control_flow]) >>
  `gas_marked_path F ctx func (t with vs_inst_idx := 7) 0
     (OK (jump_to (slot_copy_cond cs) (t with vs_inst_idx := 7)))` by
    (irule place_store_copy_jump_path >> (conj_tac >- simp[]) >>
     qexistsl_tac
       [`<|bb_label := slot_copy_body cs;
           bb_instructions := place_store_copy_body_insts cs src dst tr|>`,
        `mk_inst (cs.cs_next_id + 11) JMP [Label (slot_copy_cond cs)] []`] >>
     simp[get_instruction_def, place_store_copy_body_insts_def,
          step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  gvs[gas_marked_path_def, jump_to_def] >>
  metis_tac[gas_path_then, ADD_0]
QED

Theorem place_store_copy_iteration_path:
  fn_has_code cs (place_store_copy_final cs src dst n tr) func /\
  ~s.vs_halted /\ s.vs_current_bb = slot_copy_body cs /\ s.vs_inst_idx = 0 /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at cs x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var (slot_copy_var cs 0) s = SOME k /\ ~s.vs_call_ctx.cc_static ==>
  let a = sw + k * 32w; w = mload (w2n a) s;
      s1 = update_var (slot_copy_var cs 2) (k * 32w) s;
      s2 = update_var (slot_copy_var cs 3) a s1;
      s3 = update_var (slot_copy_var cs 4) w s2;
      s4 = update_var (slot_copy_var cs 5) (dw + k) s3;
      s5 = (if tr then tstore else sstore) (dw + k) w s4;
      s6 = update_var (slot_copy_var cs 6) (k + 1w) s5;
      s7 = update_var (slot_copy_var cs 0) (k + 1w) s6
  in gas_marked_path F ctx func s 0 (OK (jump_to (slot_copy_cond cs) s7))
Proof
  strip_tac >> simp_tac pure_ss [LET_THM] >>
  irule place_store_copy_body_path >>
  simp[] >> goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >> simp[] >>
  simp_tac (srw_ss()) [place_store_copy_body_insts_def] >>
  `ALL_DISTINCT [slot_copy_var cs 0; slot_copy_var cs 2;
     slot_copy_var cs 3; slot_copy_var cs 4; slot_copy_var cs 5;
     slot_copy_var cs 6]` by
    simp[slot_copy_var_def, listTheory.ALL_DISTINCT, ASCIInumbersTheory.toString_inj] >>
  `!x. src = Var x \/ dst = Var x ==>
     ~MEM x [slot_copy_var cs 0; slot_copy_var cs 2;
       slot_copy_var cs 3; slot_copy_var cs 4; slot_copy_var cs 5;
       slot_copy_var cs 6]` by
    (rpt strip_tac >> gvs[listTheory.MEM] >> metis_tac[place_store_copy_old_var]) >>
  drule_all place_store_forward_body_run >>
  disch_then (qspecl_then [`tr`, `cs.cs_next_id + 4`] mp_tac) >>
  simp[LET_THM]
QED

Theorem place_store_update_projections[local]:
  (update_var x w s).vs_memory = s.vs_memory /\
  (update_var x w s).vs_call_ctx = s.vs_call_ctx /\
  (update_var x w s).vs_halted = s.vs_halted /\
  (update_var x w s).vs_current_bb = s.vs_current_bb /\
  (update_var x w s).vs_inst_idx = s.vs_inst_idx
Proof
  simp[update_var_def]
QED

Theorem place_store_jump_projections[local]:
  (jump_to l s).vs_memory = s.vs_memory /\
  (jump_to l s).vs_allocas = s.vs_allocas /\
  (jump_to l s).vs_call_ctx = s.vs_call_ctx /\
  (jump_to l s).vs_halted = s.vs_halted /\
  (jump_to l s).vs_current_bb = l /\
  (jump_to l s).vs_inst_idx = 0 /\
  lookup_var x (jump_to l s) = lookup_var x s
Proof
  simp[jump_to_def, lookup_var_def]
QED

Theorem place_store_slot_projections[local]:
  ((if tr then tstore else sstore) k w s).vs_memory = s.vs_memory /\
  ((if tr then tstore else sstore) k w s).vs_allocas = s.vs_allocas /\
  ((if tr then tstore else sstore) k w s).vs_call_ctx = s.vs_call_ctx /\
  ((if tr then tstore else sstore) k w s).vs_halted = s.vs_halted /\
  ((if tr then tstore else sstore) k w s).vs_current_bb = s.vs_current_bb /\
  ((if tr then tstore else sstore) k w s).vs_inst_idx = s.vs_inst_idx /\
  lookup_var x ((if tr then tstore else sstore) k w s) = lookup_var x s
Proof
  Cases_on `tr` >> simp[sstore_def, tstore_def, lookup_var_def]
QED

Theorem place_store_copy_framed_step:
  fn_has_code cs (place_store_copy_final cs src dst n tr) func /\
  ~q.vs_halted /\ q.vs_current_bb = slot_copy_cond cs /\ q.vs_inst_idx = 0 /\
  lookup_var (slot_copy_var cs 0) q = SOME (n2w i) /\ i < n /\
  n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at cs x) /\
  eval_operand src q = SOME sw /\ eval_operand dst q = SOME dw /\
  ~q.vs_call_ctx.cc_static /\ q.vs_memory = s.vs_memory /\
  store_copy_frame cs (if tr then LocTransient else LocStorage) sw dw s i q ==>
  ?t. gas_marked_path F ctx func q 0 (OK t) /\
      store_copy_frame cs (if tr then LocTransient else LocStorage) sw dw s (SUC i) t /\
      (!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x q) /\
      t.vs_memory = q.vs_memory /\ t.vs_allocas = q.vs_allocas /\
      t.vs_call_ctx = q.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = slot_copy_cond cs /\ t.vs_inst_idx = 0 /\
      lookup_var (slot_copy_var cs 0) t = SOME (n2w (SUC i))
Proof
  strip_tac >>
  qabbrev_tac `u = jump_to (slot_copy_body cs)
    (update_var (slot_copy_var cs 1) 0w q)` >>
  `i <= n /\ i <> n` by decide_tac >>
  `gas_marked_path F ctx func q 0 (OK u)` by
    (drule_all place_store_copy_test_path >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[Abbr `u`, bool_to_word_def]) >>
  `(!x. src = Var x \/ dst = Var x ==> x <> slot_copy_var cs 1)` by
    metis_tac[place_store_copy_old_var] >>
  `eval_operand src u = SOME sw /\ eval_operand dst u = SOME dw /\
   lookup_var (slot_copy_var cs 0) u = SOME (n2w i) /\
   ~u.vs_halted /\ u.vs_current_bb = slot_copy_body cs /\
   u.vs_inst_idx = 0 /\ ~u.vs_call_ctx.cc_static` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[Abbr `u`, jump_to_def, update_var_def, eval_operand_def,
         lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
         slot_copy_var_def, ASCIInumbersTheory.toString_inj]) >>
  drule_all place_store_copy_iteration_path >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac pure_ss [LET_THM] >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func u 0 (OK t)` >>
  qexists_tac `t` >>
  (conj_tac >- (drule_all gas_marked_path_then >> simp[])) >>
  `!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x q` by
    (rpt strip_tac >>
     `!k. x <> slot_copy_var cs k` by metis_tac[place_store_copy_old_var] >>
     Cases_on `tr` >>
     simp[Abbr `t`, Abbr `u`, jump_to_def, update_var_def,
          sstore_def, tstore_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  (conj_tac >-
    (pure_rewrite_tac[arithmeticTheory.ADD1] >>
     irule place_store_copy_frame_chunk >> qexists_tac `q` >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `t`, Abbr `u`, store_copy_normalize_def, jump_to_def,
          update_var_def, sstore_def, tstore_def, mload_def])) >>
  simp[Abbr `t`, Abbr `u`, place_store_jump_projections,
       place_store_update_projections, place_store_slot_projections,
       allocaFootprintTheory.update_var_fields,
       emitHelperPropsTheory.lookup_var_update_var, wordsTheory.n2w_SUC]
QED

Theorem place_store_copy_frame_observations:
  store_copy_frame cs loc sw dw s i q ==>
  q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
  q.vs_labels = s.vs_labels /\ q.vs_call_ctx = s.vs_call_ctx /\
  q.vs_halted = s.vs_halted
Proof
  `!i. (store_copy_prefix loc sw dw s i).vs_memory = s.vs_memory /\
       (store_copy_prefix loc sw dw s i).vs_allocas = s.vs_allocas /\
       (store_copy_prefix loc sw dw s i).vs_labels = s.vs_labels /\
       (store_copy_prefix loc sw dw s i).vs_call_ctx = s.vs_call_ctx /\
       (store_copy_prefix loc sw dw s i).vs_halted = s.vs_halted` by
    (Induct >- simp[store_copy_prefix_def, rich_listTheory.COUNT_LIST_def] >>
     pure_rewrite_tac[store_copy_prefix_def, rich_listTheory.COUNT_LIST_SNOC,
                      listTheory.FOLDL_SNOC] >>
     pure_rewrite_tac[GSYM store_copy_prefix_def] >>
     Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]) >>
  strip_tac >> gvs[store_copy_frame_def] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  qpat_x_assum `store_copy_normalize _ _ = _` (SUBST1_TAC o SYM) >>
  simp[store_copy_normalize_def]
QED

Theorem place_store_copy_frame_operand[local]:
  store_copy_frame cs loc sw dw s i q /\
  (!x. op = Var x ==> not_fresh_at cs x) ==>
  eval_operand op q = eval_operand op s
Proof
  strip_tac >> drule place_store_copy_frame_observations >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def, store_copy_frame_def]
QED

Theorem place_store_copy_condition_run:
  fn_has_code cs (place_store_copy_final cs src dst n tr) func /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at cs x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  n < dimword (:256) /\ i <= n /\
  store_copy_frame cs (if tr then LocTransient else LocStorage) sw dw s i q /\
  q.vs_current_bb = slot_copy_cond cs /\ q.vs_inst_idx = 0 /\
  lookup_var (slot_copy_var cs 0) q = SOME (n2w i) ==>
  ?t. gas_marked_path F ctx func q 0 (OK t) /\
      store_copy_frame cs (if tr then LocTransient else LocStorage) sw dw s n t /\
      ~t.vs_halted /\ t.vs_current_bb = slot_copy_exit cs /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  qabbrev_tac `copy_inv = \j u.
    j <= n /\ store_copy_frame cs (if tr then LocTransient else LocStorage) sw dw s j u /\
    u.vs_current_bb = slot_copy_cond cs /\ u.vs_inst_idx = 0 /\
    lookup_var (slot_copy_var cs 0) u = SOME (n2w j)` >>
  `!j u. copy_inv j u ==> ~u.vs_halted` by
    (simp[Abbr `copy_inv`] >> metis_tac[place_store_copy_frame_observations]) >>
  `!j u. j < n /\ copy_inv j u ==>
    ?r. gas_marked_path F ctx func u 0 (OK r) /\ copy_inv (SUC j) r` by
    (simp[Abbr `copy_inv`] >> rpt strip_tac >>
     drule place_store_copy_frame_observations >> strip_tac >>
     `eval_operand src u = SOME sw /\ eval_operand dst u = SOME dw` by
       metis_tac[place_store_copy_frame_operand] >>
     `~u.vs_halted /\ ~u.vs_call_ctx.cc_static` by simp[] >>
     drule_all place_store_copy_framed_step >>
     disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
     qexists_tac `t` >> simp[] >> decide_tac) >>
  `copy_inv i q` by simp[Abbr `copy_inv`] >>
  drule_all place_store_counted_iterate >> strip_tac >>
  rename1 `copy_inv n r` >>
  `~r.vs_halted` by metis_tac[] >>
  fs[Abbr `copy_inv`] >>
  qabbrev_tac `t = jump_to (slot_copy_exit cs)
    (update_var (slot_copy_var cs 1) 1w r)` >>
  `n <= n /\ n < dimword (:256)` by simp[] >>
  `gas_marked_path F ctx func r 0 (OK t)` by
    (drule_all place_store_copy_test_path >>
     disch_then (qspec_then `ctx` mp_tac) >>
     simp[Abbr `t`, bool_to_word_def]) >>
  qexists_tac `t` >>
  (conj_tac >- (drule_all gas_marked_path_then >> simp[])) >>
  (conj_tac >-
    (`n = n + 0` by simp[] >>
     pop_assum SUBST1_TAC >>
     irule place_store_copy_frame_chunk >> qexists_tac `r` >>
     simp[Abbr `t`, store_copy_normalize_def, update_var_def, jump_to_def] >>
     rpt strip_tac >>
     `x <> slot_copy_var cs 1` by metis_tac[place_store_copy_old_var] >>
     simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE])) >>
  simp[Abbr `t`, place_store_jump_projections, place_store_update_projections]
QED

Theorem place_store_copy_framed_run:
  fn_has_code cs (place_store_copy_final cs src dst n tr) func /\
  ~s.vs_halted /\ s.vs_current_bb = cs.cs_current_bb /\
  s.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at cs x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  n < dimword (:256) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_frame cs (if tr then LocTransient else LocStorage) sw dw s n t /\
      (!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\
      ~t.vs_halted /\
      t.vs_current_bb = (place_store_copy_final cs src dst n tr).cs_current_bb /\
      t.vs_inst_idx = LENGTH (place_store_copy_final cs src dst n tr).cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `q = jump_to (slot_copy_cond cs)
    (update_var (slot_copy_var cs 0) 0w s)` >>
  `gas_marked_path F ctx func s 0 (OK q)` by
    (simp[Abbr `q`] >> irule place_store_copy_entry_path >> simp[] >>
     goal_assum (drule_at (Pat `fn_has_code _ _ _`))) >>
  `store_copy_frame cs (if tr then LocTransient else LocStorage) sw dw s 0 q` by
    (simp[store_copy_frame_def, store_copy_prefix_def, rich_listTheory.COUNT_LIST_def,
          Abbr `q`, store_copy_normalize_def, jump_to_def, update_var_def] >>
     (conj_tac >-
       (rpt strip_tac >>
        `x <> slot_copy_var cs 0` by metis_tac[place_store_copy_old_var] >>
        simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE])) >>
     simp[venom_state_component_equality]) >>
  `q.vs_current_bb = slot_copy_cond cs /\ q.vs_inst_idx = 0 /\
   lookup_var (slot_copy_var cs 0) q = SOME (n2w 0) /\ 0 <= n` by
    simp[Abbr `q`, place_store_jump_projections, emitHelperPropsTheory.lookup_var_update_var] >>
  drule_all place_store_copy_condition_run >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `t` >>
  (conj_tac >- (drule_all gas_marked_path_then >> simp[])) >>
  drule place_store_copy_frame_observations >> strip_tac >>
  gvs[place_store_copy_final_def, store_copy_frame_def]
QED

Theorem place_store_memory_to_slots_path:
  (if tr then compile_memory_to_transient else compile_memory_to_storage)
    src dst n sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  n < dimword (:256) /\ w2n sw + 32*n < dimword (:256) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32*j) s) q) s (COUNT_LIST n) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `compile_word_copy_loop src dst n LocMemory
     (if tr then LocTransient else LocStorage) F sa = (result,sb)` by
    (Cases_on `tr` >> gvs[contextTheory.compile_memory_to_transient_def,
                          contextTheory.compile_memory_to_storage_def]) >>
  drule place_store_copy_boundary >> strip_tac >> gvs[] >>
  `n < dimword (:256)` by (simp[] >> decide_tac) >>
  drule_all place_store_copy_framed_run >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  drule place_store_copy_frame_observations >> strip_tac >> simp[] >>
  fs[store_copy_frame_def, store_copy_prefix_def] >>
  irule listTheory.FOLDL_CONG >> simp[] >>
  simp[rich_listTheory.MEM_COUNT_LIST] >> rpt strip_tac >>
  `32*x + w2n sw < dimword (:256)` by (simp[] >> decide_tac) >>
  `sw + n2w x * 32w = n2w (32*x + w2n sw)` by
    simp[GSYM wordsTheory.word_add_n2w, GSYM wordsTheory.word_mul_n2w,
         wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_MULT_COMM] >>
  Cases_on `tr` >> simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

(* The allocation-limit check bounds the natural size, before n2w. *)
(* Restore execution cursor fields after reasoning about a normalized suffix. *)
Theorem place_store_stmt_cursor:
  stmt_state_rel ctx func cenv cx es
    (s with <|vs_current_bb := bb; vs_prev_bb := prev; vs_inst_idx := idx|>) <=>
  stmt_state_rel ctx func cenv cx es s
Proof
  `fmp_room ctx func
    (s with <|vs_current_bb := bb; vs_prev_bb := prev; vs_inst_idx := idx|>) <=>
   fmp_room ctx func s` by
    (irule exprLoweringPropsTheory.fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def,
       exprLoweringPropsTheory.immutable_base_zero_alt,
       accounts_rel_def, accounts_agree_def]
QED

Theorem place_store_normalized_stmt_state:
  stmt_state_rel ctx func cenv cx es (store_copy_normalize s t) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (t with vs_vars := s.vs_vars)` by
    (`store_copy_normalize s t =
       (t with vs_vars := s.vs_vars) with
         <|vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb;
           vs_inst_idx := s.vs_inst_idx|>` by
       simp[store_copy_normalize_def] >>
     qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     asm_rewrite_tac[place_store_stmt_cursor]) >>
  `stmt_state_rel ctx func cenv cx es
     ((t with vs_vars := s.vs_vars) with vs_vars := t.vs_vars)` suffices_by
    simp[] >>
  irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >>
  fs[local_ptrs_reserved_def] >> rpt strip_tac >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

Theorem place_store_emit_slot_path:
  emit_void (if tr then TSTORE else SSTORE) [dst;src] sa = ((),sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME w ==>
  gas_marked_path F ctx func s 0
    (OK (((if tr then tstore else sstore) dw w s)
      with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  sb.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  reverse conj_tac >- simp[] >>
  irule place_store_emitted_seq_path >> conj_tac >- simp[] >>
  qexists_tac `sa` >>
  Cases_on `tr`
  >- simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
          step_inst_base_def, exec_write2_def, eval_operands_def] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_def, exec_write2_def, eval_operands_def]
QED

(* Counted suffix execution consumes only the live part of the encoded leaf.
   In particular n need not cover dead destination capacity words. *)
Theorem place_store_memory_leaf_run:
  (if tr then compile_memory_to_transient else compile_memory_to_storage)
    src dst n sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  n < dimword (:256) /\ w2n sw + 32*n < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\ n <= type_slot_size tv /\
  (!i b. i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
       start tv (start+i) b ==>
    i < n /\
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (mload (w2n sw + 32*i) s) T)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx
        (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all (BETA_RULE (Q.INST [`rd` |-> `\i. mload (w2n sw + 32*i) s`]
    (SPEC_ALL place_store_encoded_leaf_state))) >> strip_tac >>
  drule_all place_store_memory_to_slots_path >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> simp[] >>
  qpat_x_assum `store_copy_normalize _ _ = _` SUBST1_TAC >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  qpat_x_assum `start = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac bool_ss [GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
    AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM,
    arithmeticTheory.ADD_COMM]
QED

Theorem place_store_storage_write_inv:
  write_place cx (StoragePlace tr k tv) v ee = (INL (),ff) /\
  stmt_state_rel ctx func cenv cx ee s ==>
  ?writes. encode_value tv v = SOME writes /\
    ff = set_storage cx ee tr (apply_writes k writes (get_storage cx ee tr)) /\
    ~s.vs_call_ctx.cc_static
Proof
  strip_tac >>
  fs[write_place_def, vyperStorageBackendTheory.write_storage_slot_eq,
     AllCaseEqs()] >>
  fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]
QED

Theorem place_store_storage_leaf_bounds:
  expr_sim_inv cenv cx env ee /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ 0 < type_slot_size tv ==>
  w2n rootk + delta + type_slot_size tv <= dimword (:256) /\
  w2n (rootk + n2w delta) = w2n rootk + delta
Proof
  strip_tac >> drule_all place_store_root_layout >> strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `w2n rootk + delta + type_slot_size tv <= dimword (:256)` by decide_tac >>
  `w2n rootk + delta < dimword (:256)` by decide_tac >>
  simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
       arithmeticTheory.MOD_PLUS, arithmeticTheory.LESS_MOD] >>
  fs[wordsTheory.dimword_def] >> decide_tac
QED

Theorem place_store_word_live_copy:
  is_word_type dty /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type dtv v /\ encode_value dtv v = SOME writes /\
  i < type_slot_size dtv ==>
  i < 1 /\
  EL b (word_to_bytes
    (lookup_storage (n2w (w2n k+i)) (apply_writes k writes st)) T) =
  EL b (word_to_bytes (typed_val_to_w256 dtv v) T)
Proof
  strip_tac >>
  drule_all stmtSimAssignStorageTheory.encode_value_word_typed >> strip_tac >>
  `type_slot_size dtv = 1` by
    (Cases_on `dty` >>
     gvs[is_word_type_def, evaluate_type_def, vyperValueTheory.type_slot_size_def,
         AllCaseEqs()]) >>
  gvs[] >>
  `lookup_storage k (apply_writes k [(0,typed_val_to_w256 dtv v)] st) =
    typed_val_to_w256 dtv v` by
    (irule place_store_apply_writes_header >> simp[]) >>
  simp[wordsTheory.n2w_w2n]
QED

Theorem place_store_bytestring_representation:
  type_widens_to tenv sty dty /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ val_in_memory stv v off mem ==>
  ?src_cap dst_cap.
    ((stv = BaseTV (BytesT (Dynamic src_cap)) /\
      dtv = BaseTV (BytesT (Dynamic dst_cap))) \/
     (stv = BaseTV (StringT src_cap) /\ dtv = BaseTV (StringT dst_cap))) /\
    src_cap <= dst_cap /\ val_in_memory dtv v off mem /\
    (case v of BytesV bs => LENGTH bs <= src_cap
     | StringV str => LENGTH str <= src_cap | _ => F) /\
    type_memory_size stv = 32 * (1 + word_size src_cap)
Proof
  strip_tac >>
  Cases_on `sty` >> fs[is_bytestring_type_def] >>
  rename1 `BaseT bs` >> Cases_on `bs` >> fs[is_bytestring_type_def] >>
  Cases_on `dty` >> fs[is_bytestring_type_def] >>
  rename1 `BaseT bd` >> Cases_on `bd` >> fs[is_bytestring_type_def] >>
  gvs[type_widens_to_def, arg_type_fits_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, valueEncodingTheory.type_memory_size_def,
      valueEncodingDefsTheory.val_in_memory_def, is_bytestring_type_def]
QED

Theorem place_store_load_emit_path:
  emit_op MLOAD [src] sa = (loaded,sm) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;loaded] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME k /\ eval_operand src s = SOME sw ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    store_copy_normalize s t = (if tr then tstore else sstore) k (mload (w2n sw) s) s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!out. step_inst_base (mk_inst sa.cs_next_id MLOAD [src] [out]) s =
    OK (update_var out (mload (w2n sw) s) s)` by
    (gen_tac >> irule emitHelperPropsTheory.step_MLOAD >> simp[eval_operands_def]) >>
  drule place_store_emit_op_path >>
  simp[is_terminator_def] >>
  disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`mload (w2n sw) s`,`ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK u)` >>
  first_x_assum (qspecl_then [`0`,`0`] strip_assume_tac) >>
  fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `eval_operand dst u = SOME k` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static /\ u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  drule_all place_store_emit_slot_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `((if tr then tstore else sstore) k (mload (w2n sw) s) u)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
        gas_marked_path_then)) >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `tr` >>
  gvs[store_copy_normalize_def, tstore_def, sstore_def, lookup_var_def] >>
  qpat_x_assum `_ = s` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >> gvs[]
QED

Theorem place_store_memory_live_at:
  well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v off s.vs_memory /\ encode_value tv v = SOME writes /\
  start < dimword (:256) /\ start + type_slot_size tv <= dimword (:256) /\
  i < type_slot_size tv /\ b < 32 /\
  ~dead_bytes (apply_writes (n2w start) writes st) start tv (start+i) b ==>
  EL b (word_to_bytes (lookup_storage (n2w (start+i))
    (apply_writes (n2w start) writes st)) T) =
  EL b (word_to_bytes (mload (off+32*i) s) T)
Proof
  strip_tac >>
  mp_tac (Q.INST [`k` |-> `n2w start`, `mem` |-> `s.vs_memory`, `j` |-> `i`]
    (SPEC_ALL storageCopyLiveTheory.encode_value_memory_live)) >>
  `w2n (n2w start : bytes32) = start` by simp[wordsTheory.w2n_n2w] >>
  pure_asm_rewrite_tac[] >>
  simp_tac bool_ss [valueEncodingPropsTheory.mem_word_at_eq_mload]
QED

Theorem place_store_typed_memory_suffix_run:
  (if type_memory_size tv <= 32 then
     ?loaded sm. emit_op MLOAD [src] sa = (loaded,sm) /\
       emit_void (if tr then TSTORE else SSTORE) [dst;loaded] sm = ((),sb)
   else ?r. (if tr then compile_memory_to_transient else compile_memory_to_storage)
       src dst (type_memory_size tv DIV 32) sa = (r,sb)) /\
  type_memory_size tv = 32 * type_slot_size tv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ val_in_memory tv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `!i b. i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
      start tv (start+i) b ==>
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (mload (w2n sw+32*i) s) T)` by
    (rpt strip_tac >> irule place_store_memory_live_at >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tv`, `v`] >> pure_asm_rewrite_tac[] >> simp[]) >>
  Cases_on `type_memory_size tv <= 32`
  >- suspend "load"
  >> suspend "loop"
QED
Resume place_store_typed_memory_suffix_run[loop]:
  `type_slot_size tv < dimword (:256)` by decide_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  mp_tac (Q.INST [`n` |-> `type_slot_size tv`, `result` |-> `r`]
    (SPEC_ALL place_store_memory_leaf_run)) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED
Resume place_store_typed_memory_suffix_run[load]:
  `type_slot_size tv = 1` by decide_tac >>
  fs[IgnAsm `start = _`] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all place_store_load_emit_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
      (n2w (start+i)) (mload (w2n sw) s) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. mload (w2n (sw:bytes32)) s`]
      (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >> reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> qexists_tac `v` >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at Any) >> simp[] >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >> gvs[]
QED
Finalise place_store_typed_memory_suffix_run

Theorem place_store_destination_alloc_bound:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  ~is_word_type dty /\ type_alloc_ok cenv dty ==>
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_size dtv < dimword (:256)
Proof
  strip_tac >>
  drule_all exprSimHypsTheory.expr_sim_inv_memory_size >> strip_tac >>
  `2 ** 64 < dimword (:256)` by simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  gvs[allocLimitsTheory.type_alloc_ok_def] >> decide_tac
QED

Theorem place_store_value_storage_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    (!et n. dty <> ArrayT et (Dynamic n)) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of
         ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes cenv et + 31) DIV 32,
                 type_memory_bytes cenv et)
       | _ => NONE)
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
     type_alloc_ok cenv dty) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >> gvs[] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  Cases_on `is_word_type dty`
  >- suspend "word"
  >> suspend "memory"
QED
Resume place_store_value_storage_run[word]:
  drule_all place_store_storage_compile >> simp[] >> strip_tac >>
  `sty = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[] >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by
    fs[expr_val_rel_def] >>
  drule_all place_store_emit_slot_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
      (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
       (n2w (w2n root+delta+i)) (typed_val_to_w256 dtv v) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. typed_val_to_w256 dtv v`]
       (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >>
     reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> rpt strip_tac >>
     drule_all place_store_word_live_copy >>
     disch_then (qspecl_then [`get_storage cx ee tr`, `root+n2w delta`, `b`] mp_tac) >>
     simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func s 0 (OK t)` >>
  qexists_tac `t` >> simp[] >>
  reverse conj_tac
  >- (unabbrev_all_tac >> Cases_on `tr` >>
      simp[tstore_def, sstore_def, lookup_var_def]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >>
  simp[] >>
  unabbrev_all_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
       wordsTheory.WORD_ADD_COMM]
QED
Resume place_store_value_storage_run[memory]:
  drule_all place_store_storage_compile >> simp[] >>
  disch_then (qx_choose_then `src` (qx_choose_then `sc`
    (map_every assume_tac o CONJUNCTS))) >>
  Cases_on `dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty)`
  >- suspend "normalize"
  >> suspend "direct"
QED
Resume place_store_value_storage_run[direct]:
  gvs[]
  >- suspend "equal"
  >> suspend "bytes"
QED
Resume place_store_value_storage_run[equal]:
  fs[expr_val_rel_def] >>
  `val_in_memory dtv v (w2n w) s.vs_memory` by metis_tac[] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + type_memory_size dtv < dimword (:256)` by
    (first_x_assum (qspec_then `w` mp_tac) >> simp[] >> strip_tac >>
     fs[] >> decide_tac) >>
  `type_memory_size dtv = 32 * type_slot_size dtv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  qsuff_tac `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
        (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts`
  >- (strip_tac >> qexists_tac `t` >> gvs[]) >>
  irule place_store_typed_memory_suffix_run >>
  simp[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`dst_op`, `op`, `w`, `v`] >>
  simp[] >> gvs[] >> metis_tac[]
QED
Resume place_store_value_storage_run[bytes]:
  `~is_word_type sty` by
    (Cases_on `sty` >> fs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT (BytesT bound)` >> Cases_on `bound` >>
     fs[is_bytestring_type_def, is_word_type_def]) >>
  fs[expr_val_rel_def] >>
  `val_in_memory stv v (w2n w) s.vs_memory` by metis_tac[] >>
  drule_all place_store_bytestring_representation >>
  disch_then (qx_choose_then `src_cap` (qx_choose_then `dst_cap`
    (map_every assume_tac o CONJUNCTS))) >>
  `type_memory_bytes cenv sty = type_memory_size stv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + 32 * (1 + word_size src_cap) < dimword (:256)` by
    (first_x_assum (qspec_then `w` mp_tac) >> simp[] >> strip_tac >> fs[] >> decide_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `1 + word_size src_cap <= type_slot_size dtv` by
    (fs[vyperValueTheory.type_slot_size_def] >>
     metis_tac[exprSimHypsTheory.word_size_monotone]) >>
  Cases_on `1 + word_size src_cap <= 1`
  >- suspend "bytes_load"
  >> suspend "bytes_loop"
QED
Resume place_store_value_storage_run[bytes_loop]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  simp[] >> strip_tac >>
  `eval_operand dst_op s = SOME (n2w (w2n root+delta))` by simp[] >>
  `1 + word_size src_cap < dimword (:256)` by (fs[] >> decide_tac) >>
  `!x. op = Var x \/ dst_op = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  qsuff_tac `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
        (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts`
  >- (strip_tac >> qexists_tac `t` >> gvs[]) >>
  irule place_store_memory_leaf_run >>
  simp[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `(if _ then _ else _) _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  simp[] >> qexists_tac `v` >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    mp_tac (Q.INST [`tv` |-> `dtv`, `v` |-> `v`, `off` |-> `w2n (w:bytes32)`,
      `mem` |-> `s.vs_memory`, `k` |-> `root+n2w delta:bytes32`,
      `writes` |-> `writes`, `st` |-> `get_storage cx ee tr`,
      `src_cap` |-> `src_cap`, `dst_cap` |-> `dst_cap`, `i` |-> `i`, `b` |-> `b`]
      (SPEC_ALL place_store_bytestring_live_copy)) >>
    (impl_tac >- (simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      metis_tac[])) >>
    qpat_assum `w2n (root+n2w delta) = _` (fn th =>
      simp_tac bool_ss [th, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
        valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
    qpat_assum `n2w (w2n root+delta) = _` (fn th =>
      simp_tac bool_ss [SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] th])) >>
  metis_tac[]
QED
Resume place_store_value_storage_run[bytes_load]:
  markerLib.RESUME_TAC >>
  `1 + word_size src_cap = 1` by decide_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  simp[] >> strip_tac >>
  `cs_extends sa sd /\ cs_extends sd sb` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `fn_has_code sa sd func /\ fn_has_code sd sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all place_store_load_emit_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
      (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
      (n2w (w2n root+delta+i)) (mload (w2n w) s) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. mload (w2n (w:bytes32)) s`]
      (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >>
     reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> qexists_tac `v` >> simp[] >> rpt strip_tac >>
     mp_tac (Q.INST [`tv` |-> `dtv`, `v` |-> `v`, `off` |-> `w2n (w:bytes32)`,
       `mem` |-> `s.vs_memory`, `k` |-> `root+n2w delta:bytes32`,
       `writes` |-> `writes`, `st` |-> `get_storage cx ee tr`,
       `src_cap` |-> `src_cap`, `dst_cap` |-> `dst_cap`, `i` |-> `i`, `b` |-> `b`]
       (SPEC_ALL place_store_bytestring_live_copy)) >>
     (impl_tac >- (simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
       metis_tac[])) >> strip_tac >>
     `i = 0` by decide_tac >> gvs[] >>
     qpat_assum `w2n (root+n2w delta) = _` (fn th =>
       simp_tac bool_ss [th, arithmeticTheory.ADD_0, arithmeticTheory.MULT_0,
         AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
         valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
     qpat_assum `n2w (w2n root+delta) = _` (fn th =>
       simp_tac bool_ss [SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] th])) >>
  qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at Any) >> simp[] >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >> gvs[]
QED
Resume place_store_value_storage_run[normalize]:
  `~is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `~is_word_type sty` by
    (spose_not_then assume_tac >>
     qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     Cases_on `sty` >> Cases_on `dty` >>
     gvs[type_widens_to_def, is_word_type_def,
         arg_type_fits_def, is_bytestring_type_def] >>
     Cases_on `b` >> Cases_on `b'` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `arg_type_fits (BaseT (BytesT bd)) (BaseT (BytesT bd'))` >>
     Cases_on `bd` >> Cases_on `bd'` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def]) >>
  gvs[] >>
  drule_all place_store_destination_alloc_bound >> strip_tac >>
  fs[expr_val_rel_def] >>
  `?sw. eval_operand op s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (qpat_x_assum `!sw. eval_operand op s = SOME sw ==> _` (qspec_then `sw` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  `cs_extends sa sm` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm sc` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends sc sb` by
    (Cases_on `type_memory_size dtv <= 32`
     >- (qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
         `cs_extends sc sd /\ cs_extends sd sb` by
           metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
         metis_tac[cs_extends_trans]) >>
     qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
     Cases_on `tr` >> gvs[] >>
     mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_context_helpers) >>
     mp_tac (cj 2 stmtLoweringMonoTheory.ci_mono_context_helpers) >>
     disch_then (qspecl_then [`a.buf_operand`, `dst_op`, `type_memory_size dtv DIV 32`, `sc`] mp_tac) >>
     simp[ci_mono_def] >>
     disch_then kall_tac >>
     disch_then (qspecl_then [`a.buf_operand`, `dst_op`, `type_memory_size dtv DIV 32`, `sc`] mp_tac) >>
     simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next /\
   (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw)` by
    (qpat_assum `!sw. eval_operand op s = SOME sw ==> _` (qspec_then `sw` mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) place_store_normalize_path >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`cx`, `ctx`, `func`, `ee`, `stv`, `v`, `sw`, `s`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `dw`
    (map_every assume_tac o CONJUNCTS))) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `sm.cs_next_var <= sc.cs_next_var` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. a.buf_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, comp_ignore_bind_def] >> strip_tac >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `!x. a.buf_operand = Var x \/ dst_op = Var x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand dst_op u = SOME (root+n2w delta)` by
    (Cases_on `dst_op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static` by
    (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`) place_store_storage_write_inv >>
     disch_then drule >> simp[]) >>
  `type_memory_size dtv = 32 * type_slot_size dtv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
        (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x u) /\
    t.vs_allocas = u.vs_allocas /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_typed_memory_suffix_run >>
     simp[] >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> qexistsl_tac [`dst_op`, `a.buf_operand`, `dw`, `v`] >>
     gvs[] >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
       gas_marked_path_then)) >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  `not_fresh_at sc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `!x. not_fresh_at sc x ==> _` drule >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]
QED
Finalise place_store_value_storage_run
