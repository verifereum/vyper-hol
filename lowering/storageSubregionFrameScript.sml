Theory storageSubregionFrame
Ancestors
  compileEnv accountsRelProps vyperStoragePlaceRegion vyperState vyperMisc list option pair vyperValue

Theorem dead_bytes_list_selected:
  !types i elem st base j b.
    oEL i types = SOME elem /\
    dead_bytes st (base + tuple_prefix_slot_size i types) elem j b ==>
    dead_bytes_list st base types j b
Proof
  Induct >> Cases_on `i` >>
  simp[oEL_def, tuple_prefix_slot_size_def, dead_bytes_def] >>
  rpt strip_tac >> disj2_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  asm_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC]
QED

Theorem dead_bytes_fields_selected:
  !fields id delta elem st base j b.
    struct_field_slot fields id = SOME (delta,elem) /\
    dead_bytes st (base + delta) elem j b ==>
    dead_bytes_fields st base fields j b
Proof
  Induct >> simp[struct_field_slot_def, dead_bytes_def] >>
  Cases >> rpt gen_tac >>
  simp[struct_field_slot_def, dead_bytes_def] >>
  IF_CASES_TAC >> simp[] >> rpt strip_tac
  >- (gvs[] >> disj1_tac >> simp[]) >>
  gvs[AllCaseEqs()] >> PairCases_on `z` >> gvs[] >>
  disj2_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >>
  `base' + type_slot_size r + z0 = base' + (z0 + type_slot_size r)` by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem storage_subregion_dead_bytes:
  !tv path off leaf st base j b.
    storage_subregion tv path off leaf /\
    dead_bytes st (base + off) leaf j b ==>
    dead_bytes st base tv j b
Proof
  recInduct storage_subregion_ind >>
  rpt strip_tac >> gvs[storage_subregion_def]
  >- (pure_rewrite_tac[dead_bytes_def] >> qexists_tac `Num i` >>
      conj_tac >- asm_rewrite_tac[] >>
      first_x_assum irule >> goal_assum (drule_at Any) >>
      metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM])
  >- (pure_rewrite_tac[dead_bytes_def] >> qexists_tac `Num i` >>
      conj_tac >- asm_rewrite_tac[] >>
      `dead_bytes st (base' + 1 + Num i * type_slot_size elem) elem j b` by
        (first_x_assum irule >> goal_assum (drule_at Any) >>
         metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
      IF_CASES_TAC >- asm_rewrite_tac[] >>
      drule (cj 1 dead_bytes_range) >> decide_tac)
  >- (pure_rewrite_tac[dead_bytes_def] >>
      irule dead_bytes_fields_selected >>
      goal_assum (drule_at (Pat `struct_field_slot _ _ = _`)) >>
      first_x_assum irule >> goal_assum (drule_at Any) >>
      metis_tac[arithmeticTheory.ADD_ASSOC]) >>
  pure_rewrite_tac[dead_bytes_def] >>
  irule dead_bytes_list_selected >> goal_assum (drule_at Any) >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem dead_bytes_list_selected_frame:
  !types k elem st st' base lo hi j b.
    oEL k types = SOME elem /\
    base + tuple_prefix_slot_size k types <= lo /\
    hi <= base + tuple_prefix_slot_size k types + type_slot_size elem /\
    (!i. base <= i /\ i < base + type_slot_size_list types /\
         ~(lo <= i /\ i < hi) ==>
         lookup_storage (n2w i) st' = lookup_storage (n2w i) st) /\
    (dead_bytes st' (base + tuple_prefix_slot_size k types) elem j b <=>
     dead_bytes st (base + tuple_prefix_slot_size k types) elem j b) ==>
    (dead_bytes_list st' base types j b <=> dead_bytes_list st base types j b)
Proof
  Induct >> Cases_on `k` >>
  simp[oEL_def, tuple_prefix_slot_size_def, dead_bytes_def, type_slot_size_def] >>
  rpt strip_tac
  >- (rename1 `hi <= bs + type_slot_size h` >>
      `dead_bytes_list st' (bs + type_slot_size h) types j b <=>
        dead_bytes_list st (bs + type_slot_size h) types j b` by
        (irule (cj 2 dead_bytes_frame) >> rpt strip_tac >>
         first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  rename1 `bs + (type_slot_size h + tuple_prefix_slot_size n types) <= lo` >>
  `dead_bytes st' bs h j b <=> dead_bytes st bs h j b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `dead_bytes_list st' (bs + type_slot_size h) types j b <=>
   dead_bytes_list st (bs + type_slot_size h) types j b` by
    (first_x_assum irule >> goal_assum (drule_at (Pat `oEL _ _ = _`)) >>
     qexistsl_tac [`hi`, `lo`] >>
     `bs + type_slot_size h + tuple_prefix_slot_size n types + type_slot_size elem =
      bs + (type_slot_size elem + (type_slot_size h + tuple_prefix_slot_size n types))` by decide_tac >>
     asm_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Theorem dead_bytes_fields_list:
  !fields st base j b.
    dead_bytes_fields st base fields j b <=>
    dead_bytes_list st base (MAP SND fields) j b
Proof
  Induct >> simp[dead_bytes_def] >> Cases_on `h` >> simp[dead_bytes_def]
QED

Theorem struct_field_slot_list_selected:
  !fields id delta elem.
    struct_field_slot fields id = SOME (delta,elem) ==>
    ?k. oEL k (MAP SND fields) = SOME elem /\
        delta = tuple_prefix_slot_size k (MAP SND fields)
Proof
  Induct >> simp[struct_field_slot_def] >> Cases >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC >> simp[] >> rpt strip_tac
  >- (gvs[] >> qexists_tac `0` >> simp[oEL_def, tuple_prefix_slot_size_def]) >>
  gvs[AllCaseEqs()] >> PairCases_on `z` >> gvs[] >>
  first_x_assum drule >> strip_tac >> qexists_tac `SUC k` >>
  simp[oEL_def, tuple_prefix_slot_size_def]
QED

Theorem dead_bytes_array_selected_frame:
  !elem n k st st' base lo hi j b.
    k < n /\ base + k * type_slot_size elem <= lo /\
    hi <= base + k * type_slot_size elem + type_slot_size elem /\
    (!i. base <= i /\ i < base + n * type_slot_size elem /\
         ~(lo <= i /\ i < hi) ==>
         lookup_storage (n2w i) st' = lookup_storage (n2w i) st) /\
    (dead_bytes st' (base + k * type_slot_size elem) elem j b <=>
     dead_bytes st (base + k * type_slot_size elem) elem j b) ==>
    !a. a < n ==>
      (dead_bytes st' (base + a * type_slot_size elem) elem j b <=>
       dead_bytes st (base + a * type_slot_size elem) elem j b)
Proof
  rpt strip_tac >> Cases_on `a = k` >- gvs[] >>
  irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  `a * type_slot_size elem + type_slot_size elem <= n * type_slot_size elem` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `a * type_slot_size elem + type_slot_size elem <= k * type_slot_size elem \/
   k * type_slot_size elem + type_slot_size elem <= a * type_slot_size elem` by
    (Cases_on `a < k`
     >- (disj1_tac >> irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
     disj2_tac >> irule vyperLookupStorageTheory.array_index_element_end_bound >> decide_tac) >>
  first_x_assum irule >> decide_tac
QED

Theorem type_slot_size_fields_list:
  !fields. type_slot_size_fields fields = type_slot_size_list (MAP SND fields)
Proof
  Induct >> simp[type_slot_size_def] >> Cases_on `h` >> simp[type_slot_size_def]
QED

Theorem storage_subregion_dead_bytes_frame_outside:
  !tv path off leaf st st' base j b.
    storage_subregion tv path off leaf /\
    (!i. base <= i /\ i < base + type_slot_size tv /\
         ~(base + off <= i /\
           i < base + off + type_slot_size leaf) ==>
         lookup_storage (n2w i) st' = lookup_storage (n2w i) st) /\
    ~(base + off <= j /\
      j < base + off + type_slot_size leaf) ==>
    (dead_bytes st' base tv j b <=> dead_bytes st base tv j b)
Proof
  recInduct storage_subregion_ind >> rpt gen_tac >>
  simp_tac pure_ss [storage_subregion_def] >> rpt strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC
  >- (eq_tac >> strip_tac >> drule (cj 1 dead_bytes_range) >> decide_tac)
  >- suspend "fixed"
  >- suspend "dynamic"
  >- suspend "struct"
  >> suspend "tuple"
QED

Resume storage_subregion_dead_bytes_frame_outside[fixed]:
      rename1 `dead_bytes st' bs (ArrayTV elem (Fixed n)) j b` >>
      drule storage_subregion_bounds >> strip_tac >>
      `Num i * type_slot_size elem + type_slot_size elem <= n * type_slot_size elem` by
        (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
      `dead_bytes st' (bs + Num i * type_slot_size elem) elem j b <=>
       dead_bytes st (bs + Num i * type_slot_size elem) elem j b` by
        (first_x_assum irule >> goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
         conj_tac
         >- (rpt strip_tac >> first_x_assum irule >>
             simp[type_slot_size_def] >> decide_tac) >>
         decide_tac) >>
      `!a. a < n ==>
        (dead_bytes st' (bs + a * type_slot_size elem) elem j b <=>
         dead_bytes st (bs + a * type_slot_size elem) elem j b)` by
        (match_mp_tac dead_bytes_array_selected_frame >>
         goal_assum (drule_at (Pat `_ < n`)) >>
         qexistsl_tac [`bs + (Num i * type_slot_size elem + rest)`,
           `bs + (Num i * type_slot_size elem + rest) + type_slot_size leaf`] >>
         asm_rewrite_tac[] >> conj_tac >- decide_tac >>
         conj_tac >- decide_tac >> rpt strip_tac >>
         first_x_assum irule >> simp[type_slot_size_def] >> decide_tac) >>
      pure_rewrite_tac[dead_bytes_def] >> metis_tac[]
QED

Resume storage_subregion_dead_bytes_frame_outside[dynamic]:
      rename1 `dead_bytes st' bs (ArrayTV elem (Dynamic n)) j b` >>
      drule storage_subregion_bounds >> strip_tac >>
      `Num i * type_slot_size elem + type_slot_size elem <= n * type_slot_size elem` by
        (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
      `lookup_storage (n2w bs) st' = lookup_storage (n2w bs) st` by
        (first_x_assum irule >> simp[type_slot_size_def] >> decide_tac) >>
      `dead_bytes st' (bs + 1 + Num i * type_slot_size elem) elem j b <=>
       dead_bytes st (bs + 1 + Num i * type_slot_size elem) elem j b` by
        (first_x_assum irule >> goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
         conj_tac
         >- (rpt strip_tac >> first_x_assum irule >>
             simp[type_slot_size_def] >> decide_tac) >> decide_tac) >>
      `!a. a < n ==>
        (dead_bytes st' (bs + 1 + a * type_slot_size elem) elem j b <=>
         dead_bytes st (bs + 1 + a * type_slot_size elem) elem j b)` by
        (match_mp_tac dead_bytes_array_selected_frame >>
         goal_assum (drule_at (Pat `_ < n`)) >>
         qexistsl_tac [`bs + (1 + Num i * type_slot_size elem + rest)`,
           `bs + (1 + Num i * type_slot_size elem + rest) + type_slot_size leaf`] >>
         asm_rewrite_tac[] >> conj_tac >- decide_tac >>
         conj_tac >- decide_tac >> rpt strip_tac >>
         first_x_assum irule >> simp[type_slot_size_def] >> decide_tac) >>
      pure_rewrite_tac[dead_bytes_def] >> asm_rewrite_tac[] >> metis_tac[]
QED

Resume storage_subregion_dead_bytes_frame_outside[struct]:
      rename1 `dead_bytes st' bs (StructTV fields) j b` >>
      drule storage_subregion_bounds >> strip_tac >>
      drule struct_field_slot_end_bound >> strip_tac >>
      `dead_bytes st' (bs + delta) elem j b <=>
       dead_bytes st (bs + delta) elem j b` by
        (first_x_assum irule >> goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
         conj_tac
         >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >> decide_tac) >>
      drule struct_field_slot_list_selected >> strip_tac >>
      pure_rewrite_tac[dead_bytes_def, dead_bytes_fields_list] >>
      irule dead_bytes_list_selected_frame >>
      goal_assum (drule_at (Pat `oEL _ _ = _`)) >>
      qexistsl_tac [`bs + (delta + rest) + type_slot_size leaf`, `bs + (delta + rest)`] >>
      asm_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
      conj_tac
      >- (rpt strip_tac >> first_x_assum irule >>
          asm_rewrite_tac[type_slot_size_def, type_slot_size_fields_list,
                          GSYM arithmeticTheory.ADD_ASSOC]) >>
      conj_tac >- decide_tac >> conj_tac >- decide_tac >> metis_tac[]
QED

Resume storage_subregion_dead_bytes_frame_outside[tuple]:
  rename1 `dead_bytes st' bs (TupleTV types) j b` >>
  drule storage_subregion_bounds >> strip_tac >>
  drule tuple_component_slot_end_bound >> strip_tac >>
  `dead_bytes st' (bs + tuple_prefix_slot_size (Num i) types) elem j b <=>
   dead_bytes st (bs + tuple_prefix_slot_size (Num i) types) elem j b` by
    (first_x_assum irule >> goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >> decide_tac) >>
  pure_rewrite_tac[dead_bytes_def] >>
  irule dead_bytes_list_selected_frame >>
  goal_assum (drule_at (Pat `oEL _ _ = _`)) >>
  qexistsl_tac [`bs + (tuple_prefix_slot_size (Num i) types + rest) + type_slot_size leaf`,
    `bs + (tuple_prefix_slot_size (Num i) types + rest)`] >>
  asm_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      asm_rewrite_tac[type_slot_size_def, GSYM arithmeticTheory.ADD_ASSOC]) >>
  decide_tac
QED

Finalise storage_subregion_dead_bytes_frame_outside

Theorem storage_dead_subregion_frame_outside:
 !cx tr mid n subs slot tv path off leaf st st' j b.
  declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
  storage_subregion tv path off leaf /\
  (!k:bytes32. ~(w2n slot + off <= w2n k /\
                 w2n k < w2n slot + off + type_slot_size leaf) ==>
       lookup_storage k st' = lookup_storage k st) /\
  ~(w2n slot + off <= j /\ j < w2n slot + off + type_slot_size leaf) ==>
  (storage_dead cx tr st' j b <=> storage_dead cx tr st j b)
Proof
  rpt gen_tac >> strip_tac >>
  `!w tvw. w2n w + type_slot_size tvw <= dimword (:256) /\
      ((w,tvw) <> (slot,tv) ==>
        ranges_disjoint (w2n w) (type_slot_size tvw) (w2n slot) (type_slot_size tv)) ==>
      (dead_bytes st' (w2n w) tvw j b <=> dead_bytes st (w2n w) tvw j b)` by
    (rpt gen_tac >> strip_tac >> Cases_on `(w,tvw) = (slot,tv)`
     >- (qpat_x_assum `(w,tvw) = (slot,tv)` mp_tac >>
         pure_rewrite_tac[pairTheory.PAIR_EQ] >> strip_tac >>
         rpt BasicProvers.VAR_EQ_TAC >>
         irule storage_subregion_dead_bytes_frame_outside >>
         goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
         conj_tac
         >- (rpt strip_tac >> first_x_assum irule >>
             `i < dimword (:256)` by decide_tac >> simp[] >> decide_tac) >>
         decide_tac) >>
     irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     `i < dimword (:256)` by decide_tac >>
     first_x_assum irule >> simp[] >>
     drule storage_subregion_bounds >>
     fs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
  pure_rewrite_tac[storage_dead_def] >> metis_tac[]
QED

Theorem storage_agree_subregion_patch:
 !cx tr mid n subs slot tv path off leaf st st' ts ts'.
  declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
  storage_subregion tv path off leaf /\
  storage_agree (storage_dead cx tr st) st ts /\
  (!k:bytes32. ~(w2n slot + off <= w2n k /\
                 w2n k < w2n slot + off + type_slot_size leaf) ==>
       lookup_storage k st' = lookup_storage k st /\
       lookup_storage k ts' = lookup_storage k ts) /\
  (!k:bytes32. !b. b < 32 /\
       w2n slot + off <= w2n k /\
       w2n k < w2n slot + off + type_slot_size leaf /\
       ~storage_dead cx tr st' (w2n k) b ==>
       EL b (word_to_bytes (lookup_storage k st') T) =
       EL b (word_to_bytes (lookup_storage k ts') T)) ==>
  storage_agree (storage_dead cx tr st') st' ts'
Proof
  rpt gen_tac >> strip_tac >>
  `!j b. ~(w2n slot + off <= j /\
           j < w2n slot + off + type_slot_size leaf) ==>
     (storage_dead cx tr st' j b <=> storage_dead cx tr st j b)` by
    (rpt strip_tac >> irule storage_dead_subregion_frame_outside >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  pure_rewrite_tac[storage_agree_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `w2n slot + off <= w2n k /\
            w2n k < w2n slot + off + type_slot_size leaf`
  >- (first_x_assum irule >> asm_rewrite_tac[]) >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >>
  pure_rewrite_tac[storage_agree_def] >> metis_tac[]
QED
