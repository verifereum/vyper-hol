(* Lookup and agreement boundaries for live dynamic storage copies. *)
Theory placeStorageDynamicAgreement
Ancestors
  placeStorageSubregionLive storageCopyLive placeStorageElementPaths
  compileEnv accountsRelProps vyperStoragePlaceRegion vyperValue vyperStorage vyperTyping
  bodyMemAssignTopCopySem stmtSimStoreCopy venomState words list rich_list arithmetic

Theorem storage_live_fold_flatten[local]:
  !n ew f s.
    FOLDL (\a j. FOLDL (\a k. f a (j*ew+k)) a (COUNT_LIST ew))
      s (COUNT_LIST n) = FOLDL f s (COUNT_LIST (n*ew))
Proof
  Induct >- simp[COUNT_LIST_def] >>
  rpt gen_tac >>
  `SUC n * ew = n*ew + ew` by simp[MULT_CLAUSES, ADD_COMM] >>
  pure_asm_rewrite_tac[COUNT_LIST_SNOC, FOLDL_SNOC] >>
  pure_rewrite_tac[COUNT_LIST_ADD, FOLDL_APPEND, FOLDL_MAP] >>
  first_x_assum (qspecl_then [`ew`, `f`, `s`] assume_tac) >>
  gvs[ADD_COMM]
QED

Theorem storage_live_words_lookup:
  !n ew k ws st q.
    w2n k + n*ew <= dimword(:256) ==>
    lookup_storage q
      (FOLDL (\a j. FOLDL (\a h.
        update_storage (k+n2w (j*ew+h)) (ws (j*ew+h)) a)
        a (COUNT_LIST ew)) st (COUNT_LIST n)) =
    if w2n k <= w2n q /\ w2n q < w2n k+n*ew then
      ws (w2n q-w2n k) else lookup_storage q st
Proof
  rpt strip_tac >>
  qspecl_then [`n`, `ew`, `\a i. update_storage (k+n2w i) (ws i) a`, `st`]
    mp_tac storage_live_fold_flatten >>
  simp_tac bool_ss [] >> disch_then SUBST1_TAC >>
  irule copy_fold_region >> simp[]
QED

Theorem storage_live_backend_projection:
  !n tr p d stride ew s.
    (if tr then contract_transient else contract_storage)
      (FOLDL (\a j. store_copy_prefix
        (if tr then LocTransient else LocStorage)
        (p+n2w (32+j*stride)) (d+n2w (1+j*ew)) a ew)
        s (COUNT_LIST n)) =
    FOLDL (\a j. FOLDL (\a h.
      update_storage (d+n2w (1+j*ew)+n2w h)
        (mload (w2n (p+n2w (32+j*stride)+n2w h*32w)) s) a)
      a (COUNT_LIST ew))
      ((if tr then contract_transient else contract_storage) s)
      (COUNT_LIST n)
Proof
  rpt gen_tac >> Induct_on `n` >- simp[COUNT_LIST_def] >>
  pop_assum (mk_asm "projection_ih") >>
  pure_rewrite_tac[COUNT_LIST_SNOC, FOLDL_SNOC] >>
  BETA_TAC >>
  qmatch_goalsub_abbrev_tac `store_copy_prefix loc b k prev ew` >>
  `prev.vs_memory = s.vs_memory` by
    (qspec_then `\i. FOLDL (\a j. store_copy_prefix loc
       (p+n2w (32+j*stride)) (d+n2w (1+j*ew)) a ew) s (COUNT_LIST i)`
       mp_tac (GEN ``H:num -> venom_state``
         (Q.INST [`sbase` |-> `s`] storage_element_fold_fields)) >>
     simp[] >> disch_then (qspec_then `n` mp_tac) >>
     simp[Abbr `prev`]) >>
  asm_x "projection_ih" mp_tac >>
  gvs[Abbr `loc`, Abbr `prev`] >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[Once store_copy_prefix_def] >>
  Cases_on `tr` >>
  simp[SRULE [] (Q.INST [`tr` |-> `T`] (SPEC_ALL topcopy_backend_fold)),
       SRULE [] (Q.INST [`tr` |-> `F`] (SPEC_ALL topcopy_backend_fold)),
       contract_storage_def, contract_transient_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  gvs[mload_def, read_memory_def]
QED
Theorem storage_live_header_lookup:
  !n ew d ws st len q.
    w2n d + 1 + n*ew <= dimword(:256) ==>
    lookup_storage q (update_storage d len
      (FOLDL (\a j. FOLDL (\a h.
        update_storage (d+1w+n2w (j*ew+h)) (ws (j*ew+h)) a)
        a (COUNT_LIST ew)) st (COUNT_LIST n))) =
    if q = d then len else
    if w2n d < w2n q /\ w2n q < w2n d+1+n*ew then
      ws (w2n q-(w2n d+1)) else lookup_storage q st
Proof
  rpt strip_tac >>
  Cases_on `q = d` >- simp[copy_lookup_update] >>
  simp[copy_lookup_update] >>
  Cases_on `n*ew = 0`
  >- (Cases_on `n = 0` >- gvs[COUNT_LIST_def] >>
      `ew = 0` by gvs[] >> gvs[COUNT_LIST_def] >>
      qpat_x_assum `n <> 0` kall_tac >>
      Induct_on `n` >- simp[COUNT_LIST_def] >>
      simp[COUNT_LIST_SNOC, FOLDL_SNOC]) >>
  `w2n (d+1w) = w2n d+1` by
    simp[w2n_add_2] >>
  qspecl_then [`n`, `ew`, `d+1w`, `ws`, `st`, `q`]
    mp_tac storage_live_words_lookup >>
  simp[LESS_EQ_IFF_LESS_SUC, ADD1]
QED

Theorem storage_live_backend_lookup:
  !n tr p d ew s len q.
    w2n d + 1 + n*ew <= dimword(:256) ==>
    lookup_storage q (update_storage d len
      ((if tr then contract_transient else contract_storage)
        (FOLDL (\a j. store_copy_prefix
          (if tr then LocTransient else LocStorage)
          (p+n2w (32+j*(32*ew))) (d+n2w (1+j*ew)) a ew)
          s (COUNT_LIST n)))) =
    if q = d then len else
    if w2n d < w2n q /\ w2n q < w2n d+1+n*ew then
      mload (w2n (p+n2w (32+32*(w2n q-(w2n d+1)))) ) s
    else lookup_storage q ((if tr then contract_transient else contract_storage) s)
Proof
  rpt strip_tac >>
  rewrite_tac[storage_live_backend_projection] >>
  `!j h. (d+n2w (1+j*ew)+n2w h:256 word) =
      d+1w+n2w (j*ew+h)` by
    metis_tac[GSYM WORD_ADD_ASSOC, word_add_n2w, ADD_ASSOC] >>
  `!j h. (p+n2w (32+j*(32*ew))+n2w h*32w:256 word) =
      p+n2w (32+32*(j*ew+h))` by
    metis_tac[GSYM WORD_ADD_ASSOC, word_mul_n2w, word_add_n2w,
         LEFT_ADD_DISTRIB, MULT_ASSOC, MULT_COMM] >>
  asm_rewrite_tac[] >>
  simp[storage_live_header_lookup]
QED

Theorem storage_subregion_dead_outside:
  !cx mid name subs tr k root path delta leaf d st st' x b.
    declared_storage_region cx mid name subs = SOME (tr,k,root) /\
    storage_subregion root path delta leaf /\
    w2n d = w2n k+delta /\
    w2n k+type_slot_size root <= dimword(:256) /\
    (!a. a < dimword(:256) /\
      (a < w2n d \/ w2n d+type_slot_size leaf <= a) ==>
      lookup_storage (n2w a) st' = lookup_storage (n2w a) st) /\
    (x < w2n d \/ w2n d+type_slot_size leaf <= x) /\
    storage_dead cx tr st x b ==>
    storage_dead cx tr st' x b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [storage_dead_def] >> strip_tac >>
  rename1 `dead_bytes st (w2n slot) tv x b` >>
  `dead_bytes st' (w2n slot) tv x b` by
    (Cases_on `(slot,tv) = (k,root)`
     >- (gvs[] >> drule storage_subregion_dead_frame >>
         disch_then (qspecl_then [`st`, `st'`, `w2n k`, `x`, `b`] mp_tac) >>
         simp[] >> metis_tac[]) >>
     drule storage_subregion_bounds >> strip_tac >>
     `ranges_disjoint (w2n slot) (type_slot_size tv)
       (w2n k) (type_slot_size root)` by
       (first_x_assum irule >> simp[] >> metis_tac[]) >>
     `dead_bytes st' (w2n slot) tv x b <=> dead_bytes st (w2n slot) tv x b` by
       (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
        first_x_assum irule >> fs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
     simp[]) >>
  simp_tac bool_ss [storage_dead_def] >>
  qexistsl_tac [`mid'`, `n`, `subs'`, `slot`, `tv`] >> asm_rewrite_tac[]
QED

Theorem storage_dynamic_encoded_header[local]:
  !tv cap vs writes d st.
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    encode_value (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes /\
    w2n d+type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword(:256) ==>
    lookup_storage d (apply_writes d writes st) = n2w (LENGTH vs)
Proof
  rpt gen_tac >> strip_tac >>
  fs[Once value_has_type_def] >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once encode_value_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `_::slots = writes` (SUBST1_TAC o SYM) >>
  irule copy_dyn_head >> qexists_tac `tv` >> simp[] >>
  fs[type_slot_size_def] >>
  `LENGTH vs * type_slot_size tv <= cap * type_slot_size tv` by simp[] >>
  decide_tac
QED

Theorem storage_dynamic_live_bound[local]:
  !j cap tv b d st n.
    0 < j /\ j < 1+cap*type_slot_size tv /\ b < 32 /\
    lookup_storage d st = n2w n /\
    ~dead_bytes st (w2n d) (ArrayTV tv (Dynamic cap)) (w2n d+j) b ==>
    j < 1+n*type_slot_size tv
Proof
  rpt gen_tac >> strip_tac >>
  drule_all copy_dyn_live_index >> strip_tac >>
  `i < n` by
    (fs[w2n_n2w] >>
     `n MOD dimword(:256) <= n` by (irule MOD_LESS_EQ >> simp[]) >> gvs[]) >>
  `i*type_slot_size tv+type_slot_size tv <= n*type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  decide_tac
QED

Theorem storage_dynamic_subregion_lookup_agree[local]:
  !cx tr mid name subs k root path delta tv cap d vs writes off mem st1 st2 st2'.
    declared_storage_region cx mid name subs = SOME (tr,k,root) /\
    storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
    w2n d = w2n k+delta /\
    w2n k+type_slot_size root <= dimword(:256) /\
    (!mid' name' subs' k' root'.
      declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
      (k',root') <> (k,root) ==>
      ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
    well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    encode_value (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes /\
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem /\
    (!q. lookup_storage q st2' =
      if q = d then n2w (LENGTH vs) else
      if w2n d < w2n q /\ w2n q < w2n d+1+LENGTH vs*type_slot_size tv then
        mem_word_at (off+32*(w2n q-w2n d)) mem
      else lookup_storage q st2) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr (apply_writes d writes st1))
      (apply_writes d writes st1) st2'
Proof
  rpt gen_tac >> strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n d+type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword(:256)` by decide_tac >>
  `LENGTH vs <= cap` by fs[Once value_has_type_def] >>
  `LENGTH vs*type_slot_size tv <= cap*type_slot_size tv` by simp[] >>
  pure_rewrite_tac[storage_agree_def] >> rpt gen_tac >> strip_tac >>
  rename1 `~storage_dead cx tr (apply_writes d writes st1) (w2n q) b` >>
  Cases_on `w2n d <= w2n q /\ w2n q < w2n d+type_slot_size (ArrayTV tv (Dynamic cap))`
  >- suspend "inside"
  >> suspend "outside"
QED
Resume storage_dynamic_subregion_lookup_agree[inside]:
  `~dead_bytes (apply_writes d writes st1) (w2n d)
    (ArrayTV tv (Dynamic cap)) (w2n q) b` by
    (strip_tac >> qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >> simp[] >>
     pure_rewrite_tac[storage_dead_def] >>
     qexistsl_tac [`mid`, `name`, `subs`, `k`, `root`] >> simp[] >>
     conj_tac >- gvs[] >>
     drule storage_subregion_dead_leaf >>
     disch_then (qspecl_then [`apply_writes d writes st1`, `w2n k`, `w2n q`, `b`] mp_tac) >>
     simp[] >> metis_tac[ADD_COMM]) >>
  `lookup_storage d (apply_writes d writes st1) = n2w (LENGTH vs)` by
    (irule storage_dynamic_encoded_header >> metis_tac[]) >>
  Cases_on `q = d` >- (gvs[]) >>
  `0 < w2n q-w2n d /\ w2n d+(w2n q-w2n d) = w2n q` by
    (`w2n q <> w2n d` by metis_tac[w2n_11] >> decide_tac) >>
  `w2n q-w2n d < 1+LENGTH vs*type_slot_size tv` by
    (irule storage_dynamic_live_bound >> simp[] >>
     qexistsl_tac [`b`, `cap`, `d`, `apply_writes d writes st1`] >>
     fs[type_slot_size_def] >> gvs[]) >>
  qpat_x_assum `!q. lookup_storage q st2' = _` (qspec_then `q` mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  drule encode_value_memory_live >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`d`, `st1`, `w2n q-w2n d`, `b`] mp_tac) >>
  simp[] >> gvs[]
QED
Resume storage_dynamic_subregion_lookup_agree[outside]:
  `!a. a < dimword(:256) /\
    (a < w2n d \/ w2n d+type_slot_size (ArrayTV tv (Dynamic cap)) <= a) ==>
    lookup_storage (n2w a) (apply_writes d writes st1) = lookup_storage (n2w a) st1` by
    (gen_tac >> disch_tac >> irule copy_encoded_outside >>
     conj_tac >- gvs[] >>
     qexistsl_tac [`ArrayTV tv (Dynamic cap)`, `ArrayV (DynArrayV vs)`] >> simp[] >> decide_tac) >>
  `~storage_dead cx tr st1 (w2n q) b` by
    (strip_tac >> qpat_x_assum `~storage_dead _ _ (apply_writes _ _ _) _ _` mp_tac >> simp[] >>
     irule (INST_TYPE [alpha |-> ``:256``] storage_subregion_dead_outside) >>
     qexistsl_tac [`d`, `delta`, `k`, `ArrayTV tv (Dynamic cap)`, `mid`, `name`,
       `path`, `root`, `st1`, `subs`] >> simp[] >> gvs[]) >>
  `lookup_storage q (apply_writes d writes st1) = lookup_storage q st1` by
    (first_x_assum (qspec_then `w2n q` mp_tac) >> simp[w2n_lt] >> decide_tac) >>
  `q <> d /\ ~(w2n d < w2n q /\ w2n q < w2n d+1+LENGTH vs*type_slot_size tv)` by
    (conj_tac
     >- (strip_tac >> gvs[type_slot_size_def]) >>
     qpat_x_assum `~(_ <= _ /\ _)` mp_tac >>
     simp_tac std_ss [type_slot_size_def] >> decide_tac) >>
  qpat_x_assum `!q. lookup_storage q st2' = _` (qspec_then `q` mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >> simp[storage_agree_def]
QED
Finalise storage_dynamic_subregion_lookup_agree

Theorem storage_dynamic_subregion_backend_agree:
  !cx tr mid name subs k root path delta tv cap d vs writes p s st1.
    declared_storage_region cx mid name subs = SOME (tr,k,root) /\
    storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
    w2n d = w2n k+delta /\
    w2n k+type_slot_size root <= dimword(:256) /\
    (!mid' name' subs' k' root'.
      declared_storage_region cx mid' name' subs' = SOME (tr,k',root') /\
      (k',root') <> (k,root) ==>
      ranges_disjoint (w2n k) (type_slot_size root) (w2n k') (type_slot_size root')) /\
    well_formed_type_value (ArrayTV tv (Dynamic cap)) /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    encode_value (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes /\
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n p) s.vs_memory /\
    w2n p+32*(1+LENGTH vs*type_slot_size tv) <= dimword(:256) /\
    storage_agree (storage_dead cx tr st1) st1
      ((if tr then contract_transient else contract_storage) s) ==>
    storage_agree (storage_dead cx tr (apply_writes d writes st1))
      (apply_writes d writes st1)
      (update_storage d (n2w (LENGTH vs))
        ((if tr then contract_transient else contract_storage)
          (FOLDL (\a j. store_copy_prefix
            (if tr then LocTransient else LocStorage)
            (p+n2w (32+j*(32*type_slot_size tv)))
            (d+n2w (1+j*type_slot_size tv)) a (type_slot_size tv))
            s (COUNT_LIST (LENGTH vs)))))
Proof
  rpt gen_tac >> strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `LENGTH vs <= cap` by fs[Once value_has_type_def] >>
  `LENGTH vs*type_slot_size tv <= cap*type_slot_size tv` by simp[] >>
  `w2n d+1+LENGTH vs*type_slot_size tv <= dimword(:256)` by
    (qpat_x_assum `delta+_ <= _` mp_tac >>
     simp_tac std_ss [type_slot_size_def] >> decide_tac) >>
  irule storage_dynamic_subregion_lookup_agree >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  simp[] >>
  qexistsl_tac [`delta`, `k`, `mid`, `name`, `path`, `root`, `subs`] >>
  simp[] >> conj_tac >- gvs[] >>
  gen_tac >>
  drule storage_live_backend_lookup >>
  disch_then (qspecl_then [`tr`, `p`, `s`, `n2w (LENGTH vs)`, `q`] mp_tac) >>
  `!j. j*(32*type_slot_size tv) = 32*(j*type_slot_size tv)` by
    metis_tac[MULT_ASSOC, MULT_COMM] >>
  simp[] >> disch_then SUBST1_TAC >>
  Cases_on `q = d` >- simp[] >>
  Cases_on `w2n d < w2n q /\ w2n q < w2n d+1+LENGTH vs*type_slot_size tv`
  >- (simp[] >>
      `32+32*(w2n q-(w2n d+1)) = 32*(w2n q-w2n d)` by decide_tac >>
      `w2n p+32*(w2n q-w2n d) < dimword(:256)` by decide_tac >>
      `w2n (p+n2w (32+32*(w2n q-(w2n d+1)))) =
        w2n p+32*(w2n q-w2n d)` by
        (asm_rewrite_tac[] >> simp[w2n_add_2]) >>
      gvs[valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  simp[]
QED
