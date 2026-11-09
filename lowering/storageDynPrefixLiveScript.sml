Theory storageDynPrefixLive
Ancestors
  storageSubregionLive storageSubregionFrame compileEnv loweringStateRelDefs vyperEncodeDecode vyperStoragePlaceRegion
  arithmetic list rich_list words

(* Every slot beyond the stored length prefix is dead, including nested
   arrays whose individual live elements may themselves contain dead bytes. *)
Theorem dynarray_live_prefix[local]:
  !st start et cap j b.
    start <= j /\ j < start + 1 + cap * type_slot_size et /\ b < 32 /\
    ~dead_bytes st start (ArrayTV et (Dynamic cap)) j b ==>
    j < start + 1 + w2n (lookup_storage (n2w start) st) * type_slot_size et
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `type_slot_size et = 0` >- gvs[] >>
  spose_not_then assume_tac >>
  `start + 1 <= j` by decide_tac >>
  qpat_x_assum `~dead_bytes _ _ _ _ _` mp_tac >>
  simp_tac pure_ss [dead_bytes_def] >>
  simp_tac bool_ss [NOT_EXISTS_THM] >>
  qexists_tac `(j - (start + 1)) DIV type_slot_size et` >>
  `0 < cap` by (Cases_on `cap` >> gvs[]) >>
  conj_tac >- (simp[DIV_LT_X] >> decide_tac) >>
  `~((j - (start + 1)) DIV type_slot_size et <
      w2n (lookup_storage (n2w start) st))` by
    (simp[DIV_LT_X] >> decide_tac) >>
  simp[] >>
  qspec_then `type_slot_size et` mp_tac DIVISION >>
  simp[] >> disch_then (qspec_then `j - (start + 1)` strip_assume_tac) >>
  `(j - (start + 1)) MOD type_slot_size et < type_slot_size et` by simp[] >>
  simp[LEFT_ADD_DISTRIB] >> decide_tac
QED

Theorem storage_agree_dynarray_subregion_prefix:
 !cx mid name subs tr root tv path delta et cap a vs addr mem writes st ts.
 declared_storage_region cx mid name subs = SOME (tr,root,tv) /\
 w2n root + type_slot_size tv <= dimword (:256) /\
 (!mid' name' subs' root' tv'.
   declared_storage_region cx mid' name' subs' = SOME (tr,root',tv') /\
   (root',tv') <> (root,tv) ==>
   ranges_disjoint (w2n root) (type_slot_size tv)
                   (w2n root') (type_slot_size tv')) /\
 storage_subregion tv path delta (ArrayTV et (Dynamic cap)) /\
 w2n a = w2n root + delta /\
 well_formed_type_value (ArrayTV et (Dynamic cap)) /\
 value_has_type (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
 val_in_memory (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) addr mem /\
 encode_value (ArrayTV et (Dynamic cap)) (ArrayV (DynArrayV vs)) = SOME writes /\
 storage_agree (storage_dead cx tr st) st ts ==>
 storage_agree (storage_dead cx tr (apply_writes a writes st))
   (apply_writes a writes st)
   (FOLDL (\t i. update_storage (a + n2w i)
                       (mem_word_at (addr + 32*i) mem) t)
          ts (COUNT_LIST (1 + LENGTH vs * type_slot_size et)))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH vs <= cap /\ all_have_type et vs` by
    gvs[vyperTypingTheory.value_has_type_def] >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n a + (1 + cap * type_slot_size et) <= dimword (:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  qpat_x_assum `encode_value _ _ = _` mp_tac >>
  simp[Once vyperStorageTheory.encode_value_def, AllCaseEqs()] >> strip_tac >>
  `!i. MEM i (MAP FST slots) ==>
       1 <= i /\ i < 1 + LENGTH vs * type_slot_size et` by
    metis_tac[cj 4 encode_writes_bounded] >>
  `LENGTH vs * type_slot_size et <= cap * type_slot_size et` by
    simp[] >>
  `lookup_storage a (apply_writes a writes st) = n2w (LENGTH vs)` by
    (gvs[] >>
     `n2w (delta + w2n root) = a` by metis_tac[wordsTheory.n2w_w2n] >>
     simp_tac pure_ss [vyperStorageTheory.apply_writes_def, LET_THM] >>
     simp_tac bool_ss [ADD_0, wordsTheory.n2w_w2n] >>
     qmatch_goalsub_abbrev_tac `apply_writes a slots initial` >>
     qspecl_then [`slots`,`w2n a`,`initial`,`0`] mp_tac apply_writes_lookup_miss_num >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        `w2n a + off < dimword (:256)` by
          (first_x_assum drule >> strip_tac >>
           `LENGTH vs * type_slot_size et <= cap * type_slot_size et` by simp[] >>
           gvs[wordsTheory.dimword_def] >> decide_tac) >>
        simp[wordsTheory.n2w_11] >>
        gvs[wordsTheory.dimword_def] >> metis_tac[DECIDE ``~(1 <= 0:num)``])) >>
     simp[Abbr `initial`, vfmStateTheory.lookup_storage_def,
          vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]) >>
  `!j b. w2n a <= j /\ j < w2n a + 1 + cap * type_slot_size et /\
          b < 32 /\ ~dead_bytes (apply_writes a writes st) (w2n a)
                         (ArrayTV et (Dynamic cap)) j b ==>
          j < w2n a + 1 + LENGTH vs * type_slot_size et` by
    (rpt gen_tac >> strip_tac >>
     drule_all dynarray_live_prefix >>
     simp[wordsTheory.n2w_w2n] >>
     Cases_on `type_slot_size et = 0` >- simp[] >>
     `cap * type_slot_size et < dimword (:256)` by decide_tac >>
     `cap <= cap * type_slot_size et` by
       (Cases_on `type_slot_size et` >> gvs[] >> simp[MULT_CLAUSES]) >>
     `LENGTH vs < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.dimword_def, wordsTheory.w2n_n2w, MULT_COMM]) >>
  `!is (ad:num->bytes32) f q w initial.
     (!i. MEM i is /\ ad i = q ==> f i = w) ==>
     lookup_storage q (FOLDL (\t i. update_storage (ad i) (f i) t) initial is) =
       if MEM q (MAP ad is) then w else lookup_storage q initial` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     `!i. MEM i is /\ ad i = q ==> f i = w` by metis_tac[] >>
     first_x_assum (qspecl_then [`ad`,`f`,`q`,`w`] mp_tac) >>
     simp[] >> disch_then (qspec_then `update_storage (ad h) (f h) initial` mp_tac) >>
     simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
          combinTheory.APPLY_UPDATE_THM] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `FOLDL copy_step ts (COUNT_LIST ncopy)` >>
  `ncopy <= 1 + cap * type_slot_size et` by (simp[Abbr `ncopy`] >> decide_tac) >>
  `!i. i < ncopy ==> w2n (a + n2w i) = w2n a + i` by
    (rpt strip_tac >>
     `w2n a + i < dimword (:256)` by decide_tac >>
     `a + n2w i = n2w (w2n a + i)` by
       metis_tac[wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
     asm_rewrite_tac[] >> gvs[wordsTheory.dimword_def]) >>
  `!q:bytes32. MEM q (MAP (\i. a + n2w i) (COUNT_LIST ncopy)) <=>
       w2n a <= w2n q /\ w2n q < w2n a + ncopy` by
    (gen_tac >> simp[MEM_MAP, MEM_COUNT_LIST] >> eq_tac
     >- (strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
     strip_tac >> qexists_tac `w2n q - w2n a` >>
     `w2n q - w2n a < ncopy` by decide_tac >>
     `w2n (a + n2w (w2n q - w2n a)) = w2n q` by
       (qpat_x_assum `!i. i < ncopy ==> _` (qspec_then `w2n q - w2n a` mp_tac) >>
        asm_rewrite_tac[] >> decide_tac) >>
     metis_tac[wordsTheory.w2n_11]) >>
  `!q. lookup_storage q (FOLDL copy_step ts (COUNT_LIST ncopy)) =
       if w2n a <= w2n q /\ w2n q < w2n a + ncopy then
         mem_word_at (addr + 32 * (w2n q - w2n a)) mem
       else lookup_storage q ts` by
    (gen_tac >> simp[Abbr `copy_step`] >>
     first_x_assum (qspecl_then [`COUNT_LIST ncopy`, `\i. a + n2w i`,
                               `\i. mem_word_at (addr + 32*i) mem`] mp_tac) >>
     disch_then (qspecl_then [`q`, `mem_word_at (addr + 32*(w2n q-w2n a)) mem`,
                             `ts`] mp_tac) >>
     simp[] >> disch_then irule >> rpt strip_tac >>
     `w2n q = w2n a + i` by metis_tac[MEM_COUNT_LIST] >>
     `w2n q - w2n a = i` by decide_tac >> simp[]) >>
  irule storage_agree_subregion_patch >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `storage_agree _ _ _`)) >>
  reverse conj_tac
  >- (gen_tac >> disch_tac >>
      `~(w2n a <= w2n k /\ w2n k < w2n a + ncopy)` by
        (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
      conj_tac
      >- (qspecl_then [`writes`,`w2n a`,`st`,`w2n (k-a)`]
            mp_tac apply_writes_lookup_miss_num >>
          `n2w (w2n a + w2n (k-a)) = k` by
            ( `n2w (w2n a + w2n (k-a)) = a + (k-a)` by
                metis_tac[wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
              asm_rewrite_tac[] >> wordsLib.WORD_DECIDE_TAC) >>
          asm_rewrite_tac[wordsTheory.n2w_w2n] >> disch_then irule >>
          rpt strip_tac >> pop_assum (mp_tac o AP_TERM ``w2n:bytes32->num``) >>
          disch_then (assume_tac o PURE_REWRITE_RULE [wordsTheory.w2n_n2w]) >>
          `off < ncopy` by
            (qpat_x_assum `MEM off (MAP FST writes)` mp_tac >>
             qpat_x_assum `_::slots = writes` (fn th => rewrite_tac[GSYM th]) >>
             simp[Abbr `ncopy`] >> strip_tac >- simp[] >>
             qpat_x_assum `!i. MEM i (MAP FST slots) ==> _`
               (qspec_then `off` mp_tac) >> simp[] >> decide_tac) >>
          `w2n a + off < dimword (:256)` by decide_tac >>
          `w2n k = w2n a + off` by
            (qpat_x_assum `(_ + off) MOD _ = _` mp_tac >>
             simp_tac pure_ss [GSYM wordsTheory.dimword_def] >>
             `w2n root + delta + off = w2n a + off` by decide_tac >>
             pop_assum (fn th => pure_rewrite_tac[th]) >>
             qpat_x_assum `w2n a + off < _` (fn th => simp_tac std_ss [th]) ) >> decide_tac) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  `~dead_bytes (apply_writes a writes st) (w2n a)
      (ArrayTV et (Dynamic cap)) (w2n k) b` by
    (asm_rewrite_tac[] >> irule storage_subregion_global_live >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `w2n a <= w2n k /\ w2n k < w2n a + ncopy` by
    (qpat_x_assum `!j b. _ ==> j < _` (qspecl_then [`w2n k`,`b`] mp_tac) >>
     gvs[Abbr `ncopy`, vyperValueTheory.type_slot_size_def]) >>
  `EL b (word_to_bytes (lookup_storage k (apply_writes a writes st)) T) =
   EL b (word_to_bytes (mem_word_at (addr + 32*(w2n k - w2n a)) mem) T)`
    suffices_by simp[] >>
  irule storage_subregion_encoded_memory_live >>
  asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  asm_rewrite_tac[] >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  simp[Once vyperStorageTheory.encode_value_def] >> asm_rewrite_tac[]
QED
