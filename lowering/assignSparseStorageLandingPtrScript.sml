(* Land the existing sparse storage pointer execution in the source state. *)
Theory assignSparseStorageLandingPtr
Ancestors
  storeSlotsPtrInterface placeStoreSlots placeStoreStorage
  assignBasePtrStorageTaint assignBasePtrStorageFrame appendStorageGhostPtr accountsRelProps
  bodyPtrDefs exprSimHypsDefs exprLoweringProps vyperStoragePlaceRegion
  vyperStorageBackend vyperTyping compileEnv context loweringStateRelDefs
  venomState valueEncoding valueEncodingDefs vyperEncodeDecode ptrDiscipline arithmetic words
  finite_map list pred_set

Theorem sparse_store_taint_members:
  !ks old q c.
    (q,c) IN FOLDL (\ta j. key_update ta (dw+n2w j)
      (mem_word_taint ta0 (off+32*j))) old ks ==>
    ((q,c) IN old /\ !j. MEM j ks ==> q <> dw+n2w j) \/
    (?j. MEM j ks /\ q = dw+n2w j /\ c < 32 /\ off+32*j+c IN ta0)
Proof
  Induct >> simp_tac std_ss [FOLDL,MEM] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> simp[key_update_def,mem_word_taint_def] >>
  metis_tac[]
QED
Theorem sparse_store_retained_dead:
  expr_sim_inv ce cx env es /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,rootv) /\
  storage_subregion rootv path delta tv /\ start = w2n rootk+delta /\
  0 < type_slot_size tv /\ start+type_slot_size tv <= dimword (:256) /\
  encode_value tv v = SOME writes /\ value_has_type tv v /\
  storage_dead cx tr st (w2n q) c /\
  (!j. MEM j (MAP FST writes) ==> q <> n2w (start+j)) ==>
  storage_dead cx tr (apply_writes (n2w start) writes st) (w2n q) c
Proof
  strip_tac >> drule_all place_store_root_layout >> strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  Cases_on `start <= w2n q /\ w2n q < start+type_slot_size tv`
  >- (`c < 32` by
        (qpat_x_assum `storage_dead _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [storage_dead_def]) >>
         drule (cj 1 dead_bytes_range) >> simp[]) >>
      `dead_bytes st start tv (w2n q) c` by
        (spose_not_then assume_tac >>
         mp_tac (Q.SPECL [`cx`,`tr`,`mid`,`name`,`subs`,`rootk`,`rootv`,
           `path`,`delta`,`tv`,`st`,`w2n q`,`c`] place_store_subregion_not_dead) >>
         (impl_tac >- (rpt conj_tac >> fs[] >> metis_tac[])) >> simp[]) >>
      `start+(w2n q-start) = w2n q` by decide_tac >>
      `w2n q-start < type_slot_size tv` by decide_tac >>
      `~MEM (w2n q-start) (MAP FST writes)` by
        (strip_tac >>
         `q <> n2w (start+(w2n q-start))` by metis_tac[] >>
         qpat_x_assum `q <> n2w (start+(w2n q-start))` mp_tac >>
         asm_rewrite_tac[n2w_w2n]) >>
      `dead_bytes (apply_writes (n2w start) writes st) start tv (w2n q) c` by
        (spose_not_then assume_tac >>
         qpat_x_assum `start = w2n rootk+delta` kall_tac >>
         mp_tac (Q.SPECL [`tv`,`v`,`writes`,`st`,`start`,`w2n q-start`,`c`]
           place_store_unwritten_live_preserved) >>
         asm_rewrite_tac[]) >>
      `dead_bytes (apply_writes (n2w start) writes st)
        (w2n rootk) rootv (w2n q) c` by
        (irule place_store_dead_subregion >>
         goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
         metis_tac[]) >>
      irule declared_region_dead_storage_dead >>
      goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
      simp[] >> qexistsl_tac [`mid`,`name`,`subs`] >> simp[]) >>
  irule place_store_storage_dead_subregion_frame >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  qexists_tac `st` >> simp[] >> qx_gen_tac `key` >> disch_tac >>
  `lookup_storage (n2w (w2n key)) (apply_writes (n2w start) writes st) =
    lookup_storage (n2w (w2n key)) st` suffices_by simp[] >>
  irule encoded_storage_lookup_outside >>
  conj_tac >- simp[w2n_lt] >>
  qexistsl_tac [`tv`,`v`] >> simp[w2n_n2w] >> decide_tac
QED

Theorem sparse_store_taint_dead:
  expr_sim_inv ce cx env es /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,rootv) /\
  storage_subregion rootv path delta tv /\ start = w2n rootk+delta /\
  0 < type_slot_size tv /\ start+type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ encode_value tv v = SOME writes /\
  value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv v (w2n sw) m) /\
  (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
  (!q c. (q,c) IN (if tr then tn.t_trans else tn.t_stor) ==>
    storage_dead cx tr st (w2n q) c) ==>
  !q c. (q,c) IN store_slots_taint tr sw (n2w start) tn ks ==>
    storage_dead cx tr (apply_writes (n2w start) writes st) (w2n q) c
Proof
  strip_tac >> drule_all place_store_root_layout >> strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  rpt gen_tac >> rewrite_tac[store_slots_taint_def] >> strip_tac >>
  drule sparse_store_taint_members >> strip_tac
  >- (irule sparse_store_retained_dead >> rpt conj_tac
      >- metis_tac[word_add_n2w]
      >- (qexistsl_tac [`ce`,`env`,`es`] >> asm_rewrite_tac[])
      >- (qexistsl_tac [`delta`,`mid`,`name`,`path`,`rootk`,`rootv`,`subs`,`tv`,`v`] >>
          asm_rewrite_tac[])
      >> metis_tac[]) >>
  `j < type_slot_size tv` by
    (irule (cj 1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
     goal_assum (drule_at (Pat `encode_value _ _ = _`)) >> simp[] >> metis_tac[]) >>
  `start+j < dimword (:256)` by decide_tac >>
  `w2n q = start+j` by
    (qpat_x_assum `q = n2w start+n2w j`
       (fn th => pure_rewrite_tac[th,word_add_n2w,w2n_n2w]) >>
     irule LESS_MOD >> first_assum ACCEPT_TAC) >>
  `MEM j (MAP FST writes)` by metis_tac[] >>
  `w2n (n2w start : bytes32) = start` by
    (pure_rewrite_tac[w2n_n2w] >> irule LESS_MOD >> first_assum ACCEPT_TAC) >>
  `dead_bytes (apply_writes (n2w start) writes st) start tv (w2n q) c` by
    (qpat_x_assum `w2n q = start+j` SUBST1_TAC >>
     qpat_x_assum `w2n (n2w start : bytes32) = start`
       (fn th => mp_tac (REWRITE_RULE [th]
         (Q.SPECL [`tv`,`v`,`writes`,`n2w start`,`st`,`tn.t_mem`,`mem`,
           `w2n (sw:bytes32)`,`j`,`c`] robust_memory_taint_dead))) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `dead_bytes (apply_writes (n2w start) writes st)
    (w2n rootk) rootv (w2n q) c` by
    (irule place_store_dead_subregion >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >> metis_tac[]) >>
  irule declared_region_dead_storage_dead >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`mid`,`name`,`subs`] >> simp[]
QED

