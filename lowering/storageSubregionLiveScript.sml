Theory storageSubregionLive
Ancestors
  storageSubregionFrame storageCopyLive compileEnv loweringStateRelDefs vyperStoragePlaceRegion
  words list

Theorem storage_subregion_global_live:
 !cx tr mid n subs slot tv path off leaf st j b.
 declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
 w2n slot + type_slot_size tv <= dimword (:256) /\
 (!mid' n' subs' slot' tv'.
   declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
   (slot',tv') <> (slot,tv) ==>
   ranges_disjoint (w2n slot) (type_slot_size tv)
                   (w2n slot') (type_slot_size tv')) /\
 storage_subregion tv path off leaf /\
 ~storage_dead cx tr st j b ==>
 ~dead_bytes st (w2n slot + off) leaf j b
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  `dead_bytes st (w2n slot) tv j b` by
    (irule storage_subregion_dead_bytes >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `~storage_dead _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[storage_dead_def] >> metis_tac[]
QED

Theorem storage_subregion_encoded_memory_live:
 !cx tr mid n subs slot tv path off leaf a v ptr mem writes st k b.
 declared_storage_region cx mid n subs = SOME (tr,slot,tv) /\
 w2n slot + type_slot_size tv <= dimword (:256) /\
 (!mid' n' subs' slot' tv'.
   declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
   (slot',tv') <> (slot,tv) ==>
   ranges_disjoint (w2n slot) (type_slot_size tv)
                   (w2n slot') (type_slot_size tv')) /\
 storage_subregion tv path off leaf /\
 w2n a = w2n slot + off /\
 well_formed_type_value leaf /\ value_has_type leaf v /\
 val_in_memory leaf v ptr mem /\ encode_value leaf v = SOME writes /\
 w2n a <= w2n k /\ w2n k < w2n a + type_slot_size leaf /\ b < 32 /\
 ~storage_dead cx tr (apply_writes a writes st) (w2n k) b ==>
 EL b (word_to_bytes (lookup_storage k (apply_writes a writes st)) T) =
 EL b (word_to_bytes (mem_word_at (ptr + 32 * (w2n k - w2n a)) mem) T)
Proof
  rpt gen_tac >> strip_tac >>
  `~dead_bytes (apply_writes a writes st) (w2n a) leaf (w2n k) b` by
    (asm_rewrite_tac[] >> irule storage_subregion_global_live >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n a + type_slot_size leaf <= dimword (:256)` by decide_tac >>
  `w2n a + (w2n k - w2n a) = w2n k` by decide_tac >>
  drule_at (Pat `val_in_memory _ _ _ _`) encode_value_memory_live >>
  disch_then (qspec_then `a` mp_tac) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`st`, `w2n k - w2n a`, `b`] mp_tac) >>
  asm_rewrite_tac[] >>
  (impl_tac >- (conj_tac >- decide_tac >> metis_tac[])) >> simp[]
QED
