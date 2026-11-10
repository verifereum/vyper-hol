(* Suffix restriction for the recursive tuple slot layout. *)
Theory bodyPtrSubscriptSeamTupleStorage
Ancestors
  accountsRelProps compileEnv loweringStateRelDefs vyperValue vyperLookupStorage vyperStorage
  targetPlaceLive exprSimPopNestedBase vyperStorageRegionWrite list words

Theorem tuple_dead_suffix:
  !pre rest st start j b.
    dead_bytes_list st start (pre ++ rest) j b /\
    start + type_slot_size_list pre <= j ==>
    dead_bytes_list st (start + type_slot_size_list pre) rest j b
Proof
  Induct >> simp[type_slot_size_def] >> rpt gen_tac >> strip_tac >>
  gvs[Once dead_bytes_def] >>
  imp_res_tac (cj 1 dead_bytes_range) >> gvs[] >>
  first_x_assum drule >> metis_tac[arithmeticTheory.ADD_ASSOC]
QED


Theorem tuple_agree_suffix:
  storage_range_agree st st' w (TupleTV (pre ++ rest)) ==>
  storage_range_agree st st'
    (w + n2w (type_slot_size_list pre)) (TupleTV rest)
Proof
  strip_tac >>
  Cases_on `type_slot_size_list rest = 0`
  >- (simp[storage_range_agree_def, type_slot_size_def] >>
      rpt strip_tac >> gvs[] >> qspec_then `w + n2w (type_slot_size_list pre)` mp_tac
        wordsTheory.w2n_lt >> simp[]) >>
  gvs[storage_range_agree_def, type_slot_size_def, type_slot_size_list_append] >>
  `w2n w + type_slot_size_list pre < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (type_slot_size_list pre)) =
    w2n w + type_slot_size_list pre` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!k b. _ ==> _` irule >> simp[] >> strip_tac >>
  `dead_bytes_list st (w2n w) (pre ++ rest) (w2n k) b` by
    (qpat_x_assum `dead_bytes _ _ (TupleTV _) _ _` mp_tac >>
     simp[Once dead_bytes_def]) >>
  drule tuple_dead_suffix >> simp[] >>
  gvs[Once dead_bytes_def]
QED

Theorem tuple_live_suffix:
  storage_read_live cx tr st w (TupleTV (pre ++ rest)) ==>
  storage_read_live cx tr st
    (w + n2w (type_slot_size_list pre)) (TupleTV rest)
Proof
  strip_tac >> Cases_on `type_slot_size_list rest = 0`
  >- (simp[storage_read_live_def, type_slot_size_def] >>
      rpt strip_tac >> gvs[] >>
      qspec_then `w + n2w (type_slot_size_list pre)` mp_tac
        wordsTheory.w2n_lt >> simp[]) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[type_slot_size_def, type_slot_size_list_append] >>
  `w2n w + type_slot_size_list pre < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (type_slot_size_list pre)) =
    w2n w + type_slot_size_list pre` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes_list st (w2n w) (pre ++ rest) j b` by
    (qpat_x_assum `_ ==> dead_bytes _ _ _ _ _` mp_tac >>
     simp[Once dead_bytes_def]) >>
  simp[Once dead_bytes_def] >> drule tuple_dead_suffix >> simp[]
QED
