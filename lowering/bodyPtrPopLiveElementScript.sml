Theory bodyPtrPopLiveElement
Ancestors
  accountsRelProps compileEnv vyperStorage vyperLookupStorage vyperValue words arithmetic

Theorem pop_live_dynamic_element:
  !cx tr st w elem n k.
    storage_read_live cx tr st w (ArrayTV elem (Dynamic n)) /\
    k < n /\ k < w2n (lookup_storage w st) ==>
    storage_read_live cx tr st (w + n2w (k * type_slot_size elem + 1)) elem
Proof
  rpt gen_tac >> strip_tac >>
  `k * type_slot_size elem + type_slot_size elem <= n * type_slot_size elem` by
    (irule array_index_element_end_bound >> simp[]) >>
  Cases_on `type_slot_size elem = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + 1w` mp_tac w2n_lt >> decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  simp[type_slot_size_def] >> strip_tac >>
  `w2n w + (k * type_slot_size elem + 1) < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (k * type_slot_size elem + 1)) =
   w2n w + (k * type_slot_size elem + 1)` by
    (Cases_on `w` >> gvs[word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes st (w2n w) (ArrayTV elem (Dynamic n)) j b` by
    (first_x_assum irule >> decide_tac) >>
  gvs[Once dead_bytes_def] >>
  `w2n w + (i * type_slot_size elem + 1) <= j /\
   j < w2n w + ((i + 1) * type_slot_size elem + 1)` by
    (Cases_on `i < w2n (lookup_storage w st)` >> gvs[]
     >- (drule (cj 1 dead_bytes_range) >>
         simp[RIGHT_ADD_DISTRIB] >> decide_tac) >>
     gvs[MULT_COMM]) >>
  `i = k` suffices_by (strip_tac >> gvs[]) >>
  Cases_on `i < k`
  >- (`(i + 1) * type_slot_size elem <= k * type_slot_size elem` by
        (irule LESS_MONO_MULT >> decide_tac) >> decide_tac) >>
  Cases_on `k < i`
  >- (`(k + 1) * type_slot_size elem <= i * type_slot_size elem` by
        (irule LESS_MONO_MULT >> decide_tac) >>
      gvs[RIGHT_ADD_DISTRIB] >> decide_tac) >> decide_tac
QED
