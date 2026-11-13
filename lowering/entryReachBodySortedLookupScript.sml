Theory entryReachBodySortedLookup
Ancestors
  sorting alist rich_list list pair

Theorem entry_sorted_tail_absent[local]:
  SORTED $< (a::MAP FST xs) /\ k <= a ==> ALOOKUP xs k = NONE
Proof
  simp[less_sorted_eq] >> rpt strip_tac >>
  Cases_on `ALOOKUP xs k` >> simp[] >>
  drule ALOOKUP_MEM >> strip_tac >>
  `MEM k (MAP FST xs)` by (simp[MEM_MAP] >> metis_tac[FST]) >>
  first_x_assum drule >> simp[]
QED

Theorem entry_sorted_lookup_unique:
  !xs ys : (num # 'a) list.
    SORTED $< (MAP FST xs) /\ SORTED $< (MAP FST ys) /\
    (!k. ALOOKUP xs k = ALOOKUP ys k) ==> xs = ys
Proof
  Induct
  >- (Cases >> simp[] >> Cases_on `h` >>
      disj2_tac >> qexists_tac `q` >> simp[]) >>
  Cases_on `h` >> Cases_on `ys`
  >- (simp[] >> disj2_tac >> qexists_tac `q` >> simp[]) >>
  Cases_on `h` >> simp[] >> strip_tac >>
  `q = q'` by
    (Cases_on `q < q'`
     >- (`ALOOKUP t q = NONE` by (irule entry_sorted_tail_absent >> goal_assum (drule_at Any) >> simp[]) >>
         qpat_x_assum `!k. _` (qspec_then `q` mp_tac) >> simp[] >> decide_tac) >>
     Cases_on `q' < q`
     >- (`ALOOKUP xs q' = NONE` by (irule entry_sorted_tail_absent >> goal_assum (drule_at Any) >> simp[]) >>
         qpat_x_assum `!k. _` (qspec_then `q'` mp_tac) >> simp[] >> decide_tac) >>
     decide_tac) >>
  gvs[] >> conj_tac
  >- (qpat_x_assum `!k. _` (qspec_then `q` mp_tac) >> simp[]) >>
  first_x_assum irule >> gvs[less_sorted_eq] >>
  gen_tac >> Cases_on `k = q` 
  >- (gvs[] >>
      `ALOOKUP xs k = NONE` by
        (irule entry_sorted_tail_absent >> qexists_tac `k` >> simp[less_sorted_eq]) >>
      `ALOOKUP t k = NONE` by
        (irule entry_sorted_tail_absent >> qexists_tac `k` >> simp[less_sorted_eq]) >> simp[]) >>
  qpat_x_assum `!k. _` (qspec_then `k` mp_tac) >> simp[]
QED
