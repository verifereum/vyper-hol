(* Directed adjacent inversions, independent of instruction semantics. *)
Theory dftFramePerm
Ancestors
  dftScheduleOrder dftSsaPreserve dftPermSim relation sorting list

Definition adjacent_swap_def:
  adjacent_swap R l r <=>
    ?p a b q. l = p ++ [a;b] ++ q /\ r = p ++ [b;a] ++ q /\ R a b
End

Definition inv_swap_def:
  inv_swap s t = adjacent_swap (\a b. id_before s a b /\ id_before t b a)
End

Theorem adjacent_swap_context:
  adjacent_swap R l r ==> adjacent_swap R (p ++ l ++ q) (p ++ r ++ q)
Proof
  rw[adjacent_swap_def] >>
  qexistsl [`p ++ p'`, `a`, `b`, `q' ++ q`] >> simp[APPEND_ASSOC]
QED

Theorem adjacent_swap_RTC_context:
  !l r. RTC (adjacent_swap R) l r ==>
    RTC (adjacent_swap R) (p ++ l ++ q) (p ++ r ++ q)
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  metis_tac[adjacent_swap_context, RTC_SINGLE, RTC_TRANS]
QED

Theorem adjacent_swap_bubble:
  !p. EVERY (\a. R a b) p ==>
    RTC (adjacent_swap R) (p ++ b::q) (b::(p ++ q))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  irule RTC_TRANS >> qexists_tac `h::b::p ++ q` >> conj_tac
  >- (first_x_assum (drule_then assume_tac) >>
      drule adjacent_swap_RTC_context >>
      disch_then (qspecl_then [`[]`, `[h]`] mp_tac) >> simp[]) >>
  irule RTC_SINGLE >> simp[adjacent_swap_def] >>
  qexistsl [`[]`, `h`, `b`, `p ++ q`] >> simp[]
QED

Theorem adjacent_swap_extract:
  !t s. ALL_DISTINCT s /\ PERM s t /\
    (!a b. id_before s a b /\ id_before t b a ==> R a b) ==>
    RTC (adjacent_swap R) s t
Proof
  Induct >- simp[] >> rpt strip_tac >>
  `MEM h s` by metis_tac[PERM_MEM_EQ, MEM] >>
  `?p q. s = p ++ [h] ++ q` by metis_tac[GEN_ALL MEM_SPLIT_APPEND_first] >>
  gvs[] >>
  `PERM (p ++ q) t` by metis_tac[perm_cons_delete] >>
  `ALL_DISTINCT (p ++ q)` by gvs[ALL_DISTINCT_APPEND] >>
  `EVERY (\a. R a h) p` by
    (simp[EVERY_MEM] >> rpt strip_tac >> first_x_assum irule >>
     simp[id_before_append, id_before_cons] >>
     `MEM a (h::t)` by metis_tac[PERM_MEM_EQ, MEM_APPEND, MEM] >>
     `a <> h` by (gvs[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
     gvs[]) >>
  irule RTC_TRANS >> qexists_tac `h::(p ++ q)` >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> irule (GEN_ALL adjacent_swap_bubble) >> simp[]) >>
  `RTC (adjacent_swap R) (p ++ q) t` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >>
     gvs[id_before_append, id_before_cons] >> metis_tac[]) >>
  drule adjacent_swap_RTC_context >>
  disch_then (qspecl_then [`[]`, `[h]`] mp_tac) >> simp[]
QED

Theorem inv_swap_extract:
  ALL_DISTINCT s /\ PERM s t ==> RTC (inv_swap s t) s t
Proof
  simp[inv_swap_def] >> strip_tac >> irule adjacent_swap_extract >> simp[]
QED
