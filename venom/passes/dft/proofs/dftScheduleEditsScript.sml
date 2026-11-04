(* Original/final order evidence for adjacent schedule edits. *)
Theory dftScheduleEdits
Ancestors
  dftScheduleOrder dftDefs list sorting relation

Definition inv_edit_def:
  inv_edit orig dest u v <=>
    ?p a b q. u = p ++ [a;b] ++ q /\ v = p ++ [b;a] ++ q /\
      id_before orig a b /\ id_before dest b a
End

(* The proposed unrestricted provenance claim needs distinct destination IDs. *)
Theorem inv_edit_provenance_counterexample:
  (!a b. id_before [1;2] a b /\ T ==> id_before [1;2;1] a b) /\
  inv_edit [1;2] [1;2;1] [1;2] [2;1] /\
  ~(?p a b q. [1;2] = p ++ [a;b] ++ q /\
     [2;1] = p ++ [b;a] ++ q /\ ~T)
Proof
  conj_tac
  >- (simp[id_before_cons] >> rpt strip_tac >> gvs[] >>
      simp[id_before_cons]) >>
  simp[inv_edit_def] >> qexistsl [`[]`, `1`, `2`, `[]`] >>
  simp[id_before_cons]
QED

Theorem schedule_before_asym[local]:
  ALL_DISTINCT xs /\ id_before xs a b ==> ~id_before xs b a
Proof
  strip_tac >> pure_rewrite_tac[id_before_def] >> strip_tac >>
  qpat_x_assum `id_before _ _ _` mp_tac >>
  pure_rewrite_tac[id_before_def] >> strip_tac >>
  `i < LENGTH xs /\ i' < LENGTH xs` by simp[] >>
  `i = j' /\ j = i'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
QED

Theorem inv_edit_provenance:
  ALL_DISTINCT dest /\
  (!a b. id_before orig a b /\ R a b ==> id_before dest a b) /\
  inv_edit orig dest u v ==>
  ?p a b q. u = p ++ [a;b] ++ q /\ v = p ++ [b;a] ++ q /\
    id_before orig a b /\ id_before dest b a /\ ~R a b
Proof
  rw[inv_edit_def] >> qexistsl [`p`, `a`, `b`, `q`] >>
  simp[] >> metis_tac[schedule_before_asym]
QED

Theorem inv_edit_perm:
  inv_edit orig dest u v ==> PERM u v
Proof
  rw[inv_edit_def] >> simp[PERM_APPEND_IFF, PERM_SWAP_AT_FRONT]
QED

Theorem inv_edit_distinct:
  inv_edit orig dest u v ==> (ALL_DISTINCT u <=> ALL_DISTINCT v)
Proof
  metis_tac[inv_edit_perm, ALL_DISTINCT_PERM]
QED

Theorem inv_edit_context:
  inv_edit orig dest u v ==>
  inv_edit orig dest (pre ++ u ++ post) (pre ++ v ++ post)
Proof
  rw[inv_edit_def] >> qexistsl [`pre ++ p`, `a`, `b`, `q ++ post`] >>
  simp[APPEND_ASSOC]
QED

Theorem inv_edit_rtc_context:
  RTC (inv_edit orig dest) u v ==>
  RTC (inv_edit orig dest) (pre ++ u ++ post) (pre ++ v ++ post)
Proof
  map_every qid_spec_tac [`v`, `u`] >>
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- simp[] >>
  metis_tac[RTC_RULES, inv_edit_context]
QED

Theorem schedule_before_append[local]:
  id_before (p ++ q) a b <=>
  id_before p a b \/ (MEM a p /\ MEM b q) \/ id_before q a b
Proof
  Induct_on `p` >- simp[id_before_def] >>
  simp[id_before_cons] >> metis_tac[]
QED

Theorem inv_edit_bubble[local]:
  (!a. MEM a p ==> id_before orig a h /\ id_before dest h a) ==>
  RTC (inv_edit orig dest) (p ++ h::q) (h::(p ++ q))
Proof
  Induct_on `p` >- simp[] >> rpt strip_tac >>
  `RTC (inv_edit orig dest) (p ++ h::q) (h::(p ++ q))` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  drule inv_edit_rtc_context >>
  disch_then (qspecl_then [`[h']`, `[]`] mp_tac) >>
  simp[] >> strip_tac >>
  irule RTC_TRANS >> qexists `h'::h::(p ++ q)` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule RTC_SINGLE >> simp[inv_edit_def] >>
  qexistsl [`[]`, `h'`, `h`, `p ++ q`] >> simp[]
QED

Theorem inv_edit_factor_embedded[local]:
  !ys xs. ALL_DISTINCT xs /\ PERM xs ys /\
    (!a b. id_before xs a b ==> id_before orig a b) /\
    (!a b. id_before ys a b ==> id_before dest a b) ==>
    RTC (inv_edit orig dest) xs ys
Proof
  Induct_on `ys`
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `MEM h xs` by metis_tac[PERM_MEM_EQ, MEM] >>
  qpat_x_assum `MEM h xs` mp_tac >> rewrite_tac[MEM_SPLIT] >>
  strip_tac >> gvs[] >>
  rename1 `PERM (p ++ h::q) (h::ys)` >>
  `PERM (p ++ q) ys` by
    (qpat_x_assum `PERM _ _` mp_tac >>
     once_rewrite_tac[PERM_SYM] >> simp[PERM_TO_APPEND_SIMPS]) >>
  `RTC (inv_edit orig dest) (p ++ h::q) (h::(p ++ q))` by
    (irule inv_edit_bubble >> gen_tac >> disch_tac >> conj_tac
     >- (first_x_assum irule >> simp[schedule_before_append, id_before_cons]) >>
     first_x_assum irule >> simp[id_before_cons] >>
     metis_tac[PERM_MEM_EQ, MEM_APPEND]) >>
  `RTC (inv_edit orig dest) (p ++ q) ys` by
    (qpat_x_assum `!xs. _` irule >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum irule >>
         gvs[schedule_before_append, id_before_cons] >> metis_tac[]) >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> simp[id_before_cons]) >>
     gvs[ALL_DISTINCT_APPEND]) >>
  drule inv_edit_rtc_context >>
  disch_then (qspecl_then [`[h]`, `[]`] mp_tac) >> simp[] >>
  strip_tac >> irule RTC_TRANS >> qexists `h::(p ++ q)` >>
  pure_asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem inv_edit_factor:
  ALL_DISTINCT orig /\ PERM orig dest ==>
  RTC (inv_edit orig dest) orig dest
Proof
  strip_tac >> irule inv_edit_factor_embedded >> simp[]
QED
