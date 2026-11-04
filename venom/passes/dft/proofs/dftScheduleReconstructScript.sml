(* Reconstruction always chooses original representatives, not operand flips. *)
Theory dftScheduleReconstruct
Ancestors
  dftScheduleEdits dftScheduleOrder dftDefs list sorting relation

Theorem dft_perm_map_reconstruct:
  PERM (MAP key orig) ids ==>
  ?mid. PERM orig mid /\ MAP key mid = ids
Proof
  map_every qid_spec_tac [`orig`, `ids`] >> Induct
  >- (simp[] >> rpt strip_tac >> gvs[] >> qexists `[]` >> simp[]) >>
  rpt strip_tac >>
  `MEM h (MAP key orig)` by metis_tac[PERM_MEM_EQ, MEM] >>
  gvs[MEM_MAP] >>
  qpat_x_assum `MEM _ orig` mp_tac >> rewrite_tac[MEM_SPLIT] >>
  strip_tac >> gvs[] >>
  rename1 `PERM (MAP key p ++ key y::MAP key s) (key y::ids)` >>
  `PERM (MAP key (p ++ s)) ids` by
    (qpat_x_assum `PERM _ _` mp_tac >>
     once_rewrite_tac[PERM_SYM] >> simp[MAP_APPEND, PERM_TO_APPEND_SIMPS]) >>
  first_x_assum drule >> strip_tac >>
  qexists `y::mid` >> simp[] >>
  metis_tac[PERM_TRANS, PERM_CONS_IFF, PERM_TO_APPEND_SIMPS, PERM_REFL]
QED

Theorem dft_unique_key_eq[local]:
  ALL_DISTINCT (MAP key orig) /\ MEM a orig /\ MEM b orig /\
  key a = key b ==> a = b
Proof
  simp[MEM_EL] >> rpt strip_tac >>
  `n < LENGTH (MAP key orig) /\ n' < LENGTH (MAP key orig)` by simp[] >>
  `EL n (MAP key orig) = EL n' (MAP key orig)` by gvs[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
QED

Theorem dft_unique_key_before:
  ALL_DISTINCT (MAP key orig) /\ PERM orig xs /\
  MEM a orig /\ MEM b orig ==>
  (id_before (MAP key xs) (key a) (key b) <=> id_before xs a b)
Proof
  strip_tac >> eq_tac
  >- (simp[id_before_def] >> rpt strip_tac >>
      `i < LENGTH xs` by decide_tac >>
      gvs[EL_MAP] >>
      `EL i xs = a /\ EL j xs = b` by
        (conj_tac >> irule dft_unique_key_eq >>
         qexistsl [`key`, `orig`] >> simp[] >>
         drule PERM_MEM_EQ >> disch_then (fn th => rewrite_tac[th]) >>
         rename1 `MEM (EL k xs) xs` >>
         simp[MEM_EL] >> qexists `k` >> simp[] >> decide_tac) >>
      qexistsl [`i`, `j`] >> simp[]) >>
  simp[id_before_def] >> rpt strip_tac >>
  qexistsl [`i`, `j`] >> simp[EL_MAP]
QED

Theorem dft_key_schedule_edges[local]:
  ALL_DISTINCT (MAP key orig) /\ PERM orig xs ==>
  (schedule_edges (MAP key orig)
    (\ka kb. ?a b. MEM a orig /\ MEM b orig /\
       key a = ka /\ key b = kb /\ R a b) (MAP key xs) <=>
   schedule_edges orig R xs)
Proof
  strip_tac >> simp[schedule_edges_def] >> eq_tac
  >- (rpt strip_tac >>
      `MEM a orig /\ MEM b orig` by metis_tac[id_before_mem] >>
      `id_before (MAP key orig) (key a) (key b)` by
        metis_tac[dft_unique_key_before, PERM_REFL] >>
      `id_before (MAP key xs) (key a) (key b)` by metis_tac[] >>
      metis_tac[dft_unique_key_before]) >>
  rpt strip_tac >> gvs[] >>
  `id_before orig a b` by
    metis_tac[dft_unique_key_before, PERM_REFL] >>
  metis_tac[dft_unique_key_before]
QED

Theorem dft_id_schedule_reconstruct:
  ALL_DISTINCT (MAP key orig) /\ PERM orig dest /\
  schedule_edges orig R dest /\
  RTC (inv_edit (MAP key orig) (MAP key dest)) (MAP key orig) ids ==>
  ?mid. PERM orig mid /\ MAP key mid = ids /\
        schedule_edges orig R mid
Proof
  strip_tac >>
  `PERM (MAP key orig) ids` by metis_tac[inv_edit_rtc_perm] >>
  drule dft_perm_map_reconstruct >> strip_tac >>
  qexists `mid` >> simp[] >>
  qabbrev_tac `KR = \ka kb. ?a b. MEM a orig /\ MEM b orig /\
    key a = ka /\ key b = kb /\ R a b` >>
  `schedule_edges (MAP key orig) KR (MAP key dest)` by
    (simp[Abbr `KR`] >> metis_tac[dft_key_schedule_edges]) >>
  `schedule_edges (MAP key orig) KR (MAP key orig)` by
    simp[schedule_edges_def] >>
  `ALL_DISTINCT (MAP key dest)` by metis_tac[PERM_MAP, ALL_DISTINCT_PERM] >>
  `schedule_edges (MAP key orig) KR ids` by
    (drule_all inv_edit_rtc_schedule_edges >> simp[]) >>
  gvs[Abbr `KR`] >> metis_tac[dft_key_schedule_edges]
QED
