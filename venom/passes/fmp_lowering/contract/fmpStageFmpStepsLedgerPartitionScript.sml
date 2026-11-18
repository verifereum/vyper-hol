Theory fmpStageFmpStepsLedgerPartition
Ancestors
  fmpStageRel fmpRestoreProps fmpProvenanceProps fmpAliasProps
  fmpLedgerProps fmpReclaimProps fmpReclaimDefs rich_list finite_map pred_set list arithmetic

Theorem fmp_stage_cut_bounds:
  fmp_ledger_ok insts env t lo (ps ++ ks) /\ ps <> [] /\
  EVERY (\r. elo <= r.fr_lo) (ps ++ ks) ==>
  elo <= (LAST ps).fr_lo /\ (LAST ps).fr_lo <= lo
Proof
  strip_tac >> drule_all fmp_ledger_split >> strip_tac >>
  fs[EVERY_MEM] >> metis_tac[LAST_MEM, MEM_APPEND]
QED

Theorem fmp_stage_cut_region_bounds:
  fmp_ledger_ok insts env t lo (ps ++ ks) /\ ps <> [] ==>
  EVERY (\r. (LAST ps).fr_lo <= r.fr_lo) ps /\
  EVERY (\r. r.fr_hi <= (LAST ps).fr_lo) ks
Proof
  strip_tac >> drule_all fmp_ledger_split >> strip_tac >>
  drule fmp_ledger_bounds >> simp[EVERY_MEM] >> strip_tac >>
  fs[EVERY_MEM]
QED

Theorem fmp_stage_cut_bottom:
  fmp_ledger_ok insts env t lo (ps ++ ks) /\ ps <> [] ==>
  (LAST (ps ++ ks)).fr_lo <= (LAST ps).fr_lo
Proof
  strip_tac >> Cases_on `ks = []` >- gvs[] >>
  drule_all fmp_ledger_split >> strip_tac >>
  drule fmp_ledger_bounds >> simp[EVERY_MEM] >> strip_tac >>
  simp[LAST_APPEND_NOT_NIL] >>
  first_x_assum (qspec_then `LAST ks` mp_tac) >> simp[LAST_MEM] >>
  decide_tac
QED

Theorem fmp_stage_cut_site_end:
  fmp_ledger_ok insts env t lo (ps ++ ks) /\ ps <> [] /\
  EVERY (\r. elo <= r.fr_lo) (ps ++ ks) /\
  fmp_ledger_link sm eb lo (ps ++ ks) /\
  FLOOKUP sm (b,z) = SOME (c,id) /\ c < (LAST ps).fr_lo /\
  (b < eb ==> c + z <= elo) ==>
  c + z <= (LAST ps).fr_lo
Proof
  strip_tac >>
  drule_all fmp_stage_cut_bounds >> strip_tac >>
  Cases_on `b < eb` >- (res_tac >> decide_tac) >>
  drule_all fmp_stage_cut_bottom >> strip_tac >>
  drule_all fmp_stage_cut_region_bounds >> strip_tac >>
  qpat_x_assum `fmp_ledger_link _ _ _ _` mp_tac >>
  simp[fmp_ledger_link_def] >>
  disch_then (qspecl_then [`b`, `z`, `c`, `id`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `c < (LAST (ps ++ ks)).fr_lo`
  >- (fs[] >> decide_tac) >>
  `?r. MEM r (ps ++ ks) /\ r.fr_lo = c /\ r.fr_hi = c + z` by
    (fs[] >> metis_tac[]) >>
  fs[MEM_APPEND, EVERY_MEM] >> metis_tac[NOT_LESS, LESS_EQ_TRANS]
QED

Theorem fmp_stage_cut_ledger_link:
  fmp_ledger_ok insts env t lo (ps ++ ks) /\ ps <> [] /\
  fmp_ledger_link sm eb lo (ps ++ ks) /\
  (!b z c id. FLOOKUP sm' (b,z) = SOME (c,id) ==>
     FLOOKUP sm (b,z) = SOME (c,id)) ==>
  fmp_ledger_link sm' eb (LAST ps).fr_lo ks
Proof
  strip_tac >> drule_all fmp_ledger_split >> strip_tac >>
  drule_all fmp_stage_cut_region_bounds >> strip_tac >>
  simp[fmp_ledger_link_def] >> rpt gen_tac >> strip_tac >>
  `c < lo /\ FLOOKUP sm (b,z) = SOME (c,id)` by
    metis_tac[LESS_LESS_EQ_TRANS] >>
  Cases_on `ks = []`
  >- (qpat_x_assum `fmp_ledger_link _ _ _ _` mp_tac >>
      simp[fmp_ledger_link_def] >>
      disch_then (qspecl_then [`b`, `z`, `c`, `id`] mp_tac) >>
      simp[] >> gvs[]) >>
  qpat_x_assum `fmp_ledger_link _ _ _ _` mp_tac >>
  simp[fmp_ledger_link_def] >>
  disch_then (qspecl_then [`b`, `z`, `c`, `id`] mp_tac) >>
  simp[LAST_APPEND_NOT_NIL] >> strip_tac >>
  strip_tac >>
  `?r. MEM r (ps ++ ks) /\ r.fr_lo = c /\ r.fr_hi = c + z /\
       r.fr_site = id` by metis_tac[MEM_APPEND] >>
  qexists `r` >> fs[MEM_APPEND, EVERY_MEM] >>
  metis_tac[NOT_LESS]
QED

Theorem fmp_stage_popped_not_live:
  fmp_ledger_ok (fn_insts fn) env t lo (ps ++ ks) /\
  MAP (\r. r.fr_mark) ps = popped /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  MEM v (live_vars_at live (FST p) (SND p)) /\
  MEM id (fmp_bases env v) /\ MEM r ps ==>
  r.fr_site <> id
Proof
  strip_tac >>
  `MEM r (ps ++ ks) /\ MEM r.fr_mark popped` by
    (conj_tac >- simp[] >>
     qpat_x_assum `MAP _ ps = popped` (fn th => rewrite_tac[GSYM th]) >>
     simp[MEM_MAP] >> qexists `r` >> simp[]) >>
  drule_all fmp_ledger_mark >> strip_tac >>
  drule_all fmp_pop_member_dead >>
  simp[fmp_mark_dead_def] >> strip_tac >>
  metis_tac[fmp_allocation_live_variable]
QED

Theorem fmp_stage_cut_live_site:
  fmp_ledger_ok (fn_insts fn) env t lo (ps ++ ks) /\ ps <> [] /\
  EVERY (\r. elo <= r.fr_lo) (ps ++ ks) /\
  fmp_ledger_link sm eb lo (ps ++ ks) /\
  fmp_frame_covers sm env eb lo G /\
  fmp_sites_ok sm fmp0 raw0 lo raw /\
  MAP (\r. r.fr_mark) ps = popped /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  MEM v (live_vars_at live (FST p) (SND p)) /\
  FLOOKUP G v = SOME (b,z) /\ FLOOKUP sm (b,z) = SOME (c,id) /\
  (b < eb ==> c + z <= elo) ==>
  c < (LAST ps).fr_lo
Proof
  strip_tac >>
  `0 < z /\ c + z <= lo` by
    (fs[fmp_sites_ok_def] >> metis_tac[]) >>
  drule_all fmp_stage_cut_bounds >> strip_tac >>
  Cases_on `b < eb` >- (res_tac >> decide_tac) >>
  `MEM id (fmp_bases env v)` by
    (fs[fmp_frame_covers_def] >>
     first_x_assum (qspecl_then [`v`, `b`, `z`, `c`, `id`] mp_tac) >> simp[]) >>
  drule_all fmp_stage_cut_bottom >> strip_tac >>
  drule_all fmp_stage_cut_region_bounds >> strip_tac >>
  spose_not_then assume_tac >>
  `?r. MEM r (ps ++ ks) /\ r.fr_lo = c /\ r.fr_hi = c + z /\
       r.fr_site = id` by
    (qpat_x_assum `fmp_ledger_link _ _ _ _` mp_tac >>
     simp[fmp_ledger_link_def] >>
     disch_then (qspecl_then [`b`, `z`, `c`, `id`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `MEM r ps` by
    (fs[MEM_APPEND, EVERY_MEM] >>
     qpat_x_assum `!r. MEM r ks ==> r.fr_hi <= _`
       (qspec_then `r` mp_tac) >> simp[] >> decide_tac) >>
  drule_all fmp_stage_popped_not_live >> simp[]
QED
