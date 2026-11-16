Theory fmpStageFmpStepsRestoreCut
Ancestors
  fmpStageFmpStepsLedgerPartition fmpStageFmpStepsLedgerRestrict
  fmpStageRel finite_map pred_set list arithmetic

Theorem fmp_restore_cut_sites:
  fmp_ledger_ok insts env t lo (ps ++ ks) /\ ps <> [] /\
  EVERY (\r. elo <= r.fr_lo) (ps ++ ks) /\
  fmp_ledger_link sm eb lo (ps ++ ks) /\
  fmp_sites_ok sm fmp0 raw0 lo raw /\
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) /\ b < eb ==>
     c + z <= elo) /\
  sm' = DRESTRICT sm {key | key IN FDOM sm /\
                          FST (sm ' key) < (LAST ps).fr_lo} ==>
  fmp_sites_ok sm' fmp0 raw0 (LAST ps).fr_lo raw
Proof
  strip_tac >> irule fmp_sites_ok_restrict >>
  qexistsl [`lo`, `sm`] >> simp[] >> rpt strip_tac >>
  irule fmp_stage_cut_site_end >> metis_tac[]
QED

Theorem fmp_restore_cut_covers:
  fmp_frame_covers sm env eb lo G /\ cut <= lo /\
  sm' = DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut} ==>
  fmp_frame_covers sm' env eb cut G
Proof
  rw[fmp_frame_covers_def] >>
  gvs[FLOOKUP_DRESTRICT] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem fmp_restore_cut_link:
  fmp_ledger_ok insts env t lo (ps ++ ks) /\ ps <> [] /\
  fmp_ledger_link sm eb lo (ps ++ ks) /\
  sm' = DRESTRICT sm {key | key IN FDOM sm /\
                          FST (sm ' key) < (LAST ps).fr_lo} ==>
  fmp_ledger_link sm' eb (LAST ps).fr_lo ks
Proof
  strip_tac >> irule fmp_stage_cut_ledger_link >> simp[] >>
  qexistsl [`env`, `insts`, `lo`, `sm`, `t`] >> simp[] >>
  simp[FLOOKUP_DRESTRICT] >> rpt strip_tac >> gvs[]
QED

Theorem fmp_restore_cut_env:
  fmp_ledger_ok (fn_insts fn) env t lo (ps ++ ks) /\ ps <> [] /\
  EVERY (\r. elo <= r.fr_lo) (ps ++ ks) /\
  fmp_ledger_link sm eb lo (ps ++ ks) /\
  fmp_frame_covers sm env eb lo G /\
  fmp_sites_ok sm fmp0 raw0 lo raw /\
  MAP (\r. r.fr_mark) ps = popped /\
  fmp_pop_at infos fn live env p inst st = (popped,kept) /\
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) /\ b < eb ==>
     c + z <= elo) /\
  fmp_env_rel sm fn (live_vars_at live (FST p) (SND p)) G tv s t /\
  sm' = DRESTRICT sm {key | key IN FDOM sm /\
                          FST (sm ' key) < (LAST ps).fr_lo} ==>
  fmp_env_rel sm' fn (live_vars_at live (FST p) (SND p)) G tv s t
Proof
  strip_tac >> irule fmp_env_rel_transport >> qexists `sm` >> simp[] >>
  rpt strip_tac >> Cases_on `FLOOKUP sm (b,z)`
  >- gvs[FLOOKUP_DRESTRICT, FLOOKUP_DEF] >>
  rename1 `FLOOKUP sm (b,z) = SOME value` >> PairCases_on `value` >>
  `value0 < (LAST ps).fr_lo` by
    (`b < eb ==> value0 + z <= elo` by metis_tac[] >>
     drule_all fmp_stage_cut_live_site >> simp[]) >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_DEF]
QED

