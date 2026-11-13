Theory fmpStageFmpStepsLedgerRestrict
Ancestors
  fmpStageRel o1LowerDloadMapEvolution o1LowerDloadRelocationKernel
  finite_map pred_set pair list

Theorem fmp_restrict_lookup:
  sm' = DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut} ==>
  (FLOOKUP sm' (b,z) = SOME (c,id) <=>
   FLOOKUP sm (b,z) = SOME (c,id) /\ c < cut)
Proof
  strip_tac >> gvs[FLOOKUP_DRESTRICT, FLOOKUP_DEF] >>
  eq_tac >> strip_tac >> gvs[]
QED

Theorem fmp_restrict_identity:
  fmp_sites_ok sm fmp0 raw0 lo raw ==>
  DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < lo} = sm
Proof
  strip_tac >> pure_rewrite_tac [fmap_eq_flookup] >> gen_tac >>
  Cases_on `x` >> simp[FLOOKUP_DRESTRICT] >>
  Cases_on `FLOOKUP sm (q,r)` >> simp[] >>
  rename1 `FLOOKUP sm (q,r) = SOME v` >> Cases_on `v` >>
  gvs[FLOOKUP_DEF, fmp_sites_ok_def] >>
  qpat_x_assum `!b z c id. _ ==> 0 < z /\ _` (qspecl_then [`q`,`r`,`q'`,`r'`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem fmp_value_rel_transport:
  fmp_value_rel sm h m x y /\
  (!b z. h = SOME (b,z) /\ 0 < z ==>
         FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)) ==>
  fmp_value_rel sm' h m x y
Proof
  Cases_on `h` >- simp[fmp_value_rel_def, ld_value_agree_def] >>
  rename1 `SOME p` >> PairCases_on `p` >>
  Cases_on `p1 = 0` >>
  simp[fmp_value_rel_def, ld_value_agree_def, FLOOKUP_fmp_ld_sites] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_env_rel_transport:
  fmp_env_rel sm fn live G tv s t /\
  (!v b z. MEM v live /\ ~retpc_var fn v /\
     FLOOKUP G v = SOME (b,z) /\ 0 < z ==>
     FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)) ==>
  fmp_env_rel sm' fn live G tv s t
Proof
  rw[fmp_env_rel_def] >> first_x_assum drule >> strip_tac >>
  qexists `y` >> simp[] >> rpt strip_tac >>
  irule fmp_value_rel_transport >> qexists `sm` >>
  metis_tac[]
QED

Theorem fmp_params_rel_transport:
  fmp_params_rel sm PG s t /\
  (!k b z. k < LENGTH s.vs_params /\ k < LENGTH PG /\
     EL k PG = SOME (b,z) /\ 0 < z ==>
     FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)) ==>
  fmp_params_rel sm' PG s t
Proof
  rw[fmp_params_rel_def] >>
  irule fmp_value_rel_transport >> qexists `sm` >>
  rpt strip_tac >> Cases_on `k < LENGTH PG` >> gvs[] >> metis_tac[]
QED

Theorem fmp_sites_ok_restrict:
  fmp_sites_ok sm fmp0 raw0 lo raw /\
  sm' = DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut} /\
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) /\ c < cut ==>
              c + z <= cut) ==>
  fmp_sites_ok sm' fmp0 raw0 cut raw
Proof
  strip_tac >> gvs[] >>
  `!b z c id. FLOOKUP (DRESTRICT sm
      {key | key IN FDOM sm /\ FST (sm ' key) < cut}) (b,z) = SOME (c,id) <=>
      FLOOKUP sm (b,z) = SOME (c,id) /\ c < cut` by
    (rpt gen_tac >> simp[FLOOKUP_DRESTRICT, FLOOKUP_DEF] >>
     eq_tac >> strip_tac >> gvs[]) >>
  gvs[fmp_sites_ok_def] >> metis_tac[]
QED

Theorem fmp_ld_sites_restrict:
  fmp_ld_sites (DRESTRICT sm keep) = DRESTRICT (fmp_ld_sites sm) keep
Proof
  pure_rewrite_tac [fmap_eq_flookup] >> gen_tac >> Cases_on `x` >>
  simp[FLOOKUP_fmp_ld_sites, FLOOKUP_DRESTRICT] >>
  Cases_on `(q,r) IN keep` >> simp[]
QED

Theorem fmp_memory_agree_restrict:
  ld_memory_agree (fmp_ld_sites sm) eom mask s t ==>
  ld_memory_agree (fmp_ld_sites (DRESTRICT sm keep)) eom mask s t
Proof
  simp[fmp_ld_sites_restrict, ld_memory_agree_restrict]
QED
