(*
 * Dropping sites from FmpLowering's site map sm: a restore keeps the sites
 * below its new runner, a return the caller's.  The relations survive as
 * long as every site a related value points into keeps its entry.
 *
 * TOP-LEVEL:
 *   fmp_restrict_identity        - restricting to sites below lo keeps all
 *   fmp_value_rel_transport      - a value relation under another site map
 *   fmp_env_rel_transport        - the environment relation likewise
 *   fmp_params_rel_transport     - the parameter relation likewise
 *   fmp_sites_ok_restrict        - the site invariant below a cut
 *   fmp_sites_ok_return_restrict - the site invariant below a caller's fmp
 *   fmp_frame_covers_drestrict   - coverage of a restricted map
 *   fmp_ledger_link_drestrict    - ledger link of a restricted map
 *   fmp_memory_agree_drestrict   - memory agreement of a restricted map
 *   fmp_frame_rel_drestrict      - a frame relation of a restricted map
 *   fmp_saved_rel_drestrict      - the saved frames of a restricted map
 *)
Theory fmpStageFmpStepsLedgerRestrict
Ancestors
  fmpStageRel o1LowerDloadRelocationKernel
  finite_map pred_set pair list words

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
  (!v x b z. FLOOKUP s.vs_vars v = SOME x /\ MEM v live /\
     ~retpc_var fn v /\ FLOOKUP G v = SOME (b,z) /\ 0 < z ==>
     FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)) ==>
  fmp_env_rel sm' fn live G tv s t
Proof
  rw[fmp_env_rel_def] >>
  qpat_x_assum `!v x. FLOOKUP s.vs_vars v = SOME x ==> ?y. _` drule >>
  strip_tac >>
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

Theorem fmp_sites_ok_return_restrict:
  fmp_sites_ok sm fmp0 raw0 lo raw_fmp /\
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) /\ b < w2n caller_fmp ==>
     c + z <= lc /\ b + z <= w2n caller_fmp) ==>
  fmp_sites_ok (DRESTRICT sm {key | FST key < w2n caller_fmp})
    fmp0 raw0 lc caller_fmp
Proof
  simp[fmp_sites_ok_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_frame_covers_drestrict:
  fmp_frame_covers sm env eb lo G ==>
  fmp_frame_covers (DRESTRICT sm keep) env eb lo G
Proof
  simp[fmp_frame_covers_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_ledger_link_drestrict:
  fmp_ledger_link sm eb lo regions ==>
  fmp_ledger_link (DRESTRICT sm keep) eb lo regions
Proof
  simp[fmp_ledger_link_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_memory_agree_drestrict:
  ld_memory_agree (fmp_ld_sites sm) eom mask mem mem' ==>
  ld_memory_agree (fmp_ld_sites (DRESTRICT sm keep)) eom mask mem mem'
Proof
  rw[ld_memory_agree_def] >>
  PairCases_on `id` >>
  gvs[FLOOKUP_fmp_ld_sites, FLOOKUP_DRESTRICT, AllCaseEqs()] >>
  first_x_assum irule >>
  simp[] >> qexistsl [`(b,id1)`, `id1`] >> simp[FLOOKUP_fmp_ld_sites]
QED

Theorem fmp_frame_rel_drestrict:
  fmp_frame_rel sm fmp0 raw0 eb elo lo restored fn fn' PG G tv s t /\
  (!v x b z. FLOOKUP s.vs_vars v = SOME x /\
     MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx) /\
     ~retpc_var fn v /\ FLOOKUP G v = SOME (b,z) /\ 0 < z ==>
     FLOOKUP (DRESTRICT sm keep) (b,z) = FLOOKUP sm (b,z)) /\
  (!k b z. k < LENGTH s.vs_params /\ k < LENGTH PG /\
     EL k PG = SOME (b,z) /\ 0 < z ==>
     FLOOKUP (DRESTRICT sm keep) (b,z) = FLOOKUP sm (b,z)) ==>
  fmp_frame_rel (DRESTRICT sm keep) fmp0 raw0 eb elo lo restored
    fn fn' PG G tv s t
Proof
  rw[fmp_frame_rel_def] >>
  qexistsl [`infos`, `ctx`, `runner`] >> simp[] >>
  rpt conj_tac
  >- (irule fmp_env_rel_transport >> metis_tac[])
  >- (irule fmp_params_rel_transport >> metis_tac[])
  >- (rpt strip_tac >> gvs[FLOOKUP_DRESTRICT, AllCaseEqs()] >> metis_tac[]) >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  conj_tac >- metis_tac[fmp_frame_covers_drestrict] >>
  IF_CASES_TAC >> gvs[] >>
  qexists `regions` >> simp[] >>
  metis_tac[fmp_ledger_link_drestrict]
QED

Theorem fmp_saved_rel_drestrict:
  fmp_saved_rel C' sm fmp0 raw0 stk ts /\
  (!f v x b z. MEM f stk /\ FLOOKUP f.cf_state.vs_vars v = SOME x /\
     MEM v (live_vars_at (liveness_analyze f.cf_fn)
       f.cf_state.vs_current_bb f.cf_state.vs_inst_idx) /\
     ~retpc_var f.cf_fn v /\ FLOOKUP f.cf_prov v = SOME (b,z) /\
     0 < z ==> FLOOKUP (DRESTRICT sm keep) (b,z) = FLOOKUP sm (b,z)) /\
  (!f k b z. MEM f stk /\ k < LENGTH f.cf_state.vs_params /\
     k < LENGTH f.cf_params /\ EL k f.cf_params = SOME (b,z) /\
     0 < z ==> FLOOKUP (DRESTRICT sm keep) (b,z) = FLOOKUP sm (b,z)) ==>
  fmp_saved_rel C' (DRESTRICT sm keep) fmp0 raw0 stk ts
Proof
  qid_spec_tac `ts` >> Induct_on `stk` >>
  Cases_on `ts` >> simp[fmp_saved_rel_def] >>
  rpt strip_tac >> PairCases_on `h` >> gvs[fmp_saved_rel_def] >>
  conj_tac
  >- (irule fmp_frame_rel_drestrict >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[MEM]
QED
