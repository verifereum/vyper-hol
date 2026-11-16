Theory fmpStageFmpStepsDallocaSaved
Ancestors fmpStageRel fmpStageReclaimSound o1LowerDloadRelocationKernel finite_map list

Theorem fmp_dalloca_value_extend[local]:
  (!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm' k = SOME v) /\
  fmp_value_rel sm h m x y ==> fmp_value_rel sm' h m x y
Proof
  Cases_on `h` >- simp[fmp_value_rel_def, ld_value_agree_def] >>
  rename1 `SOME site` >> PairCases_on `site` >>
  simp[fmp_value_rel_def, ld_value_agree_def, FLOOKUP_fmp_ld_sites] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_dalloca_env_extend[local]:
  (!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm' k = SOME v) /\
  fmp_env_rel sm fn live G tv s t ==> fmp_env_rel sm' fn live G tv s t
Proof
  simp[fmp_env_rel_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> qexists_tac `y` >> simp[] >>
  strip_tac >> irule fmp_dalloca_value_extend >>
  qexists_tac `sm` >> simp[]
QED

Theorem fmp_dalloca_params_extend[local]:
  (!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm' k = SOME v) /\
  fmp_params_rel sm PG s t ==> fmp_params_rel sm' PG s t
Proof
  simp[fmp_params_rel_def] >> rpt strip_tac >>
  irule fmp_dalloca_value_extend >> qexists_tac `sm` >> simp[]
QED

Theorem fmp_dalloca_frame_extend[local]:
  fmp_frame_rel sm fmp0 raw0 eb elo lo restored fn fn' PG G tv s t /\
  (!k v. FLOOKUP sm k = SOME v ==>
     FLOOKUP (sm |+ ((b,z),(c,id))) k = SOME v) /\
  w2n s.vs_fmp <= b /\ lo <= c ==>
  fmp_frame_rel (sm |+ ((b,z),(c,id))) fmp0 raw0 eb elo lo
    restored fn fn' PG G tv s t
Proof
  simp[fmp_frame_rel_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`infos`,`ctx`,`runner`] >> simp[] >>
  rpt conj_tac
  >- (irule fmp_dalloca_env_extend >> qexists_tac `sm` >> simp[])
  >- (irule fmp_dalloca_params_extend >> qexists_tac `sm` >> simp[])
  >- (rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.NOT_LESS]) >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >>
  rename1 `fmp_stage_root infos ctx fn = SOME root` >>
  PairCases_on `root` >> gvs[] >>
  conj_tac
  >- (gvs[fmp_frame_covers_def] >> rpt strip_tac >>
      gvs[FLOOKUP_UPDATE] >>
      Cases_on `(b',z') = (b,z)` >> gvs[] >> metis_tac[]) >>
  IF_CASES_TAC >> gvs[] >> qexists_tac `regions` >> simp[] >>
  gvs[fmp_ledger_link_def] >> rpt strip_tac >>
  gvs[FLOOKUP_UPDATE] >>
  Cases_on `(b',z') = (b,z)` >> gvs[] >> metis_tac[]
QED

Theorem fmp_dalloca_saved_extend[local]:
  !stk ts.
  fmp_saved_rel C' sm fmp0 raw0 stk ts /\
  EVERY (\f. w2n f.cf_state.vs_fmp <= b) stk /\
  fmp_frame_lo fmp0 ts <= c /\
  (!k v. FLOOKUP sm k = SOME v ==>
     FLOOKUP (sm |+ ((b,z),(c,id))) k = SOME v) ==>
  fmp_saved_rel C' (sm |+ ((b,z),(c,id))) fmp0 raw0 stk ts
Proof
  Induct >> Cases_on `ts` >> simp[fmp_saved_rel_def] >>
  PairCases_on `h` >> simp[fmp_saved_rel_def] >> gen_tac >> strip_tac >>
  gvs[EVERY_DEF, fmp_frame_lo_def] >> conj_tac
  >- (irule fmp_dalloca_frame_extend >> simp[]) >>
  first_x_assum irule >> simp[] >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_frame_rel_def] >> rpt strip_tac >> decide_tac
QED

Theorem fmp_dalloca_saved:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  fmp_saved_rel C'
    (if z = 0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id)))
    fmp0 raw0 stk ts
Proof
  strip_tac >> Cases_on `z = 0` >> simp[]
  >- gvs[fmp_stage_rel_def] >>
  drule_all fmp_stage_frame_sites >> strip_tac >>
  gvs[fmp_stage_rel_def] >> irule fmp_dalloca_saved_extend >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> Cases_on `k` >> Cases_on `v` >> strip_tac >>
      simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[] >>
      gvs[fmp_sites_ok_def] >>
      qpat_x_assum `!b z c id. FLOOKUP sm _ = _ ==> _` drule >>
      simp[] >> decide_tac) >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_frame_rel_def] >> rpt strip_tac >> simp[]
QED
