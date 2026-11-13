Theory fmpStageFmpStepsLedgerSaved
Ancestors
  fmpStageRel fmpStageReclaimSound ptrDiscipline finite_map list pred_set

Theorem fmp_frame_rel_restrict:
  fmp_frame_rel sm fmp0 raw0 eb elo top restored fn fn' PG G tv s t /\
  sm' = DRESTRICT sm keys /\
  fmp_env_rel sm' fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tv s t /\ fmp_params_rel sm' PG s t ==>
  fmp_frame_rel sm' fmp0 raw0 eb elo top restored fn fn' PG G tv s t
Proof
  simp[fmp_frame_rel_def] >> rpt strip_tac >>
  qexistsl [`infos`, `ctx`, `runner`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  conj_tac
  >- (gvs[fmp_frame_covers_def, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  IF_CASES_TAC >> gvs[] >> qexists `regions` >> simp[] >>
  gvs[fmp_ledger_link_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem fmp_saved_reachable:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    !pre f rest. stk = pre ++ f::rest ==>
      (?un. frame_reachable vs C rest f.cf_params f.cf_prov
        un f.cf_fn f.cf_inst f.cf_state /\ un.t_var = f.cf_tvar) /\
      active_inst f.cf_fn f.cf_inst f.cf_state
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      Cases_on `pre` >> gvs[] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`f::pre`, `f'`, `rest`] mp_tac) >>
  simp[]
QED

Theorem fmp_frame_rel_restrict_provenance:
  fmp_frame_rel sm fmp0 raw0 eb elo top restored fn fn' PG G tv s t /\
  sm' = DRESTRICT sm keys /\
  (!v b z. FLOOKUP G v = SOME (b,z) /\ 0 < z ==>
     FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)) /\
  (!b z. MEM (SOME (b,z)) PG /\ 0 < z ==>
     FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)) ==>
  fmp_frame_rel sm' fmp0 raw0 eb elo top restored fn fn' PG G tv s t
Proof
  rpt strip_tac >>
  `fmp_env_rel sm fn
     (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tv s t /\ fmp_params_rel sm PG s t` by
    (fs[fmp_frame_rel_def] >> metis_tac[]) >>
  irule fmp_frame_rel_restrict >>
  reverse conj_tac
  >- (reverse conj_tac >- metis_tac[] >>
      fs[fmp_env_rel_def] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >> qexists `y` >> simp[] >>
      strip_tac >>
      Cases_on `FLOOKUP G v` >>
      gvs[fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def] >>
      PairCases_on `x'` >> Cases_on `x'1 = 0` >> gvs[] >>
      `FLOOKUP (DRESTRICT sm keys) (x'0,x'1) = FLOOKUP sm (x'0,x'1)` by
        metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO] >>
      gvs[FLOOKUP_fmp_ld_sites]) >>
  fs[fmp_params_rel_def] >> rpt strip_tac >>
  first_x_assum drule >>
  Cases_on `k < LENGTH PG` >> simp[]
  >- (Cases_on `EL k PG` >>
      gvs[fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def] >>
      PairCases_on `x` >> Cases_on `x1 = 0` >> gvs[] >>
      `MEM (SOME (x0,x1)) PG` by metis_tac[MEM_EL] >>
      `FLOOKUP (DRESTRICT sm keys) (x0,x1) = FLOOKUP sm (x0,x1)` by
        metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO] >>
      simp[FLOOKUP_fmp_ld_sites]) >>
  simp[fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def]
QED

Theorem fmp_saved_source_bounds:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  !f. MEM f stk ==>
    (!v b z. FLOOKUP f.cf_prov v = SOME (b,z) /\ 0 < z ==>
      b + z <= fmp_frame_base (w2n fmp) stk) /\
    (!b z. MEM (SOME (b,z)) f.cf_params /\ 0 < z ==>
      b + z <= fmp_frame_base (w2n fmp) stk)
Proof
  strip_tac >> qx_gen_tac `f` >> strip_tac >>
  Cases_on `stk` >- fs[] >>
  `(?un. frame_reachable vs C t h.cf_params h.cf_prov un
      h.cf_fn h.cf_inst h.cf_state /\ un.t_var = h.cf_tvar) /\
    active_inst h.cf_fn h.cf_inst h.cf_state` by
    (drule fmp_saved_reachable >>
     disch_then (qspecl_then [`[]`, `h`, `t`] mp_tac) >> simp[]) >>
  drule_all fmp_stage_frame_sites >> strip_tac >>
  `?pre rest. h::t = pre ++ f::rest` by metis_tac[MEM_SPLIT] >>
  `(?un. frame_reachable vs C rest f.cf_params f.cf_prov un
      f.cf_fn f.cf_inst f.cf_state /\ un.t_var = f.cf_tvar) /\
    active_inst f.cf_fn f.cf_inst f.cf_state` by
    (qpat_assum `frame_reachable vs C (h::t) _ _ _ _ _ _`
       (mp_tac o MATCH_MP fmp_saved_reachable) >>
     disch_then (qspecl_then [`pre`, `f`, `rest`] mp_tac) >> simp[]) >>
  `w2n f.cf_state.vs_fmp <= w2n h.cf_state.vs_fmp` by
    (fs[EVERY_MEM] >> Cases_on `f = h` >> gvs[]) >>
  drule_all fmp_stage_frame_sites >> strip_tac >>
  fs[fmp_frame_base_def, EVERY_MEM] >>
  metis_tac[MEM_EL, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem fmp_saved_rel_restrict_provenance:
  !stk ts.
    fmp_saved_rel C' sm fmp0 raw0 stk ts /\ sm' = DRESTRICT sm keys /\
    (!f v b z. MEM f stk /\ FLOOKUP f.cf_prov v = SOME (b,z) /\ 0 < z ==>
      FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)) /\
    (!f b z. MEM f stk /\ MEM (SOME (b,z)) f.cf_params /\ 0 < z ==>
      FLOOKUP sm' (b,z) = FLOOKUP sm (b,z)) ==>
    fmp_saved_rel C' sm' fmp0 raw0 stk ts
Proof
  Induct >> Cases_on `ts` >> simp[fmp_saved_rel_def] >>
  rpt strip_tac >> PairCases_on `h` >> gvs[fmp_saved_rel_def] >>
  conj_tac
  >- (irule fmp_frame_rel_restrict_provenance >>
      rpt conj_tac >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem fmp_caller_lookup_restrict:
  (!b z c id. FLOOKUP sm ((b:num),z) = SOME ((c:num),id) /\ b < eb ==>
    c + z <= elo) /\ elo <= cut /\ 0 < z /\ b + z <= eb ==>
  FLOOKUP (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut}) (b,z) =
    FLOOKUP sm (b,z)
Proof
  strip_tac >> Cases_on `FLOOKUP sm (b,z)`
  >- simp[FLOOKUP_DRESTRICT] >>
  PairCases_on `x` >>
  `b < eb` by decide_tac >>
  `x0 + z <= elo` by metis_tac[] >>
  `x0 < cut` by decide_tac >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_DEF]
QED

Theorem fmp_restore_saved_rel:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\
  fmp_stage_rel D C' sm fmp0 (w2n fmp) eom restored stk PG G tn fn s lo t ts /\
  fmp_frame_lo fmp0 ts <= cut ==>
  fmp_saved_rel C'
    (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut})
    fmp0 (w2n fmp) stk ts
Proof
  strip_tac >>
  `!f. MEM f stk ==>
    (!v b z. FLOOKUP f.cf_prov v = SOME (b,z) /\ 0 < z ==>
      b + z <= fmp_frame_base (w2n fmp) stk) /\
    (!b z. MEM (SOME (b,z)) f.cf_params /\ 0 < z ==>
      b + z <= fmp_frame_base (w2n fmp) stk)` by
    metis_tac[fmp_saved_source_bounds] >>
  `!b z c id. FLOOKUP sm (b,z) = SOME (c,id) /\
    b < fmp_frame_base (w2n fmp) stk ==> c + z <= fmp_frame_lo fmp0 ts` by
    (fs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  irule fmp_saved_rel_restrict_provenance >>
  qexistsl [`{key | key IN FDOM sm /\ FST (sm ' key) < cut}`, `sm`] >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule fmp_caller_lookup_restrict >> metis_tac[])
  >- (rpt strip_tac >> irule fmp_caller_lookup_restrict >> metis_tac[]) >>
  fs[fmp_stage_rel_def] >> metis_tac[]
QED

Theorem fmp_restore_params_rel:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 (w2n fmp) eom restored stk PG G tn fn s lo t ts /\
  fmp_frame_lo fmp0 ts <= cut ==>
  fmp_params_rel
    (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut}) PG s t
Proof
  strip_tac >> drule_all fmp_stage_frame_sites >> strip_tac >>
  `fmp_params_rel sm PG s t /\
    (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) /\
      b < fmp_frame_base (w2n fmp) stk ==> c + z <= fmp_frame_lo fmp0 ts)` by
    (fs[fmp_stage_rel_def, fmp_frame_rel_def] >> metis_tac[]) >>
  `!b z. MEM (SOME (b,z)) PG /\ 0 < z ==>
    FLOOKUP (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut}) (b,z) =
      FLOOKUP sm (b,z)` by
    (rpt strip_tac >> irule fmp_caller_lookup_restrict >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  fs[fmp_params_rel_def] >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `k < LENGTH PG` >> simp[]
  >- (Cases_on `EL k PG` >>
      gvs[fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def] >>
      PairCases_on `x` >> Cases_on `x1 = 0` >> gvs[] >>
      `MEM (SOME (x0,x1)) PG` by metis_tac[MEM_EL] >>
      `FLOOKUP (DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < cut})
        (x0,x1) = FLOOKUP sm (x0,x1)` by
        metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO] >>
      simp[FLOOKUP_fmp_ld_sites]) >>
  simp[fmp_value_rel_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def]
QED
