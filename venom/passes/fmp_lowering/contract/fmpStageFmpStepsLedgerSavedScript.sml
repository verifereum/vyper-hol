(*
 * The saved caller frames across a restore: a restore drops only sites at
 * or above the current frame's base, which no saved frame points into.
 *
 * TOP-LEVEL:
 *   fmp_saved_source_bounds    - saved frames point below the frame base
 *   fmp_caller_lookup_restrict - a cut keeps the sites below the base
 *   fmp_restore_saved_rel      - the saved frames under a restore's cut
 *   fmp_restore_params_rel     - the parameters under a restore's cut
 *)
Theory fmpStageFmpStepsLedgerSaved
Ancestors
  fmpStageFmpStepsLedgerRestrict fmpStageFmpStepsRetSource
  fmpStageRel fmpStageReclaimSound ptrDiscipline finite_map list pred_set

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
  `?tn0. tn0.t_var = h.cf_tvar /\
     frame_reachable vs C t h.cf_params h.cf_prov tn0
       h.cf_fn h.cf_inst h.cf_state /\
     active_inst h.cf_fn h.cf_inst h.cf_state /\
     h.cf_inst.inst_opcode = INVOKE` by
    (drule fmp_stage_saved_source >>
     disch_then (qspecl_then [`[]`, `h`, `t`] mp_tac) >> simp[]) >>
  drule_all fmp_stage_frame_sites >> strip_tac >>
  `?pre rest. h::t = pre ++ f::rest` by metis_tac[MEM_SPLIT] >>
  `?tn1. tn1.t_var = f.cf_tvar /\
     frame_reachable vs C rest f.cf_params f.cf_prov tn1
       f.cf_fn f.cf_inst f.cf_state /\
     active_inst f.cf_fn f.cf_inst f.cf_state /\
     f.cf_inst.inst_opcode = INVOKE` by
    (qpat_assum `frame_reachable vs C (h::t) _ _ _ _ _ _`
       (mp_tac o MATCH_MP fmp_stage_saved_source) >>
     disch_then (qspecl_then [`pre`, `f`, `rest`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `w2n f.cf_state.vs_fmp <= w2n h.cf_state.vs_fmp` by
    (fs[EVERY_MEM] >> Cases_on `f = h` >> gvs[]) >>
  drule_all fmp_stage_frame_sites >> strip_tac >>
  fs[fmp_frame_base_def, EVERY_MEM] >>
  metis_tac[MEM_EL, arithmeticTheory.LESS_EQ_TRANS]
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
  `!f k b z. MEM f stk /\ k < LENGTH f.cf_params /\
     EL k f.cf_params = SOME (b,z) /\ 0 < z ==>
     b + z <= fmp_frame_base (w2n fmp) stk` by metis_tac[MEM_EL] >>
  `fmp_saved_rel C' sm fmp0 (w2n fmp) stk ts` by fs[fmp_stage_rel_def] >>
  irule fmp_saved_rel_drestrict >> simp[] >> rpt strip_tac >>
  irule fmp_caller_lookup_restrict >> metis_tac[]
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
  irule fmp_params_rel_transport >> qexists `sm` >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[MEM_EL]
QED
