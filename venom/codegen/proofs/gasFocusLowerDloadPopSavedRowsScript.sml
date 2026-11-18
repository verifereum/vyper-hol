(* The popped child's slots are not needed to interpret suspended rows. *)
Theory gasFocusLowerDloadPopSavedRows
Ancestors
  lowerDloadReturnInvokePop lowerDloadSafetyAllocation lowerDloadSafetyRelation
  lowerDloadSafetyKernel finite_map list pred_set

Theorem ld_focus_pop_saved_rows:
  ld_sync lo P C vs (c::cs) PG G tn fn ri s t A (child::f::fs) N /\
  (!a. a IN ld_slots A (f::fs) ==> FLOOKUP B a = FLOOKUP A a) /\
  (!h a. MEM h (f::fs) /\ (a IN FRANGE h.lf_H \/ MEM (SOME a) h.lf_Q) ==>
    FLOOKUP B a = FLOOKUP A a) ==>
  EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs) /\
  (!j. j < LENGTH (c::cs) ==>
    let cc = EL j (c::cs); h = EL j (f::fs) in
      cc.cf_fn = h.lf_fn /\ cc.cf_state = h.lf_src /\
      ld_ghost_ok (dyn_floor C vs) B h.lf_H cc.cf_prov /\
      ld_params_ok (dyn_floor C vs) B h.lf_Q cc.cf_params /\
      cc.cf_tvar = h.lf_tv)
Proof
  strip_tac >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ld_sync_def, EL_restricted]) >>
  conj_tac
  >- (rewrite_tac[EVERY_MEM] >> qx_gen_tac `h` >> disch_tac >>
      `ld_maps A h /\ ld_vars P A h` by
        (qpat_assum `EVERY _ (child::f::fs)` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
         disch_then (qspec_then `h` mp_tac) >> simp[]) >>
      BETA_TAC >> conj_tac
      >- (irule ld_maps_alloc_agree >> goal_assum (drule_at Any) >>
          rpt strip_tac >>
          qpat_assum `!a. a IN ld_slots A (f::fs) ==> _` irule >>
          fs[ld_slots_def] >> metis_tac[]) >>
      irule ld_vars_alloc_agree >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  `LENGTH (f::fs) = LENGTH (c::cs)` by fs[] >>
  `MEM (EL j (f::fs)) (f::fs)` by simp[EL_MEM] >>
  qpat_x_assum `!j. j < LENGTH (c::cs) ==> _` (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `h = EL j (f::fs)` >>
  `!a. a IN FRANGE h.lf_H \/ MEM (SOME a) h.lf_Q ==>
       FLOOKUP B a = FLOOKUP A a` by metis_tac[] >>
  `ld_erase B o_f h.lf_H = ld_erase A o_f h.lf_H` by
    (simp[fmap_eq_flookup, FLOOKUP_o_f] >> gen_tac >>
     Cases_on `FLOOKUP h.lf_H x` >> simp[] >>
     `FLOOKUP B x' = FLOOKUP A x'` by
       (first_x_assum irule >> simp[FRANGE_FLOOKUP] >> metis_tac[]) >>
     simp[ld_erase_def]) >>
  `MAP (OPTION_MAP (ld_erase B)) h.lf_Q =
   MAP (OPTION_MAP (ld_erase A)) h.lf_Q` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     Cases_on `x` >> simp[ld_erase_def]) >>
  metis_tac[ld_ghost_ok_erase_cong, ld_params_ok_erase_cong]
QED
