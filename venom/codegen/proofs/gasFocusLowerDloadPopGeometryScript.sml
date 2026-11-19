(* Spatial and accounting geometry at the actual resumed caller. *)
Theory gasFocusLowerDloadPopGeometry
Ancestors
  lowerDloadSafetyRelation lowerDloadPtrRel lowerDloadReturnInvokePop
  finite_map pred_set list

Theorem ld_focus_pop_layout_global:
  dload_live_layout lo g.lf_src.vs_alloca_next g.lf_tgt.vs_alloca_next rows /\
  LENGTH rows = LENGTH (g::fs) /\
  (!k. k < LENGTH (g::fs) ==>
    (EL k rows).dr_source = (EL k (g::fs)).lf_src.vs_allocas /\
    (EL k rows).dr_target = (EL k (g::fs)).lf_tgt.vs_allocas) /\
  (!k a. k < LENGTH (g::fs) /\
    (a IN FRANGE (EL k (g::fs)).lf_H \/ MEM (SOME a) (EL k (g::fs)).lf_Q) ==>
    a IN ld_slots B (DROP k (g::fs))) /\
  FDOM B = ld_slots B (g::fs) ==>
  ld_global lo B (g::fs)
Proof
  strip_tac >>
  qpat_x_assum `dload_live_layout _ _ _ _` (strip_assume_tac o
    REWRITE_RULE [dload_live_layout_def]) >>
  rewrite_tac[ld_global_def, HD] >> conj_tac
  >- (gen_tac >> Cases_on `source` >>
      simp[ld_sites_def] >> fs[] >> rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (gen_tac >> Cases_on `source` >>
      simp[ld_sites_def] >> fs[] >> rpt strip_tac >> metis_tac[pairTheory.PAIR_EQ]) >>
  rewrite_tac[Once MEM_EL] >> rpt gen_tac >> strip_tac >>
  `a IN ld_slots B (DROP n (g::fs))` by metis_tac[] >>
  qpat_x_assum `a IN ld_slots B (DROP _ _)` mp_tac >>
  simp[NoAsms, ld_slots_def, flookup_thm] >> rpt strip_tac
QED

Theorem ld_focus_pop_charge_geometry:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (child::f::fs) N /\
  bind_outputs outs vals (merge_callee_state f.lf_src sc) = SOME sr /\
  bind_outputs outs vals (merge_callee_state f.lf_tgt tc) = SOME tr /\
  g = (f with <|lf_src := sr with vs_inst_idx := si;
    lf_tgt := tr with vs_inst_idx := ti;
    lf_H := DRESTRICT f.lf_H keep;
    lf_tv := DRESTRICT f.lf_tv keep|>) ==>
  ALL_DISTINCT (MAP (\h. h.lf_serial) (g::fs)) /\
  EVERY (\h. h.lf_serial < N /\
    ld_intervals lo h.lf_src /\ ld_intervals lo h.lf_tgt /\
    h.lf_src.vs_prev_bb = h.lf_tgt.vs_prev_bb /\
    h.lf_src.vs_current_bb = h.lf_tgt.vs_current_bb /\
    MEM h.lf_fn C.ctx_functions) (g::fs) /\
  (!k. k < LENGTH (g::fs) ==>
    (EL k (g::fs)).lf_tgt.vs_alloca_next =
    (EL k (g::fs)).lf_src.vs_alloca_next + 32 * ld_charge (DROP k (g::fs))) /\
  ld_charge (g::fs) <= ctx_dload_count C
Proof
  strip_tac >> drule_all ld_return_frame_geometry >> strip_tac >>
  qpat_x_assum `g = _` kall_tac >>
  qpat_x_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[ld_sync_def] >> strip_tac >>
  `ld_intervals lo g.lf_src /\ ld_intervals lo g.lf_tgt` by
    ((qpat_assum `ld_intervals lo f.lf_src`
       (strip_assume_tac o REWRITE_RULE [ld_intervals_def]) >>
     qpat_assum `ld_intervals lo f.lf_tgt`
       (strip_assume_tac o REWRITE_RULE [ld_intervals_def]) >>
     simp[ld_intervals_def] >> (metis_tac[]))) >>
  `ld_charge (g::fs) = ld_charge (f::fs)` by simp[ld_charge_def] >>
  simp[] >> conj_tac
  >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `SUC k < SUC (SUC (LENGTH fs))` by simp[] >>
      qpat_x_assum `!j. _ ==> (EL j (child::f::fs)).lf_tgt.vs_alloca_next = _`
        (qspec_then `SUC k` mp_tac) >>
      Cases_on `k` >> simp[DROP_cons, EL]) >>
  qpat_x_assum `ld_charge (child::f::fs) <= _` mp_tac >>
  simp[NoAsms, ld_charge_def] >> decide_tac
QED
