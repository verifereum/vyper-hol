(*
 * Simplify-CFG PHI Run-Block Correctness
 *
 * run_block equivalence lemmas for simplify-phi.
 *)

Theory scfgPhiRunBlock
Ancestors
  scfgPhiStep
Libs
  venomSemTheory scfgDefsTheory scfgEquivTheory venomSemPropsTheory

Theorem run_block_simplify_phi:
  !bb s fn preds preds0 prev.
    s.vs_prev_bb = SOME prev /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_block_wf preds0 bb
  ==>
    result_equiv_cfg (run_block (simplify_phi_block preds bb) s)
                     (run_block bb s)
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> gvs[]
  >- ((* OK case *)
    sg `step_in_block (simplify_phi_block (pred_labels fn bb.bb_label) bb) s =
        (OK v, r)`
    >- (
      irule step_in_block_simplify_phi_ok >>
      conj_tac >- (qexists_tac `fn` >> simp[]) >>
      conj_tac >- simp[] >>
      conj_tac >- (qexists_tac `prev` >> simp[]) >>
      qexists_tac `preds0` >> simp[]
    )
    >- (
      gvs[] >>
      Cases_on `v.vs_halted` >> gvs[result_equiv_cfg_refl] >>
      Cases_on `r` >> gvs[result_equiv_cfg_refl] >>
      first_x_assum (qspecl_then [`fn`, `preds0`, `prev`] mp_tac) >>
      impl_tac >- (drule step_in_block_preserves_prev_bb >> simp[]) >>
      simp[]
    ))
  >- ((* Halt case *)
    drule step_in_block_simplify_phi >>
    disch_then (qspecl_then [`fn`, `pred_labels fn bb.bb_label`, `preds0`, `prev`] mp_tac) >>
    simp[] >> strip_tac >> Cases_on `res'` >> gvs[result_equiv_cfg_def])
  >- ((* Revert case *)
    drule step_in_block_simplify_phi >>
    disch_then (qspecl_then [`fn`, `pred_labels fn bb.bb_label`, `preds0`, `prev`] mp_tac) >>
    simp[] >> strip_tac >> Cases_on `res'` >> gvs[result_equiv_cfg_def])
  >- ((* Error case *)
    drule step_in_block_simplify_phi >>
    disch_then (qspecl_then [`fn`, `pred_labels fn bb.bb_label`, `preds0`, `prev`] mp_tac) >>
    simp[] >> strip_tac >> Cases_on `res'` >> gvs[result_equiv_cfg_def])
QED

Theorem run_block_simplify_phi_ok:
  !bb s fn preds preds0 prev s'.
    s.vs_prev_bb = SOME prev /\
    preds = pred_labels fn bb.bb_label /\
    MEM prev preds /\
    (!lbl. MEM lbl preds ==> MEM lbl preds0) /\
    phi_block_wf preds0 bb /\
    run_block bb s = OK s' ==>
    run_block (simplify_phi_block preds bb) s = OK s'
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  qpat_x_assum `run_block _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >>
  Cases_on `r` >> simp[]
  >- ((* Terminator case *)
    strip_tac >> gvs[] >>
    sg `step_in_block (simplify_phi_block (pred_labels fn bb.bb_label) bb) s =
        (OK s', T)`
    >- (
      irule step_in_block_simplify_phi_ok >>
      conj_tac >- (qexists_tac `fn` >> simp[]) >>
      conj_tac >- simp[] >>
      conj_tac >- (qexists_tac `prev` >> simp[]) >>
      qexists_tac `preds0` >> simp[]
    )
    >- simp[Once run_block_def]
  )
  >- ((* Non-terminal case *)
    strip_tac >>
    sg `step_in_block (simplify_phi_block (pred_labels fn bb.bb_label) bb) s =
        (OK v, F)`
    >- (
      irule step_in_block_simplify_phi_ok >>
      conj_tac >- (qexists_tac `fn` >> simp[]) >>
      conj_tac >- gvs[] >>
      conj_tac >- (qexists_tac `prev` >> gvs[]) >>
      qexists_tac `preds0` >> gvs[]
    )
    >- (
      qpat_x_assum `step_in_block (simplify_phi_block _ _) _ = _` mp_tac >>
      simp[Once run_block_def] >>
      disch_then (fn th => REWRITE_TAC [Once run_block_def, th]) >>
      simp[] >>
      first_x_assum (qspecl_then [`OK v`, `F`, `v`] mp_tac) >> simp[] >>
      `v.vs_prev_bb = s.vs_prev_bb` by
        (drule step_in_block_preserves_prev_bb >> simp[]) >>
      disch_then (qspecl_then [`fn`, `preds0`, `prev`] mp_tac) >> gvs[]
    )
  )
QED

val _ = export_theory();
