Theory loadElimOccurrencePositions
Ancestors
  loadElimOccurrence loadElimOccurrenceCoverage loadElimJoinPlacement venomExecProps venomExecProofs venomInst venomInstProps
  list rich_list

Theorem le_occ_suffix_positions:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  !pre bb u p suffix. es = pre ++ PhiOcc bb u p :: suffix ==>
    LAST (bb.bb_label :: le_occ_route suffix) = s.vs_current_bb /\
    (!b n fuel x y. MEM (StepOcc b n fuel x y) (PhiOcc bb u p :: suffix) ==>
      MEM b.bb_label (FRONT (bb.bb_label :: le_occ_route suffix)) \/
      (b.bb_label = s.vs_current_bb /\ SUC n <= s.vs_inst_idx)) /\
    (!b x y. MEM (PhiOcc b x y) (PhiOcc bb u p :: suffix) ==>
      MEM b.bb_label (FRONT (bb.bb_label :: le_occ_route suffix)) \/
      b.bb_label = s.vs_current_bb)
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      Cases_on `pre` >> simp[] >> strip_tac >> gvs[] >>
      drule lookup_block_label >> strip_tac >>
      drule eval_phis_preserves_current_bb >>
      simp[le_occ_route_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[APPEND_EQ_APPEND] >> strip_tac
      >- (Cases_on `l` >> gvs[] >>
          first_x_assum (qspecl_then [`pre`, `bb'`, `u'`, `p`, `t`] mp_tac) >>
          simp[] >> strip_tac >>
          `u.vs_current_bb = s.vs_current_bb` by
            metis_tac[step_preserves_control_flow] >>
          `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
          simp[le_occ_route_append, le_occ_route_def] >>
          conj_tac
          >- (rpt gen_tac >> strip_tac
              >- (first_x_assum drule >> strip_tac >> simp[]) >> gvs[]) >>
          metis_tac[]) >>
      Cases_on `l` >> gvs[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[APPEND_EQ_APPEND] >> strip_tac
  >- (Cases_on `l` >> gvs[] >>
      first_x_assum (qspecl_then [`pre`, `bb'`, `u'`, `p'`, `t`] mp_tac) >>
      simp[] >> strip_tac >>
      `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
      `next.bb_label = p.vs_current_bb` by
        metis_tac[lookup_block_label, eval_phis_preserves_current_bb] >>
      simp[le_occ_route_append, le_occ_route_def, FRONT_APPEND] >>
      pure_rewrite_tac[GSYM SNOC_APPEND, GSYM SNOC_CONS, LAST_SNOC] >>
      simp[] >>
      `MEM s.vs_current_bb (bb'.bb_label :: le_occ_route t)` by
        (qspec_then `bb'.bb_label :: le_occ_route t` mp_tac LAST_MEM >> simp[]) >>
      gvs[MEM] >> metis_tac[MEM_FRONT, MEM]) >>
  Cases_on `l` >> gvs[] >> Cases_on `t` >> gvs[] >>
  simp[le_occ_route_def] >>
  metis_tac[lookup_block_label, eval_phis_preserves_current_bb]
QED

Theorem le_pred_path_suffix:
  !pre tail. le_pred_path cfg (pre ++ tail) ==> le_pred_path cfg tail
Proof
  Induct >- simp[] >> Cases_on `pre` >> Cases_on `tail` >>
  simp[loadElimJoinPlacementTheory.le_pred_path_def] >> metis_tac[]
QED
