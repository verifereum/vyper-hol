Theory o1MakeSsaEventFrames
Ancestors
  o1MakeSsaTraversalFrames o1MakeSsaVisitTrace o1MakeSsaVisitRetention
  makeSsaCurrentDefs makeSsaCurrentInduct makeSsaCurrentProps makeSsaHelper
  list pair cfgTransformProps

Theorem visit_tree_coverage:
  (!tree path s rs bbs sm ct t final events.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    (!q. MEM q (dom_tree_postorder tree) ==> IS_SOME (lookup_block q bbs)) ==>
    !q. MEM q (dom_tree_postorder tree) ==> MEM q (MAP (\e. e.sve_label) events)) /\
  (!trees path s ctrs stacks bbs sm ct t final events.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    (!q. MEM q (FLAT (MAP dom_tree_postorder trees)) ==> IS_SOME (lookup_block q bbs)) ==>
    !q. MEM q (FLAT (MAP dom_tree_postorder trees)) ==>
      MEM q (MAP (\e. e.sve_label) events))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[]
      >- (rpt strip_tac >> fs[dom_tree_postorder_def] >> qpat_x_assum `!q. _` (qspec_then `lbl` mp_tac) >> simp[]) >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      fs[dom_tree_postorder_def] >>
      `MAP (\bb. bb.bb_label)
         (update_current_succ_phis rs1 lbl (replace_block lbl
           (x with bb_instructions := insts) bbs)
           (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss)) =
       MAP (\bb. bb.bb_label) bbs` by
        (simp[update_current_succ_phis_labels] >>
         irule fn_labels_replace_block >> simp[] >> drule lookup_block_label >> simp[]) >>
      drule lookup_block_labels_agree >> strip_tac >>
      disj2_tac >> qpat_x_assum `!path s ctrs stacks bbs sm ct t final events. _` irule >>
      goal_assum (drule_at Any) >> metis_tac[])
  >- simp[visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  drule (cj 1 visit_lookup_domain) >> strip_tac
  >- (disj1_tac >> qpat_x_assum `!path s rs bbs sm ct t final events. visit_blocks _ _ _ _ _ _ = _ /\ _ ==> _` irule >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  disj2_tac >> qpat_x_assum `!path s ctrs stacks bbs sm ct t final events. _` irule >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
