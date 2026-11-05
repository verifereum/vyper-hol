Theory o1MakeSsaSnapshotWitness
Ancestors
  o1MakeSsaVisitTrace o1MakeSsaVisitPaths makeSsaCurrentInduct list pair

Theorem visit_snapshot_extension:
  (!tree path s rs bbs sm result events e.
    visit_blocks path s rs bbs sm tree = (result,events) /\ MEM e events ==>
    ?suffix. e.sve_path = path ++ suffix /\
      !pre l is js post. suffix = pre ++ [(l,is,js)] ++ post ==>
        ?a. MEM a events /\ a.sve_label = l /\ a.sve_before = is /\
          a.sve_after = js /\ a.sve_path = path ++ pre) /\
  (!trees path s ctrs stacks bbs sm result events e.
    visit_children path s ctrs stacks bbs sm trees = (result,events) /\ MEM e events ==>
    ?suffix. e.sve_path = path ++ suffix /\
      !pre l is js post. suffix = pre ++ [(l,is,js)] ++ post ==>
        ?a. MEM a events /\ a.sve_label = l /\ a.sve_before = is /\
          a.sve_after = js /\ a.sve_path = path ++ pre)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
      >> first_x_assum drule_all >> strip_tac >>
      qexists `(lbl,x.bb_instructions,insts)::suffix` >>
      simp[APPEND_ASSOC] >> rpt gen_tac >> Cases_on `pre` >> simp[]
      >- (rpt strip_tac >> gvs[] >> simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
      rpt strip_tac >> gvs[] >>
      first_x_assum (qspecl_then [`t`,`l`,`is`,`js`,`post`] mp_tac) >>
      simp[] >> metis_tac[])
  >- simp[visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  qexists `suffix` >> simp[] >> metis_tac[]
QED

Theorem root_snapshot_witness:
  MEM e (SND (visit_blocks [] s rs bbs sm tree)) /\
  e.sve_path = pre ++ [(l,is,js)] ++ post ==>
  ?a. MEM a (SND (visit_blocks [] s rs bbs sm tree)) /\
    a.sve_label = l /\ a.sve_before = is /\ a.sve_after = js /\ a.sve_path = pre
Proof
  strip_tac >> Cases_on `visit_blocks [] s rs bbs sm tree` >> gvs[] >>
  drule_all (cj 1 visit_snapshot_extension) >> simp[] >> metis_tac[]
QED

Theorem root_snapshot_member:
  MEM e (SND (visit_blocks [] s rs bbs sm tree)) /\ MEM (l,is,js) e.sve_path ==>
  ?a. MEM a (SND (visit_blocks [] s rs bbs sm tree)) /\
    a.sve_label = l /\ a.sve_before = is /\ a.sve_after = js
Proof
  strip_tac >> qpat_x_assum `MEM (l,is,js) _` mp_tac >>
  simp[MEM_SPLIT] >> strip_tac >> drule_all root_snapshot_witness >> strip_tac >> fs[MEM_SPLIT] >> metis_tac[]
QED

Theorem actual_snapshot_dominates:
  wf_function fn /\ fn_entry_label fn = SOME entry /\
  MEM e (SND (visit_blocks [] s rs bbs sm (current_dom_tree fn))) /\
  cfg_reachable_of (cfg_analyze fn) e.sve_label /\
  e.sve_path = pre ++ [(l,is,js)] ++ post ==>
  ?a. MEM a (SND (visit_blocks [] s rs bbs sm (current_dom_tree fn))) /\
    a.sve_label = l /\ a.sve_before = is /\ a.sve_after = js /\ a.sve_path = pre /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) l e.sve_label
Proof
  strip_tac >> drule_all root_snapshot_witness >> strip_tac >>
  drule_all actual_visit_path_dominators >>
  disch_then (qspec_then `l` mp_tac) >> simp[MAP_APPEND] >> metis_tac[]
QED
