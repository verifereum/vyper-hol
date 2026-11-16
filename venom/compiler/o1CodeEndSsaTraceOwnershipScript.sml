Theory o1CodeEndSsaTraceOwnership
Ancestors
  makeSsaCurrentTreeTrace
  makeSsaCurrentRenameTrace makeSsaCurrentInduct o1MakeSsaVisitTrace
  list pair pred_set

Theorem code_end_trace_visit_output_agreement[local]:
  (!tree A sm s rs bbs H E visited ct s' bbs' H' visited' events path ve R.
    current_tree_trace A sm tree s rs bbs H E visited
      ct s' bbs' H' visited' events /\
    visit_blocks path s rs bbs sm tree = ((ct,s',bbs'),ve) /\
    EVERY (\e. LIST_REL (\i j. LIST_REL (\v n. R n v)
      i.inst_outputs j.inst_outputs) e.sve_before e.sve_after) ve ==>
    EVERY (\(l,bb,s,rs,H,E,is,s1,rs1,H1,E1,bbs1,bbs2).
      LIST_REL (\i j. LIST_REL (\v n. R n v)
        i.inst_outputs j.inst_outputs) bb.bb_instructions is) events) /\
  (!trees A sm s ct stacks bbs H E visited ct' s' bbs' H' visited' events path ve R.
    current_children_trace A sm trees s ct stacks bbs H E visited
      ct' s' bbs' H' visited' events /\
    visit_children path s ct stacks bbs sm trees = ((ct',s',bbs'),ve) /\
    EVERY (\e. LIST_REL (\i j. LIST_REL (\v n. R n v)
      i.inst_outputs j.inst_outputs) e.sve_before e.sve_after) ve ==>
    EVERY (\(l,bb,s,rs,H,E,is,s1,rs1,H1,E1,bbs1,bbs2).
      LIST_REL (\i j. LIST_REL (\v n. R n v)
        i.inst_outputs j.inst_outputs) bb.bb_instructions is) events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def, Once visit_blocks_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule current_local_trace_projection >> strip_tac >> gvs[] >>
      rpt (pairarg_tac >> gvs[]) >>
      first_x_assum drule >> disch_then irule >> metis_tac[])
  >- simp[current_tree_trace_def, visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def, Once visit_blocks_def] >> strip_tac >> gvs[] >>
  drule (cj 1 current_tree_trace_projection) >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  drule (cj 2 current_tree_trace_projection) >> strip_tac >> gvs[] >>
  rename1 `visit_blocks _ _ _ _ _ _ = ((visit_ct,visit_supply,visit_bbs),_)` >>
  rename1 `rename_current_blocks _ _ _ _ _ = (trace_ct,trace_supply,trace_bbs)` >>
  `visit_ct = trace_ct /\ visit_supply = trace_supply /\ visit_bbs = trace_bbs` by
    metis_tac[cj 1 visit_erasure, FST, PAIR_EQ] >> gvs[] >>
  conj_tac >> metis_tac[]
QED

Theorem code_end_actual_trace_owner_alignment:
  current_tree_trace A sm tree s rs bbs [] E visited
    ct s' bbs' H visited' events /\
  visit_blocks path s rs bbs sm tree = ((ct,s',bbs'),ve) /\
  EVERY (\e. LIST_REL (\i j. LIST_REL (\v n. (n,v) IN R)
    i.inst_outputs j.inst_outputs) e.sve_before e.sve_after) ve ==>
  !token v n. MEM (token,v,n) H ==> (n,v) IN R
Proof
  rpt strip_tac >>
  drule (cj 1 code_end_trace_visit_output_agreement) >>
  disch_then (qspecl_then [`path`,`ve`,`\n v. (n,v) IN R`] mp_tac) >>
  simp[] >> strip_tac >>
  drule (cj 1 current_tree_trace_owner_alignment) >>
  disch_then (qspec_then `\n v. (n,v) IN R` mp_tac) >>
  simp[] >> strip_tac >>
  fs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED
