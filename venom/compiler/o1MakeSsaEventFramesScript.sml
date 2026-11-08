Theory o1MakeSsaEventFrames
Ancestors
  o1MakeSsaTraversalFrames o1MakeSsaVisitTrace o1MakeSsaVisitRetention
  o1MakeSsaPatchFrames
  makeSsaDefs makeSsaCurrentInduct makeSsaCurrentProps
  list pair cfgTransformProps
  venomExecProofs

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

Theorem visit_event_input_projection:
  (!i ops. i.inst_opcode = PHI ==> f (i with inst_operands := ops) = f i) ==>
  (!tree path s rs bbs sm ct t final events e bb.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    ALL_DISTINCT (dom_tree_postorder tree) /\ MEM e events /\
    lookup_block e.sve_label bbs = SOME bb ==>
    MAP f e.sve_before = MAP f bb.bb_instructions) /\
  (!trees path s ctrs stacks bbs sm ct t final events e bb.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_postorder trees)) /\ MEM e events /\
    lookup_block e.sve_label bbs = SOME bb ==>
    MAP f e.sve_before = MAP f bb.bb_instructions)
Proof
  strip_tac >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      fs[dom_tree_postorder_def, ALL_DISTINCT_APPEND] >>
      drule (cj 2 retention_event_labels) >> strip_tac >>
      `e.sve_label <> lbl` by metis_tac[] >>
      `x.bb_label = lbl` by metis_tac[lookup_block_label] >>
      `lookup_block e.sve_label (replace_block lbl (x with bb_instructions := insts) bbs) = SOME bb`
        by simp[retention_lookup_replace] >>
      drule_all patch_lookup_projection >>
      disch_then (qspecl_then [`case ALOOKUP sm lbl of NONE => [] | SOME ss => ss`,`rs1`,`lbl`] strip_assume_tac) >>
      first_x_assum drule_all >> metis_tac[])
  >- simp[visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  fs[ALL_DISTINCT_APPEND]
  >- (qpat_x_assum `!path s rs bbs sm ct t final events e bb. visit_blocks _ _ _ _ _ _ = _ /\ _ ==> _` drule_all >> simp[]) >>
  drule (cj 2 retention_event_labels) >> strip_tac >>
  `~MEM e.sve_label (dom_tree_postorder tree)` by metis_tac[] >>
  drule visit_excluded_projection >> disch_then (drule_all o cj 1) >> strip_tac >>
  qpat_x_assum `!path s ctrs stacks bbs sm ct t final events e bb. _` drule_all >> metis_tac[]
QED

Theorem visit_event_final_projection:
  (!i ops. i.inst_opcode = PHI ==> f (i with inst_operands := ops) = f i) ==>
  (!tree path s rs bbs sm ct t final events e.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    ALL_DISTINCT (dom_tree_postorder tree) /\ MEM e events ==>
    ?out. lookup_block e.sve_label final = SOME out /\
      MAP f out.bb_instructions = MAP f e.sve_after) /\
  (!trees path s ctrs stacks bbs sm ct t final events e.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_postorder trees)) /\ MEM e events ==>
    ?out. lookup_block e.sve_label final = SOME out /\
      MAP f out.bb_instructions = MAP f e.sve_after)
Proof
  strip_tac >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      fs[dom_tree_postorder_def, ALL_DISTINCT_APPEND]
      >- (`x.bb_label = lbl` by metis_tac[lookup_block_label] >>
          `lookup_block lbl (replace_block lbl (x with bb_instructions := insts) bbs) =
            SOME (x with bb_instructions := insts)` by simp[retention_lookup_replace] >>
          drule_all patch_lookup_projection >>
          disch_then (qspecl_then [`case ALOOKUP sm lbl of NONE => [] | SOME ss => ss`,`rs1`,`lbl`] strip_assume_tac) >>
          drule visit_excluded_projection >> disch_then (drule_all o cj 2) >>
          strip_tac >> gvs[] >> metis_tac[]) >>
      first_x_assum drule_all >> simp[])
  >- simp[visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  fs[ALL_DISTINCT_APPEND]
  >- (drule (cj 1 retention_event_labels) >> strip_tac >>
      `~MEM e.sve_label (FLAT (MAP dom_tree_postorder trees))` by metis_tac[] >>
      qpat_x_assum `!path s rs bbs sm ct t final events e. visit_blocks _ _ _ _ _ _ = _ /\ _ ==> _` drule_all >> strip_tac >>
      drule visit_excluded_projection >> disch_then (drule_all o cj 2) >>
      strip_tac >> metis_tac[]) >>
  qpat_x_assum `!path s ctrs stacks bbs sm ct t final events e. _` drule_all >> simp[]
QED

Theorem visit_event_input_frame:
  (!tree path s rs bbs sm ct t final events e bb.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    ALL_DISTINCT (dom_tree_postorder tree) /\ MEM e events /\
    lookup_block e.sve_label bbs = SOME bb ==>
    indexed_patch_frame bb (bb with bb_instructions := e.sve_before)) /\
  (!trees path s ctrs stacks bbs sm ct t final events e bb.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_postorder trees)) /\ MEM e events /\
    lookup_block e.sve_label bbs = SOME bb ==>
    indexed_patch_frame bb (bb with bb_instructions := e.sve_before))
Proof
  qspec_then `\i. (i.inst_opcode, i.inst_outputs,
    if i.inst_opcode = PHI then NONE else SOME i)` mp_tac
    (Q.GEN `f` visit_event_input_projection) >> simp[] >> strip_tac >>
  conj_tac >> rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  irule projection_indexed_frame >> simp[]
QED

Theorem visit_event_final_frame:
  (!tree path s rs bbs sm ct t final events e.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    ALL_DISTINCT (dom_tree_postorder tree) /\ MEM e events ==>
    ?out. lookup_block e.sve_label final = SOME out /\
      indexed_patch_frame (out with bb_instructions := e.sve_after) out) /\
  (!trees path s ctrs stacks bbs sm ct t final events e.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    ALL_DISTINCT (FLAT (MAP dom_tree_postorder trees)) /\ MEM e events ==>
    ?out. lookup_block e.sve_label final = SOME out /\
      indexed_patch_frame (out with bb_instructions := e.sve_after) out)
Proof
  qspec_then `\i. (i.inst_opcode, i.inst_outputs,
    if i.inst_opcode = PHI then NONE else SOME i)` mp_tac
    (Q.GEN `f` visit_event_final_projection) >> simp[] >> strip_tac >>
  conj_tac >> rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexists `out` >> simp[] >> irule projection_indexed_frame >> simp[]
QED
