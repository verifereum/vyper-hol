Theory o1MakeSsaCallAssembly
Ancestors
  o1MakeSsaEventOwnership o1MakeSsaEventFrames o1ContractSueStep
  o1MakeSsaVisitTrace o1MakeSsaCallBlockBridge venomWf venomExecProps
  unitShapeDefs fmpStepList list pred_set

Theorem mssa_well_formed_phi_split:
  bb_well_formed bb ==>
  ?pre rest. bb.bb_instructions = pre ++ rest /\
    EVERY (\i. i.inst_opcode = PHI) pre /\
    EVERY (\i. i.inst_opcode <> PHI) rest
Proof
  strip_tac >>
  qspecl_then [`\i. i.inst_opcode = PHI`,`bb.bb_instructions`] mp_tac every_prefix_split >>
  fs[bb_well_formed_def] >> metis_tac[]
QED

Theorem mssa_phi_split_list_prefix[local]:
  !pre rest. EVERY P pre /\ EVERY (\i. ~P i) rest ==>
  list_prefix P (pre ++ rest)
Proof
  rpt strip_tac >> simp[list_prefix_append] >>
  conj_tac >- metis_tac[list_prefix_every] >>
  metis_tac[list_prefix_none]
QED

Theorem mssa_well_formed_phi_list_prefix:
  bb_well_formed bb ==> list_prefix (\i. i.inst_opcode = PHI) bb.bb_instructions
Proof
  strip_tac >> drule mssa_well_formed_phi_split >> strip_tac >>
  gvs[] >> irule mssa_phi_split_list_prefix >> simp[]
QED

Theorem visit_events_output_domain:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!e. MEM e events ==> IS_SOME (lookup_block e.sve_label bbs)) /\
  EVERY (\bb. EVERY (\i. set i.inst_outputs SUBSET V) bb.bb_instructions) bbs ==>
  EVERY (\e. EVERY (\i. set i.inst_outputs SUBSET V) e.sve_before) events
Proof
  strip_tac >> rewrite_tac[Once EVERY_MEM] >> qx_gen_tac `e` >> strip_tac >>
  `?bb. lookup_block e.sve_label bbs = SOME bb` by
    metis_tac[optionTheory.IS_SOME_EXISTS] >>
  BETA_TAC >> irule visit_event_output_domain >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM] >> metis_tac[lookup_block_MEM]
QED

Theorem visit_final_block_event_frame:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!q. MEM q (dom_tree_postorder tree) ==> IS_SOME (lookup_block q bbs)) /\
  set (MAP (\bb. bb.bb_label) final) SUBSET set (dom_tree_postorder tree) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) final) /\ MEM bb final ==>
  ?e. MEM e events /\ e.sve_label = bb.bb_label /\
    indexed_patch_frame (bb with bb_instructions := e.sve_after) bb
Proof
  strip_tac >>
  `MEM bb.bb_label (dom_tree_postorder tree)` by
    (fs[SUBSET_DEF, MEM_MAP] >> metis_tac[]) >>
  drule_all (cj 1 visit_tree_coverage) >> strip_tac >>
  `?e. MEM e events /\ e.sve_label = bb.bb_label` by
    (fs[MEM_MAP] >> metis_tac[]) >>
  drule_all (cj 1 visit_event_final_frame) >> strip_tac >>
  `lookup_block bb.bb_label final = SOME bb` by
    metis_tac[MEM_lookup_block] >>
  gvs[] >> qexists_tac `e` >> simp[]
QED
