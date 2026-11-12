Theory fmpStageCoverBackMssaLabels
Ancestors
  o1MakeSsaFormats o1MakeSsaStructuralShape makeSsaCurrentProps simplifyCfgStruct
  makeSsaCurrentCfg makeSsaCurrentInduct makeSsaDefs cfgAnalysisProps
  cfgDefs venomFnScheduleRunner unitShapeDefs venomWf list rich_list

val labels_inst = ``\ls i. !l. MEM (Label l) i.inst_operands ==> MEM l ls``;
val labels_blocks = ``\ls bbs. EVERY (\bb. EVERY (^labels_inst ls) bb.bb_instructions) bbs``;

Theorem phi_labels[local]:
  EVERY (\l. MEM l ls) ps ==> ^labels_inst ls (build_phi_inst_supply id v ps)
Proof
  simp[build_phi_inst_supply_def, MEM_FLAT, MEM_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem process_labels[local]:
  !fs s v pm li bbs rest hp bbs' rest' hp' s'.
  process_frontiers_supply s v pm li bbs rest hp fs = (bbs',rest',hp',s') /\
  (!l ps. ALOOKUP pm l = SOME ps ==> EVERY (\l. MEM l ls) ps) /\
  ^labels_blocks ls bbs ==> ^labels_blocks ls bbs'
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  rpt gen_tac >> simp[process_frontiers_supply_def] >>
  IF_CASES_TAC >> gvs[] >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  IF_CASES_TAC >> gvs[] >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  pairarg_tac >> gvs[] >> strip_tac >> first_x_assum drule >>
  disch_then irule >> simp[EVERY_MAP] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  simp[EVERY_MEM] >> rpt strip_tac >> Cases_on `bb.bb_label = h` >>
  gvs[insert_phi_at_block_def]
  >- (Cases_on `ALOOKUP pm bb.bb_label` >>
      gvs[build_phi_inst_supply_def, MEM_FLAT, MEM_MAP, EVERY_MEM] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem insert_labels[local]:
  !s v df pm li bbs work hp.
  (!l ps. ALOOKUP pm l = SOME ps ==> EVERY (\l. MEM l ls) ps) /\
  ^labels_blocks ls bbs ==>
  ^labels_blocks ls (FST (insert_phis_for_var_supply s v df pm li bbs work hp))
Proof
  BETA_TAC >> recInduct insert_phis_for_var_supply_ind >> rpt conj_tac >> rpt gen_tac
  >- simp[insert_phis_for_var_supply_def] >>
  strip_tac >> strip_tac >>
  simp[Once insert_phis_for_var_supply_def] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  drule (BETA_RULE process_labels) >> disch_then irule >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem add_labels[local]:
  !defs s df pm li bbs.
  (!l ps. ALOOKUP pm l = SOME ps ==> EVERY (\l. MEM l ls) ps) /\
  ^labels_blocks ls bbs ==>
  ^labels_blocks ls (FST (add_phi_nodes_supply s df pm li bbs defs))
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  simp[add_phi_nodes_supply_def] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  mp_tac (Q.SPECL [`s`, `h0`, `df`, `pm`, `li`, `bbs`, `h1`, `[]`] insert_labels) >>
  simp[] >> disch_then irule >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem rename_operands_labels[local]:
  !ops. (!l. MEM (Label l) ops ==> MEM l ls) ==>
  !l. MEM (Label l) (rename_current_operands rs ops) ==> MEM l ls
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def] >> metis_tac[]
QED

Theorem rename_inst_labels[local]:
  rename_current_inst s rs i = (rs',s',i') /\ ^labels_inst ls i ==>
  ^labels_inst ls i'
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[rename_operands_labels]
QED

Theorem rename_insts_labels[local]:
  !insts s rs rs' s' insts'.
  rename_current_block_insts s rs insts = (rs',s',insts') /\
  EVERY (^labels_inst ls) insts ==> EVERY (^labels_inst ls) insts'
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  conj_tac >- metis_tac[rename_inst_labels] >>
  first_x_assum drule_all >> simp[]
QED

Theorem update_operands_labels[local]:
  !rs lbl ops. (!l. MEM (Label l) ops ==> MEM l ls) ==>
  !l. MEM (Label l) (update_current_phi_for_pred rs lbl ops) ==> MEM l ls
Proof
  recInduct update_current_phi_for_pred_ind >>
  rw[update_current_phi_for_pred_def] >> metis_tac[]
QED

Theorem update_succ_labels[local]:
  !succs bbs. ^labels_blocks ls bbs ==>
  ^labels_blocks ls (update_current_succ_phis rs lbl bbs succs)
Proof
  Induct >> gvs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule EVERY_replace_block >> simp[] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode <> PHI` >> gvs[] >>
  metis_tac[update_operands_labels]
QED

Theorem rename_blocks_labels[local]:
  (!t s rs bbs sm ctrs s' bbs'.
    rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
    ^labels_blocks ls bbs ==> ^labels_blocks ls bbs') /\
  (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
    rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
    ^labels_blocks ls bbs ==> ^labels_blocks ls bbs')
Proof
  BETA_TAC >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> first_x_assum drule >> disch_then irule >>
      irule (BETA_RULE update_succ_labels) >>
      irule EVERY_replace_block >> simp[] >>
      drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
      drule (BETA_RULE rename_insts_labels) >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_then irule >>
  first_x_assum drule_all >> simp[]
QED

Theorem simplify_phi_labels[local]:
  ^labels_inst ls inst ==> ^labels_inst ls (simplify_current_phi inst)
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[simplify_current_phi_raw_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `current_phi_output inst.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x inst.inst_operands)` >>
  simp[] >> Cases_on `x'` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem reassign_labels[local]:
  !ids insts. EVERY (^labels_inst ls) insts ==>
  EVERY (^labels_inst ls) (reassign_current_inst_ids ids insts)
Proof
  BETA_TAC >> Induct_on `ids` >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem simplify_parts_labels[local]:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
    EVERY (^labels_inst ls) insts ==>
    EVERY (^labels_inst ls) phis /\ EVERY (^labels_inst ls) ordinary
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  gvs[] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> strip_tac >> gvs[] >>
  metis_tac[BETA_RULE simplify_phi_labels]
QED

Theorem simplify_prefix_labels[local]:
  EVERY (^labels_inst ls) insts ==>
  EVERY (^labels_inst ls) (simplify_current_phi_prefix insts)
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  irule (BETA_RULE reassign_labels) >> simp[EVERY_APPEND] >>
  drule_all (BETA_RULE simplify_parts_labels) >> simp[]
QED

Theorem simplify_block_labels[local]:
  EVERY (^labels_inst ls) bb.bb_instructions ==>
  EVERY (^labels_inst ls) (simplify_current_phi_block bb).bb_instructions
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[BETA_RULE simplify_prefix_labels] >>
  metis_tac[BETA_RULE simplify_prefix_labels, EVERY_DEF]
QED

Theorem simplify_labels[local]:
  ^labels_blocks ls bbs ==> ^labels_blocks ls (simplify_current_phis_if enabled bbs)
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def] >>
  Cases_on `blocks_have_leading_phi bbs` >> simp[simplify_current_phis_def] >>
  simp[EVERY_MAP] >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[simplify_block_labels, EVERY_MEM]
QED
