Theory fmpStageCoverBackMssaLabels
Ancestors
  o1MakeSsaFormats o1MakeSsaStructuralShape makeSsaCurrentProps simplifyCfgStruct
  makeSsaCurrentCfg makeSsaCurrentInduct makeSsaDefs cfgAnalysisProps
  cfgDefs venomFnScheduleRunner unitShapeDefs venomWf list rich_list
  o1PassContract venomInst cfgCorrectnessProof dfAnalyzeProofs alist

val labels_inst = ``\ls i. !l. MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE ==> MEM l ls \/ reserved_label l``;
val labels_blocks = ``\ls bbs. EVERY (\bb. EVERY (^labels_inst ls) bb.bb_instructions) bbs``;

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
  !ops. (!l. MEM (Label l) ops ==> P l) ==>
  !l. MEM (Label l) (rename_current_operands rs ops) ==> P l
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
  Cases_on `i.inst_opcode = INVOKE` >> simp[] >>
  ho_match_mp_tac rename_operands_labels >> gvs[]
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
  !rs lbl ops. (!l. MEM (Label l) ops ==> P l) ==>
  !l. MEM (Label l) (update_current_phi_for_pred rs lbl ops) ==> P l
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
  Cases_on `inst.inst_opcode <> PHI` >> gvs[]
  >- metis_tac[] >>
  qpat_x_assum `!bb. _` (qspec_then `x` mp_tac) >> simp[] >>
  disch_then (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >>
  `!l. MEM (Label l) (update_current_phi_for_pred rs lbl inst.inst_operands) ==>
       MEM l ls \/ reserved_label l` by
    (ho_match_mp_tac update_operands_labels >> first_assum ACCEPT_TAC) >>
  metis_tac[]
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
  IF_CASES_TAC >> strip_tac >>
  `^labels_inst ls (simplify_current_phi h)` by
    (mp_tac (Q.INST [`inst` |-> `h`] (BETA_RULE simplify_phi_labels)) >> simp[]) >>
  gvs[]
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
  pure_once_rewrite_tac[EVERY_MEM] >> gen_tac >> strip_tac >>
  BETA_TAC >> irule (BETA_RULE simplify_block_labels) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem fmp_cover_back_make_ssa_label_refs:
  make_ssa_current_fn s fn = (fn',s') /\
  fn_label_refs_ok fn ==> fn_label_refs_ok fn'
Proof
  rpt strip_tac >>
  `^labels_blocks (fn_labels fn) fn.fn_blocks` by
    (gvs[fn_label_refs_ok_def, fn_insts_def, MEM_fn_insts_blocks_iff, EVERY_MEM] >>
     metis_tac[]) >>
  `fn_labels fn' = fn_labels fn` by (drule make_ssa_current_fn_labels >> simp[fn_labels_def]) >>
  qpat_x_assum `make_ssa_current_fn _ _ = _` mp_tac >>
  simp[make_ssa_current_fn_def] >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  `!l ps. ALOOKUP (current_query_map (fn_labels fn)
      (cfg_preds_of (cfg_analyze fn))) l = SOME ps ==>
      EVERY (\l. MEM l (fn_labels fn)) ps` by
    (rpt strip_tac >> drule ALOOKUP_MEM >>
     simp[current_query_map_def, MEM_MAP] >> strip_tac >> gvs[] >>
     simp[preds_subset_fn_labels]) >>
  `^labels_blocks (fn_labels fn) bbs1` by
    (qmatch_asmsub_abbrev_tac `add_phi_nodes_supply s df pm li fn.fn_blocks defs` >>
     mp_tac (Q.SPECL [`defs`, `s`, `df`, `pm`, `li`, `fn.fn_blocks`]
       (Q.INST [`ls` |-> `fn_labels fn`] (BETA_RULE add_labels))) >> simp[] >>
     gvs[Abbr `pm`] >> metis_tac[]) >>
  `^labels_blocks (fn_labels fn) bbs2` by
    (BETA_TAC >> drule (BETA_RULE (CONJUNCT1 rename_blocks_labels)) >>
     disch_then (qspec_then `fn_labels fn` mp_tac) >> gvs[]) >>
  `^labels_blocks (fn_labels fn)
    (simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) bbs2)` by
    (BETA_TAC >> irule (BETA_RULE simplify_labels) >> gvs[]) >>
  gvs[fn_label_refs_ok_def, fn_insts_def, MEM_fn_insts_blocks_iff, EVERY_MEM] >>
  metis_tac[]
QED
