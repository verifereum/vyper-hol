Theory o1LabelReadinessSsa
Ancestors
  o1PassContract o1MakeSsaFrontier o1MakeSsaFormats makeSsaCurrentCfg
  makeSsaCurrentInduct cfgTransform simplifyCfgDefs venomInst unitShapeDefs
  cfgAnalysisProps makeSsaDefs list simplifyCfgStruct cfgCorrectnessProof
  venomPassDispatcher venomWf makeSsaCurrentFrontier unitLabelMapIdentity

Theorem rename_current_operands_label_mem[local]:
  !ops. MEM (Label l) (rename_current_operands rs ops) = MEM (Label l) ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def]
QED

Theorem rename_current_inst_label_absent[local]:
  rename_current_inst s rs i = (rs',s',i') /\
  ~MEM (Label l) i.inst_operands ==> ~MEM (Label l) i'.inst_operands
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >>
  pairarg_tac >> gvs[] >> strip_tac >>
  gvs[rename_current_operands_label_mem]
QED

Theorem rename_current_block_insts_label_absent[local]:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) insts ==>
    EVERY (\i. ~MEM (Label l) i.inst_operands) insts'
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  conj_tac >- metis_tac[rename_current_inst_label_absent] >>
  first_x_assum drule_all >> simp[]
QED

Theorem update_current_phi_for_pred_label_absent[local]:
  !rs lbl ops. ~MEM (Label l) ops ==>
    ~MEM (Label l) (update_current_phi_for_pred rs lbl ops)
Proof
  recInduct update_current_phi_for_pred_ind >>
  rw[update_current_phi_for_pred_def]
QED

Theorem update_current_succ_phis_label_absent[local]:
  !succs bbs.
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
      (update_current_succ_phis rs lbl bbs succs)
Proof
  Induct >> gvs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule EVERY_replace_block >> simp[] >>
  drule lookup_block_member_label >> strip_tac >>
  gvs[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode = PHI` >>
  gvs[] >> metis_tac[update_current_phi_for_pred_label_absent]
QED

Theorem rename_current_blocks_label_absent[local]:
  (!t s rs bbs sm ctrs s' bbs'.
    rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs') /\
  (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
    rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
    EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs')
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> first_x_assum drule >> disch_then irule >>
      irule update_current_succ_phis_label_absent >>
      irule EVERY_replace_block >> simp[] >>
      drule lookup_block_member_label >> strip_tac >>
      drule rename_current_block_insts_label_absent >> disch_then irule >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_then irule >>
  first_x_assum drule_all >> simp[]
QED

Theorem simplify_current_phi_label_absent[local]:
  ~MEM (Label l) i.inst_operands ==>
  ~MEM (Label l) (simplify_current_phi i).inst_operands
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[simplify_current_phi_raw_def] >>
  Cases_on `i.inst_opcode = PHI` >> simp[] >>
  Cases_on `current_phi_output i.inst_outputs` >> simp[] >>
  Cases_on `current_phi_values (remove_current_phi_self x i.inst_operands)` >>
  simp[] >> Cases_on `x'` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem reassign_current_inst_ids_label_absent[local]:
  !ids insts. EVERY (\i. ~MEM (Label l) i.inst_operands) insts ==>
    EVERY (\i. ~MEM (Label l) i.inst_operands) (reassign_current_inst_ids ids insts)
Proof
  Induct_on `ids` >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem simplify_current_phi_prefix_parts_label_absent[local]:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) insts ==>
    EVERY (\i. ~MEM (Label l) i.inst_operands) phis /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) ordinary
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  gvs[] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> strip_tac >> gvs[] >>
  simp[simplify_current_phi_label_absent]
QED

Theorem simplify_current_phi_prefix_label_absent[local]:
  EVERY (\i. ~MEM (Label l) i.inst_operands) insts ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands) (simplify_current_phi_prefix insts)
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  irule reassign_current_inst_ids_label_absent >> simp[EVERY_APPEND] >>
  drule_all simplify_current_phi_prefix_parts_label_absent >> simp[]
QED

Theorem simplify_current_phi_block_label_absent[local]:
  EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions ==>
  EVERY (\i. ~MEM (Label l) i.inst_operands)
    (simplify_current_phi_block bb).bb_instructions
Proof
  Cases_on `bb.bb_instructions` >> simp[simplify_current_phi_block_def] >>
  IF_CASES_TAC >> simp[simplify_current_phi_prefix_label_absent]
QED

Theorem simplify_current_phis_if_label_absent[local]:
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (simplify_current_phis_if enabled bbs)
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def] >>
  Cases_on `blocks_have_leading_phi bbs` >> simp[simplify_current_phis_def] >>
  simp[EVERY_MAP] >> strip_tac >>
  simp[Once EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  BETA_TAC >> irule simplify_current_phi_block_label_absent >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem add_phi_nodes_supply_label_absent[local]:
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    li fn.fn_blocks defs = (bbs',s') /\ wf_function fn /\
  ~MEM l (fn_labels fn) /\
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) fn.fn_blocks ==>
  EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs'
Proof
  strip_tac >> drule add_phi_nodes_supply_invariant >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[insert_phi_at_block_def, build_phi_inst_supply_def] >>
  `MEM d (fn_labels fn)` by metis_tac[current_frontier_key] >>
  drule_all current_frontier_target_count >> strip_tac >>
  `MEM f (fn_labels fn)` by
    metis_tac[dfAnalyzeProofsTheory.cfg_dfs_post_subset_fn_labels] >>
  simp[ALOOKUP_current_pred_map] >>
  simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[cfgCorrectnessProofTheory.cfg_analyze_pred_labels]
QED

Theorem make_ssa_current_fn_label_absent:
  make_ssa_current_fn s fn = (fn',s') /\ wf_function fn /\
  ~MEM l (fn_labels fn) /\
  (!i. MEM i (fn_insts fn) ==> ~MEM (Label l) i.inst_operands) ==>
  !i. MEM i (fn_insts fn') ==> ~MEM (Label l) i.inst_operands
Proof
  strip_tac >>
  `EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) fn.fn_blocks` by
    (simp[EVERY_MEM] >> metis_tac[fn_insts_MEM]) >>
  `EVERY (\bb. EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) fn'.fn_blocks` suffices_by
    (simp[EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  Cases_on `fn_entry_label fn`
  >- gvs[make_ssa_current_fn_def] >>
  qpat_x_assum `make_ssa_current_fn _ _ = _` mp_tac >>
  simp[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  irule simplify_current_phis_if_label_absent >>
  drule (CONJUNCT1 rename_current_blocks_label_absent) >> disch_then irule >>
  irule add_phi_nodes_supply_label_absent >>
  fs[current_frontier_map_def, current_pred_map_def] >>
  metis_tac[]
QED

Theorem ssa_pass_no_runtime_begin:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s fn out /\
  o1_fn_shape observed.cu_context fn /\
  (!i. MEM i (fn_insts fn) ==> ~MEM (Label "runtime_begin") i.inst_operands) ==>
  !i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "runtime_begin") i.inst_operands
Proof
  strip_tac >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_def, AllCaseEqs()] >>
  `wf_function fn /\ ~MEM "runtime_begin" (fn_labels fn)` by
    (gvs[o1_fn_shape_def, fn_shape_ok_def, fn_labels_def, MEM_MAP,
         EVERY_MEM, reserved_label_def] >> metis_tac[]) >>
  drule make_ssa_current_fn_label_absent >>
  disch_then (qspec_then `"runtime_begin"` mp_tac) >> simp[]
QED
