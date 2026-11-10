Theory cfgNormSupplySim
Ancestors
  cfgNormSupplyProofs cfgTransformProps cfgNormDefs cfgTransform venomExecProps venomInst venomWf
  finite_map venomFnScheduleRunner unitShapeDefs stateFrame
  analysisSimProofsBase analysisSimDefs cfgNormSim execEquivParamProps passSharedDefs
  prevBbIndep o1PassLift simplifyCfgPhiRepair simplifyCfgWfssa
  venomWfProps

Theorem find_and_split_supply_cases:
  !bbs fn s fn' changed s'.
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    (fn' = fn /\ ~changed /\ s' = s) \/
    (?pred target. MEM target bbs /\ MEM pred fn.fn_blocks /\
      MEM target.bb_label (bb_succs pred) /\
      1 < LENGTH (block_preds fn target.bb_label) /\
      1 < num_succs pred /\ changed /\
      insert_split_supply s fn pred target = (fn',s'))
Proof
  Induct_on `bbs` >- simp[find_and_split_supply_def] >>
  rpt gen_tac >> simp[Once find_and_split_supply_def] >>
  Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (simp[] >> strip_tac >> first_x_assum drule >>
      strip_tac >> simp[] >> metis_tac[]) >>
  simp[] >> Cases_on `FIND (\p. num_succs p > 1)
                           (block_preds fn h.bb_label)`
  >- (simp[] >> strip_tac >> first_x_assum drule >>
      strip_tac >> simp[] >> metis_tac[]) >>
  rename1 `FIND _ _ = SOME pred` >>
  Cases_on `insert_split_supply s fn pred h` >>
  simp[] >> rpt strip_tac >>
  drule venomExecPropsTheory.FIND_P >> simp[] >> strip_tac >>
  drule venomExecPropsTheory.FIND_MEM >> strip_tac >>
  gvs[block_preds_def, listTheory.MEM_FILTER] >>
  qexistsl [`pred`,`h`] >> simp[]
QED

Theorem cfg_norm_round_supply_cases:
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  (fn' = fn /\ ~changed /\ s' = s) \/
  (?pred target. MEM target fn.fn_blocks /\ MEM pred fn.fn_blocks /\
    MEM target.bb_label (bb_succs pred) /\
    1 < LENGTH (block_preds fn target.bb_label) /\
    1 < num_succs pred /\ changed /\
    insert_split_supply s fn pred target = (fn',s'))
Proof
  simp[cfg_norm_round_supply_def] >>
  MATCH_ACCEPT_TAC find_and_split_supply_cases
QED

Theorem lookup_block_snoc_other:
  !bbs l bb. l <> bb.bb_label ==>
    lookup_block l (bbs ++ [bb]) = lookup_block l bbs
Proof
  Induct_on `bbs` >> simp[lookup_block_def, listTheory.FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = l` >> gvs[lookup_block_def]
QED

Theorem insert_split_supply_other_lookup:
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  l <> pred.bb_label /\ l <> target.bb_label /\ l <> split.bb_label ==>
  lookup_block l fn'.fn_blocks = lookup_block l fn.fn_blocks
Proof
  rpt strip_tac >>
  gvs[insert_split_supply_def] >>
  Cases_on `pred.bb_label = target.bb_label` >>
  simp[lookup_block_snoc_other, lookup_block_replace_neq,
       update_phis_for_split_def, subst_label_terminator_def]
QED

Theorem insert_split_supply_target_lookup:
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  lookup_block target.bb_label fn.fn_blocks = SOME target /\
  split.bb_label <> target.bb_label ==>
  lookup_block target.bb_label fn'.fn_blocks =
    SOME (update_phis_for_split pred.bb_label split.bb_label repls
      (if pred.bb_label = target.bb_label then
         subst_label_terminator target.bb_label split.bb_label pred
       else target))
Proof
  rpt strip_tac >> gvs[insert_split_supply_def] >>
  simp[lookup_block_snoc_other] >>
  irule lookup_block_replace_eq >>
  simp[update_phis_for_split_def, subst_label_terminator_def] >>
  Cases_on `pred.bb_label = target.bb_label` >>
  simp[lookup_block_replace_eq, lookup_block_replace_neq,
       subst_label_terminator_def]
QED

Theorem insert_split_supply_pred_lookup:
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  lookup_block pred.bb_label fn.fn_blocks = SOME pred /\
  pred.bb_label <> target.bb_label /\ split.bb_label <> pred.bb_label ==>
  lookup_block pred.bb_label fn'.fn_blocks =
    SOME (subst_label_terminator target.bb_label split.bb_label pred)
Proof
  rpt strip_tac >> gvs[insert_split_supply_def] >>
  simp[lookup_block_snoc_other, lookup_block_replace_neq,
       lookup_block_replace_eq, update_phis_for_split_def,
       subst_label_terminator_def]
QED

Theorem lookup_block_snoc_fresh:
  !bbs bb. ~MEM bb.bb_label (MAP (\b. b.bb_label) bbs) ==>
    lookup_block bb.bb_label (bbs ++ [bb]) = SOME bb
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, listTheory.FIND_thm] >> rpt strip_tac >>
  gvs[lookup_block_def]
QED

Theorem insert_split_supply_split_lookup:
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  ~MEM split.bb_label (MAP (\b. b.bb_label) fn.fn_blocks) ==>
  lookup_block split.bb_label fn'.fn_blocks = SOME split
Proof
  rpt strip_tac >> gvs[insert_split_supply_def] >>
  irule lookup_block_snoc_fresh >>
  Cases_on `pred.bb_label = target.bb_label` >>
  simp[update_phis_for_split_def, subst_label_terminator_def]
QED

Theorem fn_entry_label_labels:
  fn_labels fn' = fn_labels fn ++ ls /\ fn.fn_blocks <> [] ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  simp[fn_labels_def, fn_entry_label_def, entry_block_def]
QED

Theorem insert_split_supply_entry:
  insert_split_supply s fn pred target = (fn',s') /\
  fn.fn_blocks <> [] ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  rpt strip_tac >> drule insert_split_supply_labels >> strip_tac >>
  irule fn_entry_label_labels >> metis_tac[]
QED

Theorem bb_succs_instructions:
  bb_succs bb =
    if bb.bb_instructions = [] then []
    else nub (REVERSE (get_successors (LAST bb.bb_instructions)))
Proof
  Cases_on `bb.bb_instructions` >> simp[bb_succs_def]
QED

Theorem bb_succs_update_phis_for_split:
  bb_succs (update_phis_for_split old new repls bb) = bb_succs bb
Proof
  Cases_on `bb.bb_instructions` using listTheory.SNOC_CASES
  >- simp[update_phis_for_split_def, bb_succs_instructions] >>
  simp[update_phis_for_split_def, bb_succs_instructions,
       listTheory.MAP_SNOC] >>
  Cases_on `x.inst_opcode = PHI` >>
  simp[get_successors_def, is_terminator_def]
QED

Theorem build_split_block_supply_succs:
  build_split_block_supply s pred target = (split,repls,s') ==>
  bb_succs split = [target.bb_label]
Proof
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lab,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  rename1 `build_forwarding_assigns_supply _ _ = (rs,rest)` >>
  PairCases_on `rest` >> Cases_on `fresh_inst_id rest1` >>
  simp[build_split_block_supply_def] >> strip_tac >>
  gvs[bb_succs_instructions, get_successors_def, is_terminator_def,
      venomStateTheory.get_label_def, listTheory.nub_def]
QED

Theorem get_labels_subst_label_ops_supply:
  !ops. MAP THE (FILTER IS_SOME
      (MAP venomState$get_label (MAP (subst_label_op old new) ops))) =
    MAP (\l. if l = old then new else l)
      (MAP THE (FILTER IS_SOME (MAP venomState$get_label ops)))
Proof
  Induct >> simp[] >> Cases_on `h` >>
  simp[subst_label_op_def, venomStateTheory.get_label_def] >>
  Cases_on `s = old` >> simp[venomStateTheory.get_label_def]
QED

Theorem get_successors_subst_label_inst_supply:
  get_successors (subst_label_inst old new inst) =
  MAP (\l. if l = old then new else l) (get_successors inst)
Proof
  simp[subst_label_inst_def, get_successors_def] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  simp[get_labels_subst_label_ops_supply]
QED

Theorem MEM_bb_succs_subst_label_terminator:
  MEM l (bb_succs (subst_label_terminator old new bb)) <=>
  ?k. MEM k (bb_succs bb) /\ l = (if k = old then new else k)
Proof
  Cases_on `bb.bb_instructions` using listTheory.SNOC_CASES
  >- simp[subst_label_terminator_def, bb_succs_instructions] >>
  simp[subst_label_terminator_def, bb_succs_instructions,
       listTheory.MAP_SNOC] >>
  Cases_on `is_terminator x.inst_opcode`
  >- (simp[get_successors_subst_label_inst_supply,
           listTheory.MEM_nub, listTheory.MEM_MAP] >> metis_tac[]) >>
  simp[get_successors_def, listTheory.MEM_nub]
QED

Theorem fn_cfg_edge_replace_block:
  bb.bb_label = lbl ==>
  (fn_cfg_edge (fn with fn_blocks := replace_block lbl bb bbs) a b <=>
   (a = lbl /\ MEM b (bb_succs bb) /\ MEM lbl (MAP (\x. x.bb_label) bbs)) \/
   (a <> lbl /\ fn_cfg_edge (fn with fn_blocks := bbs) a b))
Proof
  simp[fn_cfg_edge_def, replace_block_def, fn_labels_def,
       listTheory.MEM_MAP] >> rpt strip_tac >>
  eq_tac >> rpt strip_tac >> gvs[] >>
  Cases_on `bb'.bb_label = lbl` >> gvs[] >> metis_tac[]
QED

Theorem fn_cfg_edge_snoc:
  fn_cfg_edge (fn with fn_blocks := bbs ++ [bb]) a b <=>
  fn_cfg_edge (fn with fn_blocks := bbs) a b \/
  (a = bb.bb_label /\ MEM b (bb_succs bb))
Proof
  simp[fn_cfg_edge_def, listTheory.MEM_APPEND] >> metis_tac[]
QED

Theorem fn_cfg_edge_member_label:
  ALL_DISTINCT (fn_labels fn) /\ MEM bb fn.fn_blocks ==>
  (fn_cfg_edge fn bb.bb_label b <=> MEM b (bb_succs bb))
Proof
  simp[fn_labels_def, fn_cfg_edge_def] >> rpt strip_tac >>
  eq_tac >- (strip_tac >>
    `bb' = bb` by metis_tac[all_distinct_map_mem_inj_cfg] >> gvs[]) >>
  strip_tac >> qexists `bb` >> simp[]
QED

Theorem cfg_split_block_labels[simp]:
  (subst_label_terminator old new bb).bb_label = bb.bb_label /\
  (update_phis_for_split old new repls bb).bb_label = bb.bb_label
Proof
  simp[subst_label_terminator_def, update_phis_for_split_def]
QED

Theorem insert_split_supply_cfg_edges:
  ALL_DISTINCT (fn_labels fn) /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  (fn_cfg_edge fn' a b <=>
    (a = split.bb_label /\ b = target.bb_label) \/
    (a = pred.bb_label /\
      ?k. MEM k (bb_succs pred) /\
          b = (if k = target.bb_label then split.bb_label else k)) \/
    (a <> pred.bb_label /\ fn_cfg_edge fn a b))
Proof
  rpt strip_tac >>
  `MEM pred.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM target.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `bb_succs split = [target.bb_label]` by
    (drule_all build_split_block_supply_succs >> simp[]) >>
  gvs[insert_split_supply_def] >>
  Cases_on `pred.bb_label = target.bb_label`
  >- (simp[fn_cfg_edge_snoc, fn_cfg_edge_replace_block,
           bb_succs_update_phis_for_split, MEM_bb_succs_subst_label_terminator,
           GSYM fn_labels_def] >> metis_tac[]) >>
  simp[fn_cfg_edge_snoc, fn_cfg_edge_replace_block,
       bb_succs_update_phis_for_split, MEM_bb_succs_subst_label_terminator,
       GSYM fn_labels_def] >>
  `fn_cfg_edge fn target.bb_label b <=> MEM b (bb_succs target)` by
    (irule fn_cfg_edge_member_label >> simp[]) >>
  Cases_on `a = target.bb_label` >> gvs[] >> metis_tac[]
QED

Theorem exec_block_outputs_in_fdom_from_prefix:
  exec_block fuel ctx bb st = OK st' /\
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  (!j w. j < st.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM st.vs_vars) /\
  idx < LENGTH bb.bb_instructions /\
  ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
  MEM v (EL idx bb.bb_instructions).inst_outputs ==>
  v IN FDOM st'.vs_vars
Proof
  rpt strip_tac >> Cases_on `idx < st.vs_inst_idx`
  >- (`v IN FDOM st.vs_vars` by metis_tac[] >>
      drule exec_block_fdom_mono >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  irule exec_block_output_in_fdom_aux >>
  qexistsl [`bb`, `ctx`, `fuel`, `idx`,
            `LENGTH bb.bb_instructions - st.vs_inst_idx`, `st`] >> simp[]
QED

Theorem strict_dom_vars_defined_preserved_from_prefix:
  wf_function f /\ MEM bb f.fn_blocks /\
  bb.bb_label = st.vs_current_bb /\
  exec_block fuel ctx bb st = OK st' /\
  st.vs_inst_idx <= LENGTH bb.bb_instructions /\
  strict_dom_vars_defined f st /\ fn_reachable f st.vs_current_bb /\
  EVERY inst_wf bb.bb_instructions /\
  (!j w. j < st.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM st.vs_vars) ==>
  strict_dom_vars_defined f st'
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  simp[strict_dom_vars_defined_def] >> rpt strip_tac >>
  Cases_on `d_bb.bb_label = st.vs_current_bb`
  >- (`d_bb = bb` by
        metis_tac[venomExecProofsTheory.same_label_same_block] >> gvs[] >>
      `?idx. idx < LENGTH bb.bb_instructions /\
             EL idx bb.bb_instructions = d_inst` by
        metis_tac[listTheory.MEM_EL] >>
      `~is_terminator d_inst.inst_opcode` by
        (strip_tac >>
         `d_inst.inst_outputs = []` by
           metis_tac[venomExecProofsTheory.terminator_no_outputs,
                     listTheory.EVERY_MEM] >> gvs[]) >>
      irule exec_block_outputs_in_fdom_from_prefix >>
      qexistsl [`bb`, `ctx`, `fuel`, `idx`, `st`] >> simp[] >>
      metis_tac[]) >>
  `MEM st'.vs_current_bb (bb_succs bb)` by
    (irule exec_block_current_bb_in_succs >>
     conj_tac
     >- (gvs[bb_well_formed_def] >> rpt strip_tac >>
         `i < LENGTH bb.bb_instructions` by decide_tac >>
         `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
         decide_tac) >>
     `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
     simp[] >> qexistsl [`ctx`, `fuel`, `st`] >> simp[]) >>
  `fn_cfg_edge f st.vs_current_bb st'.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `fn_dominates f d_bb.bb_label st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.fn_dominates_predecessor] >>
  `v IN FDOM st.vs_vars` by
    (gvs[strict_dom_vars_defined_def] >> metis_tac[]) >>
  drule exec_block_fdom_mono >> simp[pred_setTheory.SUBSET_DEF]
QED

Theorem strict_dom_vars_defined_eval_phis:
  strict_dom_vars_defined f st /\ eval_phis st insts = OK st' ==>
  strict_dom_vars_defined f st'
Proof
  rpt strip_tac >>
  `st'.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  drule venomExecProofsTheory.eval_phis_vars_grow >>
  gvs[strict_dom_vars_defined_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem strict_dom_vars_defined_inst_idx[simp]:
  strict_dom_vars_defined f (st with vs_inst_idx := idx) <=>
  strict_dom_vars_defined f st
Proof
  simp[strict_dom_vars_defined_def]
QED

Theorem strict_dom_vars_defined_run_block_entry:
  wf_function f /\ MEM bb f.fn_blocks /\
  bb.bb_label = st.vs_current_bb /\
  run_block_entry fuel ctx bb st = OK st' /\
  strict_dom_vars_defined f st /\ fn_reachable f st.vs_current_bb /\
  EVERY inst_wf bb.bb_instructions ==>
  strict_dom_vars_defined f st'
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`st`, `bb.bb_instructions`]
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs) >> strip_tac >>
  gvs[venomExecSemanticsTheory.run_block_def] >>
  rename1 `eval_phis st bb.bb_instructions = OK st_phi` >>
  irule strict_dom_vars_defined_preserved_from_prefix >> simp[] >>
  qexistsl [`bb`, `ctx`, `fuel`,
            `st_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `st_phi.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_all venomExecProofsTheory.eval_phis_outputs_in_fdom_idx >> simp[]) >>
  drule_all strict_dom_vars_defined_eval_phis >> simp[]
QED

Theorem def_available_at_exec_block_endpoint:
  wf_function f /\ MEM bb f.fn_blocks /\
  bb.bb_label = st.vs_current_bb /\
  strict_dom_vars_defined f st /\
  EVERY inst_wf bb.bb_instructions /\
  exec_block fuel ctx bb st = OK st' /\
  (!j w. j < st.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM st.vs_vars) /\
  def_available_at f bb NONE v ==>
  v IN FDOM st'.vs_vars
Proof
  rpt strip_tac >>
  qpat_x_assum `def_available_at _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[def_available_at_def]) >>
  Cases_on `def_bb.bb_label = bb.bb_label`
  >- (`def_bb = bb` by
        metis_tac[venomExecProofsTheory.same_label_same_block] >> gvs[] >>
      `?idx. idx < LENGTH bb.bb_instructions /\
             EL idx bb.bb_instructions = def_inst` by
        metis_tac[listTheory.MEM_EL] >>
      `~is_terminator def_inst.inst_opcode` by
        (strip_tac >>
         `def_inst.inst_outputs = []` by
           metis_tac[venomExecProofsTheory.terminator_no_outputs,
                     listTheory.EVERY_MEM] >> gvs[]) >>
      irule exec_block_outputs_in_fdom_from_prefix >>
      qexistsl [`bb`, `ctx`, `fuel`, `idx`, `st`] >> simp[] >>
      gvs[wf_function_def] >> metis_tac[]) >>
  `v IN FDOM st.vs_vars` by
    (gvs[strict_dom_vars_defined_def] >> metis_tac[]) >>
  drule exec_block_fdom_mono >> simp[pred_setTheory.SUBSET_DEF] >>
  gvs[wf_function_def] >> metis_tac[]
QED

Theorem def_available_at_run_block_entry_endpoint:
  wf_function f /\ MEM bb f.fn_blocks /\
  bb.bb_label = st.vs_current_bb /\
  strict_dom_vars_defined f st /\
  EVERY inst_wf bb.bb_instructions /\
  run_block_entry fuel ctx bb st = OK st' /\
  def_available_at f bb NONE v ==>
  v IN FDOM st'.vs_vars
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`st`, `bb.bb_instructions`]
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs) >> strip_tac >>
  gvs[venomExecSemanticsTheory.run_block_def] >>
  rename1 `eval_phis st bb.bb_instructions = OK st_phi` >>
  irule def_available_at_exec_block_endpoint >>
  qexistsl [`bb`, `ctx`, `f`, `fuel`,
            `st_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[] >>
  `st_phi.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      drule_all venomExecProofsTheory.eval_phis_outputs_in_fdom_idx >> simp[]) >>
  drule_all strict_dom_vars_defined_eval_phis >> simp[]
QED

Theorem phi_forward_sources_available:
  !insts f pred target v.
    wf_ssa f /\ wf_function f /\
    MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
    (!inst. MEM inst insts ==> MEM inst target.bb_instructions) /\
    MEM v (phi_vars_needing_forward pred.bb_label pred insts) ==>
    def_available_at f pred NONE v
Proof
  Induct_on `insts` >- simp[phi_vars_needing_forward_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[phi_vars_needing_forward_def] >> rpt strip_tac >>
  gvs[listTheory.MEM_APPEND, listTheory.MEM_MAP, listTheory.MEM_FILTER,
      pairTheory.EXISTS_PROD]
  >- (gvs[wf_ssa_def, def_dominates_uses_def] >>
      `phi_edge_uses_wf f target h` by metis_tac[listTheory.MEM] >>
      gvs[phi_edge_uses_wf_def] >>
      `?p. MEM p f.fn_blocks /\ p.bb_label = pred.bb_label /\
           def_available_at f p NONE v` by metis_tac[] >>
      `p = pred` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
      gvs[]) >>
  first_x_assum irule >> simp[] >> qexists `target` >> simp[] >> metis_tac[]
QED

Theorem phi_forward_sources_run_block_entry_defined:
  wf_ssa f /\ wf_function f /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  pred.bb_label = st.vs_current_bb /\
  strict_dom_vars_defined f st /\
  EVERY inst_wf pred.bb_instructions /\
  run_block_entry fuel ctx pred st = OK st' /\
  MEM v (phi_vars_needing_forward pred.bb_label pred target.bb_instructions) ==>
  v IN FDOM st'.vs_vars
Proof
  rpt strip_tac >>
  `def_available_at f pred NONE v` by
    (irule phi_forward_sources_available >> simp[] >>
     qexistsl [`target.bb_instructions`, `target`] >> gvs[]) >>
  drule_all def_available_at_run_block_entry_endpoint >> simp[]
QED

Definition supply_entry_defined_def:
  supply_entry_defined f st <=>
    fn_reachable f st.vs_current_bb /\ strict_dom_vars_defined f st
End

Definition supply_prefix_defined_def:
  supply_prefix_defined f st <=>
    supply_entry_defined f st /\
    (!bb j v. MEM bb f.fn_blocks /\ bb.bb_label = st.vs_current_bb /\
      j < st.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
      MEM v (EL j bb.bb_instructions).inst_outputs ==>
      v IN FDOM st.vs_vars)
End

Theorem supply_prefix_defined_eval_phis:
  wf_function f /\ supply_entry_defined f st /\ MEM bb f.fn_blocks /\
  bb.bb_label = st.vs_current_bb /\
  eval_phis st bb.bb_instructions = OK sp ==>
  supply_prefix_defined f
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >>
  `sp.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  simp[supply_prefix_defined_def] >> conj_tac
  >- (gvs[supply_entry_defined_def] >>
      drule_all strict_dom_vars_defined_eval_phis >> simp[]) >>
  rpt strip_tac >>
  `bb' = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[] >> drule_all venomExecProofsTheory.eval_phis_outputs_in_fdom_idx >> simp[]
QED

Theorem supply_prefix_defined_step:
  wf_function f /\ fn_inst_wf f /\ supply_prefix_defined f st /\
  MEM bb f.fn_blocks /\ bb.bb_label = st.vs_current_bb /\
  st.vs_inst_idx < LENGTH bb.bb_instructions /\
  EL st.vs_inst_idx bb.bb_instructions = inst /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst st = OK sp ==>
  supply_prefix_defined f (sp with vs_inst_idx := SUC st.vs_inst_idx)
Proof
  rpt strip_tac >>
  `sp.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `inst_wf inst` by
    (gvs[fn_inst_wf_def] >> metis_tac[listTheory.MEM_EL, listTheory.EVERY_MEM]) >>
  `inst.inst_opcode <> PHI` by
    metis_tac[venomExecProofsTheory.step_inst_ok_imp_not_phi] >>
  `FDOM sp.vs_vars = FDOM st.vs_vars UNION set inst.inst_outputs` by
    metis_tac[venomExecProofsTheory.step_inst_fdom] >>
  gvs[supply_prefix_defined_def, supply_entry_defined_def] >> conj_tac
  >- (gvs[strict_dom_vars_defined_def] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `j < st.vs_inst_idx`
  >- metis_tac[] >>
  `j = st.vs_inst_idx` by decide_tac >>
  `bb' = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[]
QED

Theorem phi_forward_sources_exec_block_defined:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ supply_prefix_defined f st /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  pred.bb_label = st.vs_current_bb /\
  exec_block fuel ctx pred st = OK sp /\
  MEM v (phi_vars_needing_forward pred.bb_label pred target.bb_instructions) ==>
  v IN FDOM sp.vs_vars
Proof
  rpt strip_tac >>
  `def_available_at f pred NONE v` by
    (irule phi_forward_sources_available >> simp[] >>
     qexistsl [`target.bb_instructions`, `target`] >> gvs[]) >>
  irule def_available_at_exec_block_endpoint >>
  qexistsl [`pred`, `ctx`, `f`, `fuel`, `st`] >>
  gvs[supply_prefix_defined_def, supply_entry_defined_def, fn_inst_wf_def,
      listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem supply_entry_defined_entry:
  fn_entry_label f = SOME st.vs_current_bb ==> supply_entry_defined f st
Proof
  strip_tac >> simp[supply_entry_defined_def] >> conj_tac
  >- (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  drule strict_dom_vars_defined_entry >> simp[]
QED

Theorem supply_entry_defined_run_block_entry:
  wf_function f /\ fn_inst_wf f /\ supply_entry_defined f st /\
  MEM bb f.fn_blocks /\ bb.bb_label = st.vs_current_bb /\
  run_block_entry fuel ctx bb st = OK sp /\ ~sp.vs_halted ==>
  supply_entry_defined f sp
Proof
  rpt strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  gvs[supply_entry_defined_def] >> reverse conj_tac
  >- (drule_all strict_dom_vars_defined_run_block_entry >> simp[]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by
    (gvs[bb_well_formed_def] >> rpt strip_tac >>
     `i < LENGTH bb.bb_instructions` by decide_tac >>
     `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >> decide_tac) >>
  `bb.bb_instructions <> []` by
    (qpat_x_assum `bb_well_formed bb` mp_tac >>
     simp_tac (srw_ss()) [bb_well_formed_def]) >>
  `MEM sp.vs_current_bb (bb_succs bb)` by
    metis_tac[run_block_current_bb_in_succs] >>
  irule venomExecProofsTheory.fn_reachable_step >>
  qexists `st.vs_current_bb` >> simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem phi_forward_sources_entry_defined:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\ supply_entry_defined f st /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  pred.bb_label = st.vs_current_bb /\
  run_block_entry fuel ctx pred st = OK sp /\
  MEM v (phi_vars_needing_forward pred.bb_label pred target.bb_instructions) ==>
  v IN FDOM sp.vs_vars
Proof
  rpt strip_tac >> gvs[supply_entry_defined_def] >>
  irule phi_forward_sources_run_block_entry_defined >>
  qexistsl [`ctx`, `f`, `fuel`, `pred`, `st`, `target`] >>
  gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

(* Insert the split label between adjacent endpoints, including self-loops. *)
Definition supply_expand_path_def:
  supply_expand_path p t z [] = [] /\
  supply_expand_path p t z [a] = [a] /\
  supply_expand_path p t z (a::b::rest) =
    if a = p /\ b = t then
      a::z::supply_expand_path p t z (b::rest)
    else a::supply_expand_path p t z (b::rest)
End

Theorem supply_expand_path_endpoints:
  !q. supply_expand_path p t z q = [] <=> q = []
Proof
  Induct >> simp[supply_expand_path_def] >>
  Cases_on `q` >> simp[supply_expand_path_def] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED

Theorem supply_expand_path_hd_last:
  !q. q <> [] ==>
    HD (supply_expand_path p t z q) = HD q /\
    LAST (supply_expand_path p t z q) = LAST q
Proof
  Induct >> simp[supply_expand_path_def] >>
  Cases_on `q` >> simp[supply_expand_path_def] >>
  gen_tac >> IF_CASES_TAC >>
  gvs[listTheory.LAST_DEF, supply_expand_path_endpoints]
QED

Theorem supply_expand_path_mem:
  !q. d <> z ==> (MEM d (supply_expand_path p t z q) <=> MEM d q)
Proof
  Induct >> simp[supply_expand_path_def] >>
  Cases_on `q` >> simp[supply_expand_path_def] >>
  rpt gen_tac >> strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem supply_contract_path_mem:
  d <> z ==> (MEM d (FILTER (\l. l <> z) q) <=> MEM d q)
Proof
  simp[listTheory.MEM_FILTER]
QED

Theorem supply_expand_self_loop[simp]:
  supply_expand_path p p z [p;p] = [p;z;p]
Proof
  simp[supply_expand_path_def]
QED

Theorem supply_path_cons:
  is_fn_path f (a::q) <=>
  is_fn_path f q /\ (q = [] \/ fn_cfg_edge f a (HD q))
Proof
  Cases_on `q` >> simp[is_fn_path_def, boolTheory.CONJ_COMM]
QED

Theorem supply_expand_path_valid:
  (!a b. fn_cfg_edge f a b ==>
    if a = p /\ b = t then
      fn_cfg_edge g a z /\ fn_cfg_edge g z b
    else fn_cfg_edge g a b) ==>
  !q. is_fn_path f q ==> is_fn_path g (supply_expand_path p t z q)
Proof
  strip_tac >> Induct >> simp[supply_expand_path_def, is_fn_path_def] >>
  Cases_on `q` >> simp[supply_expand_path_def, is_fn_path_def] >>
  rpt strip_tac >> IF_CASES_TAC >>
  simp[supply_path_cons, supply_expand_path_endpoints,
       supply_expand_path_hd_last] >> metis_tac[]
QED

Theorem supply_contract_path_head:
  !q. q <> [] /\ HD q <> z ==>
    FILTER (\l. l <> z) q <> [] /\
    HD (FILTER (\l. l <> z) q) = HD q
Proof
  Cases >> simp[]
QED

Theorem supply_contract_path_valid:
  p <> z /\ t <> z /\ fn_cfg_edge f p t /\
  (!a. fn_cfg_edge g a z ==> a = p) /\
  (!b. fn_cfg_edge g z b ==> b = t) /\
  (!a b. fn_cfg_edge g a b /\ a <> z /\ b <> z ==> fn_cfg_edge f a b) ==>
  !q. is_fn_path g q ==> is_fn_path f (FILTER (\l. l <> z) q)
Proof
  strip_tac >> Induct
  >- simp[is_fn_path_def] >>
  gen_tac >> Cases_on `q`
  >- (Cases_on `h = z` >> simp[is_fn_path_def]) >>
  simp[is_fn_path_def] >> rpt strip_tac >>
  Cases_on `h = z`
  >- gvs[] >>
  Cases_on `h' = z`
  >- (Cases_on `t'` >> gvs[is_fn_path_def] >>
      `h'' = t` by metis_tac[] >>
      gvs[supply_path_cons] >> metis_tac[]) >>
  `is_fn_path f (FILTER (\l. l <> z) (h'::t'))` by metis_tac[] >>
  gvs[supply_path_cons] >> metis_tac[]
QED

Theorem supply_path_snoc:
  !q. is_fn_path f (SNOC a q) <=>
    is_fn_path f q /\ (q = [] \/ fn_cfg_edge f (LAST q) a)
Proof
  Induct >> simp[is_fn_path_def] >>
  Cases_on `q` >> gvs[is_fn_path_def] >> metis_tac[]
QED

Theorem supply_contract_path_last:
  (!a. fn_cfg_edge g a z ==> a = p) ==>
  !q. q <> [] /\ HD q <> z /\ is_fn_path g q ==>
    LAST (FILTER (\l. l <> z) q) = (if LAST q = z then p else LAST q)
Proof
  strip_tac >> ho_match_mp_tac listTheory.SNOC_INDUCT >>
  simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `q`
  >- simp[is_fn_path_def] >>
  simp[supply_path_snoc] >> rpt strip_tac >>
  Cases_on `x = z` >> Cases_on `p = z` >>
  gvs[listTheory.SNOC_APPEND, listTheory.FILTER_APPEND_DISTRIB,
      listTheory.LAST_APPEND_CONS, listTheory.LAST_DEF] >> metis_tac[]
QED

Theorem supply_split_label_not_old:
  ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') ==>
  ~MEM split.bb_label (fn_labels f)
Proof
  rpt strip_tac >>
  `~MEM split.bb_label s.irs_used_labels` by
    metis_tac[build_split_block_supply_label_fresh] >>
  `MEM split.bb_label (fn_ir_labels f)` by
    metis_tac[MEM_fn_labels_fn_ir_labels] >>
  gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM]
QED

Theorem supply_fresh_label_no_edges:
  wf_function f /\ ~MEM z (fn_labels f) ==>
  (!b. ~fn_cfg_edge f z b) /\ (!a. ~fn_cfg_edge f a z)
Proof
  simp[wf_function_def, fn_succs_closed_def, fn_cfg_edge_def,
       fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem supply_split_path_edges:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') ==>
  pred.bb_label <> split.bb_label /\ target.bb_label <> split.bb_label /\
  (!a. fn_cfg_edge g a split.bb_label ==> a = pred.bb_label) /\
  (!b. fn_cfg_edge g split.bb_label b ==> b = target.bb_label) /\
  (!a b. fn_cfg_edge g a b /\ a <> split.bb_label /\ b <> split.bb_label ==>
         fn_cfg_edge f a b) /\
  (!a b. fn_cfg_edge f a b ==>
    if a = pred.bb_label /\ b = target.bb_label then
      fn_cfg_edge g a split.bb_label /\ fn_cfg_edge g split.bb_label b
    else fn_cfg_edge g a b)
Proof
  strip_tac >>
  `~MEM split.bb_label (fn_labels f)` by
    metis_tac[supply_split_label_not_old] >>
  `pred.bb_label <> split.bb_label /\ target.bb_label <> split.bb_label` by
    (gvs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `!b. ~fn_cfg_edge f split.bb_label b` by
    metis_tac[supply_fresh_label_no_edges] >>
  `!a. ~fn_cfg_edge f a split.bb_label` by
    metis_tac[supply_fresh_label_no_edges] >>
  `ALL_DISTINCT (fn_labels f)` by gvs[wf_function_def] >>
  `!a b. fn_cfg_edge g a b <=>
    (a = split.bb_label /\ b = target.bb_label) \/
    (a = pred.bb_label /\ ?k. MEM k (bb_succs pred) /\
      b = (if k = target.bb_label then split.bb_label else k)) \/
    (a <> pred.bb_label /\ fn_cfg_edge f a b)` by
    (rpt gen_tac >> drule_all insert_split_supply_cfg_edges >>
     disch_then MATCH_ACCEPT_TAC) >>
  `!b. MEM b (bb_succs pred) <=> fn_cfg_edge f pred.bb_label b` by
    metis_tac[fn_cfg_edge_member_label] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem supply_entry_label_member:
  fn_entry_label f = SOME e ==> MEM e (fn_labels f)
Proof
  Cases_on `f.fn_blocks` >>
  simp[fn_entry_label_def, entry_block_def, fn_labels_def]
QED

Theorem insert_split_supply_contract_path:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  fn_cfg_edge f pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') /\
  q <> [] /\ fn_entry_label g = SOME (HD q) /\ is_fn_path g q ==>
  FILTER (\l. l <> split.bb_label) q <> [] /\
  HD (FILTER (\l. l <> split.bb_label) q) = HD q /\
  is_fn_path f (FILTER (\l. l <> split.bb_label) q) /\
  LAST (FILTER (\l. l <> split.bb_label) q) =
    (if LAST q = split.bb_label then pred.bb_label else LAST q)
Proof
  strip_tac >>
  `f.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label g = fn_entry_label f` by metis_tac[insert_split_supply_entry] >>
  `HD q <> split.bb_label` by
    metis_tac[supply_split_label_not_old, supply_entry_label_member] >>
  drule_all supply_split_path_edges >> strip_tac >>
  rpt conj_tac
  >- metis_tac[supply_contract_path_head]
  >- metis_tac[supply_contract_path_head]
  >- (irule supply_contract_path_valid >> metis_tac[]) >>
  irule supply_contract_path_last >> metis_tac[]
QED

Theorem insert_split_supply_expand_path:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') /\ is_fn_path f q ==>
  is_fn_path g (supply_expand_path pred.bb_label target.bb_label split.bb_label q)
Proof
  strip_tac >> drule_all supply_split_path_edges >> strip_tac >>
  irule supply_expand_path_valid >> metis_tac[]
QED

Theorem supply_reachable_transport:
  fn_entry_label g = fn_entry_label f /\
  (!a b. fn_cfg_edge f a b ==> RTC (fn_cfg_edge g) a b) ==>
  !n. fn_reachable f n ==> fn_reachable g n
Proof
  strip_tac >> simp[fn_reachable_def] >> rpt strip_tac >>
  qexists `entry` >> simp[] >>
  `RTC (RTC (fn_cfg_edge g)) entry n` suffices_by
    simp[relationTheory.RTC_RTC] >>
  irule relationTheory.RTC_MONOTONE >>
  qexists `fn_cfg_edge f` >> simp[]
QED

Theorem insert_split_supply_reachable:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') ==>
  !n. fn_reachable f n ==> fn_reachable g n
Proof
  strip_tac >>
  `f.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label g = fn_entry_label f` by metis_tac[insert_split_supply_entry] >>
  drule_all supply_split_path_edges >> strip_tac >>
  match_mp_tac supply_reachable_transport >> simp[] >>
  rpt strip_tac >> Cases_on `a = pred.bb_label /\ b = target.bb_label`
  >- (gvs[] >> metis_tac[relationTheory.RTC_SINGLE, relationTheory.RTC_TRANS]) >>
  metis_tac[relationTheory.RTC_SINGLE]
QED

Theorem insert_split_supply_reachable_split:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  fn_cfg_edge f pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') /\ fn_reachable f pred.bb_label ==>
  fn_reachable g split.bb_label
Proof
  strip_tac >>
  `fn_reachable g pred.bb_label` by metis_tac[insert_split_supply_reachable] >>
  drule_all supply_split_path_edges >> strip_tac >>
  irule venomExecProofsTheory.fn_reachable_step >>
  qexists `pred.bb_label` >> simp[] >> metis_tac[]
QED

Theorem insert_split_supply_reachable_cases:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') ==>
  !n. fn_reachable g n ==>
    (n <> split.bb_label /\ fn_reachable f n) \/
    (n = split.bb_label /\ fn_reachable f pred.bb_label /\
     fn_cfg_edge f pred.bb_label target.bb_label)
Proof
  strip_tac >>
  `f.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label g = fn_entry_label f` by metis_tac[insert_split_supply_entry] >>
  `~MEM split.bb_label (fn_labels f)` by metis_tac[supply_split_label_not_old] >>
  `ALL_DISTINCT (fn_labels f)` by gvs[wf_function_def] >>
  drule_all supply_split_path_edges >> strip_tac >>
  `!a b. fn_cfg_edge g a b <=>
    (a = split.bb_label /\ b = target.bb_label) \/
    (a = pred.bb_label /\ ?k. MEM k (bb_succs pred) /\
      b = (if k = target.bb_label then split.bb_label else k)) \/
    (a <> pred.bb_label /\ fn_cfg_edge f a b)` by
    (rpt gen_tac >> drule_all insert_split_supply_cfg_edges >>
     disch_then MATCH_ACCEPT_TAC) >>
  `!b. MEM b (bb_succs pred) <=> fn_cfg_edge f pred.bb_label b` by
    metis_tac[fn_cfg_edge_member_label] >>
  `!entry n. RTC (fn_cfg_edge g) entry n ==> fn_entry_label f = SOME entry ==>
    (n <> split.bb_label /\ fn_reachable f n) \/
    (n = split.bb_label /\ fn_reachable f pred.bb_label /\
     fn_cfg_edge f pred.bb_label target.bb_label)` suffices_by
    metis_tac[fn_reachable_def] >>
  ho_match_mp_tac relationTheory.RTC_STRONG_INDUCT_RIGHT1 >> conj_tac
  >- (rpt strip_tac >> disj1_tac >> conj_tac
      >- metis_tac[supply_entry_label_member] >>
      rewrite_tac[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  rpt strip_tac >>
  Cases_on `n' = split.bb_label`
  >- (disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      `n = pred.bb_label` by metis_tac[] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `!a b. fn_cfg_edge g a b <=> _` (qspecl_then [`n`,`n'`] mp_tac) >>
      pure_asm_rewrite_tac[] >> rpt strip_tac >>
      metis_tac[supply_fresh_label_no_edges]) >>
  disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `n = split.bb_label`
  >- (`n' = target.bb_label` by metis_tac[] >>
      metis_tac[venomExecProofsTheory.fn_reachable_step]) >>
  `fn_cfg_edge f n n'` by metis_tac[] >>
  metis_tac[venomExecProofsTheory.fn_reachable_step]
QED

Theorem insert_split_supply_reachable_old:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') /\ MEM n (fn_labels f) ==>
  (fn_reachable g n <=> fn_reachable f n)
Proof
  strip_tac >>
  `n <> split.bb_label` by metis_tac[supply_split_label_not_old] >>
  metis_tac[insert_split_supply_reachable_cases, insert_split_supply_reachable]
QED

Theorem insert_split_supply_reachable_split_iff:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') ==>
  (fn_reachable g split.bb_label <=>
   fn_reachable f pred.bb_label /\ fn_cfg_edge f pred.bb_label target.bb_label)
Proof
  strip_tac >>
  metis_tac[insert_split_supply_reachable_cases, insert_split_supply_reachable_split]
QED

Theorem insert_split_supply_dominates:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  fn_cfg_edge f pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') /\
  MEM n (fn_labels f) /\ fn_dominates f d n ==>
  fn_dominates g d n
Proof
  strip_tac >>
  `fn_reachable f n` by gvs[fn_dominates_def] >>
  `fn_reachable g n` by metis_tac[insert_split_supply_reachable] >>
  `n <> split.bb_label` by metis_tac[supply_split_label_not_old] >>
  `f.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label g = fn_entry_label f` by metis_tac[insert_split_supply_entry] >>
  simp[fn_dominates_def] >> rpt strip_tac >>
  `fn_entry_label g = SOME (HD path)` by metis_tac[] >>
  drule_all insert_split_supply_contract_path >> strip_tac >>
  `MEM d (FILTER (\l. l <> split.bb_label) path)` by
    (qpat_x_assum `fn_dominates f d n` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  gvs[listTheory.MEM_FILTER]
QED

Theorem insert_split_supply_dominates_split:
  wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
  MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
  fn_cfg_edge f pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s f pred target = (g,s') /\
  fn_dominates f d pred.bb_label ==>
  fn_dominates g d split.bb_label
Proof
  strip_tac >>
  `fn_reachable f pred.bb_label` by gvs[fn_dominates_def] >>
  `fn_reachable g split.bb_label` by
    metis_tac[insert_split_supply_reachable_split] >>
  `f.fn_blocks <> []` by gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label g = fn_entry_label f` by metis_tac[insert_split_supply_entry] >>
  simp[fn_dominates_def] >> rpt strip_tac >>
  `fn_entry_label g = SOME (HD path)` by metis_tac[] >>
  drule_all insert_split_supply_contract_path >> strip_tac >>
  `MEM d (FILTER (\l. l <> split.bb_label) path)` by
    (qpat_x_assum `fn_dominates f d pred.bb_label` mp_tac >>
     simp[fn_dominates_def] >> strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  gvs[listTheory.MEM_FILTER]
QED

Theorem supply_dominates_refl:
  fn_reachable f n ==> fn_dominates f n n
Proof
  simp[fn_dominates_def] >> rpt strip_tac >>
  Cases_on `path` >> gvs[rich_listTheory.MEM_LAST]
QED

(* Structural well-formedness depends only on the opcode sequence. *)
Theorem supply_bb_well_formed_opcodes:
  MAP (\i. i.inst_opcode) bb'.bb_instructions =
    MAP (\i. i.inst_opcode) bb.bb_instructions /\
  bb_well_formed bb ==> bb_well_formed bb'
Proof
  strip_tac >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[listTheory.LENGTH_MAP] >>
  `!n. n < LENGTH bb.bb_instructions ==>
    (EL n bb'.bb_instructions).inst_opcode =
    (EL n bb.bb_instructions).inst_opcode` by
    metis_tac[listTheory.EL_MAP] >>
  gvs[bb_well_formed_def] >>
  `bb'.bb_instructions <> []` by
    metis_tac[listTheory.LENGTH_NIL] >>
  `LAST bb'.bb_instructions =
    EL (PRE (LENGTH bb.bb_instructions)) bb'.bb_instructions` by
    metis_tac[listTheory.LAST_EL] >>
  `LAST bb.bb_instructions =
    EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions` by
    metis_tac[listTheory.LAST_EL] >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  metis_tac[]
QED

Theorem supply_subst_terminator_well_formed:
  bb_well_formed bb ==>
  bb_well_formed (subst_label_terminator old new bb)
Proof
  strip_tac >> irule supply_bb_well_formed_opcodes >>
  qexists `bb` >> simp[subst_label_terminator_def,
    listTheory.MAP_MAP_o, combinTheory.o_DEF, COND_RAND]
QED

Theorem supply_update_phis_well_formed:
  bb_well_formed bb ==>
  bb_well_formed (update_phis_for_split old new repls bb)
Proof
  strip_tac >> irule supply_bb_well_formed_opcodes >>
  qexists `bb` >> simp[update_phis_for_split_def,
    listTheory.MAP_MAP_o, combinTheory.o_DEF, COND_RAND] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  Cases_on `x.inst_opcode = PHI` >> simp[]
QED

Theorem supply_forwarding_opcodes:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    EVERY (\i. i.inst_opcode = ASSIGN) insts
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (v,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def] >> metis_tac[]
QED

Theorem supply_assigns_jmp_well_formed:
  EVERY (\i. i.inst_opcode = ASSIGN) insts /\ j.inst_opcode = JMP ==>
  bb_well_formed <| bb_label := l; bb_instructions := insts ++ [j] |>
Proof
  strip_tac >>
  `!n. n < LENGTH insts ==> (EL n insts).inst_opcode = ASSIGN` by
    (gvs[listTheory.EVERY_EL]) >>
  rewrite_tac[bb_well_formed_def] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[is_terminator_def] >>
  conj_tac
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      Cases_on `i < LENGTH insts` >>
      gvs[listTheory.EL_APPEND_EQN, is_terminator_def]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  rename1 `i < k` >>
  Cases_on `k < LENGTH insts`
  >- gvs[listTheory.EL_APPEND_EQN] >>
  `k = LENGTH insts` by decide_tac >>
  gvs[listTheory.EL_APPEND_EQN]
QED

Theorem build_split_block_supply_well_formed:
  build_split_block_supply s pred target = (split,repls,s') ==>
  bb_well_formed split
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lbl,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ = (rs,is,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  gvs[build_split_block_supply_def] >>
  irule supply_assigns_jmp_well_formed >> simp[] >>
  metis_tac[supply_forwarding_opcodes]
QED

Theorem supply_replace_block_property:
  (!bb. MEM bb bbs ==> P bb) /\ P new_bb ==>
  !bb. MEM bb (replace_block lbl new_bb bbs) ==> P bb
Proof
  simp[replace_block_def, listTheory.MEM_MAP] >> rpt strip_tac >>
  gvs[] >> IF_CASES_TAC >> gvs[]
QED

Theorem insert_split_supply_blocks_well_formed:
  (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  !bb. MEM bb fn'.fn_blocks ==> bb_well_formed bb
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `bb_well_formed split` by metis_tac[build_split_block_supply_well_formed] >>
  `bb_well_formed (subst_label_terminator target.bb_label split.bb_label pred)` by
    metis_tac[supply_subst_terminator_well_formed] >>
  gvs[insert_split_supply_def, listTheory.MEM_APPEND] >>
  qpat_x_assum `MEM bb _` mp_tac >>
  qid_spec_tac `bb` >> match_mp_tac supply_replace_block_property >>
  conj_tac
  >- (match_mp_tac supply_replace_block_property >> simp[]) >>
  irule supply_update_phis_well_formed >>
  Cases_on `pred.bb_label = target.bb_label` >> simp[]
QED

Theorem insert_split_supply_succs_closed:
  wf_function fn /\ MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  fn_succs_closed fn'
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `fn_labels fn' = fn_labels fn ++ [split.bb_label]` by
    (drule insert_split_supply_labels >> strip_tac >> gvs[]) >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  simp[fn_succs_closed_def] >> rpt strip_tac >>
  `fn_cfg_edge fn' bb.bb_label succ` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  drule_all insert_split_supply_cfg_edges >> strip_tac >>
  gvs[fn_succs_closed_def, wf_function_def, fn_cfg_edge_def,
      fn_labels_def, listTheory.MEM_MAP] >>
  metis_tac[]
QED

Theorem supply_inst_ids_distinct_iff:
  fn_inst_ids_distinct fn <=> ALL_DISTINCT (fn_ir_inst_ids fn)
Proof
  rewrite_tac[fn_inst_ids_distinct_def, irSupplyTheory.fn_ir_inst_ids_def] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  irule listTheory.MAP_CONG >> simp[irSupplyTheory.block_ir_inst_ids_def]
QED

Theorem insert_split_supply_ids_distinct:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  fn_inst_ids_distinct fn'
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all insert_split_supply_inst_ids >> strip_tac >>
  drule_all build_split_block_supply_ids_fresh >> strip_tac >>
  `ALL_DISTINCT (fn_ir_inst_ids fn)` by
    gvs[wf_function_def, supply_inst_ids_distinct_iff] >>
  gvs[supply_inst_ids_distinct_iff, listTheory.ALL_DISTINCT_APPEND] >>
  gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem insert_split_supply_wf_function:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  wf_function fn'
Proof
  rpt strip_tac >>
  `cfg_supply_covers_fn s fn` by
    gvs[cfg_supply_covers_fn_def, ir_supply_covers_fn_def,
        list_subset_def, listTheory.EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels fn')` by
    (irule insert_split_supply_labels_distinct >>
     qexistsl [`fn`,`pred`,`s`,`s'`,`target`] >> gvs[wf_function_def]) >>
  `fn_succs_closed fn'` by metis_tac[insert_split_supply_succs_closed] >>
  `fn_inst_ids_distinct fn'` by metis_tac[insert_split_supply_ids_distinct] >>
  `!bb. MEM bb fn'.fn_blocks ==> bb_well_formed bb` by
    (match_mp_tac insert_split_supply_blocks_well_formed >> gvs[wf_function_def]) >>
  simp[wf_function_def, fn_has_entry_def] >>
  drule insert_split_supply_labels >> strip_tac >>
  Cases_on `fn'.fn_blocks` >> gvs[fn_labels_def]
QED

Theorem insert_split_supply_no_incoming:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  (~?a. fn_cfg_edge fn a root) /\ MEM root (fn_labels fn) /\
  insert_split_supply s fn pred target = (fn',s') ==>
  ~?a. fn_cfg_edge fn' a root
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `~MEM split.bb_label (fn_labels fn)` by
    metis_tac[supply_split_label_not_old] >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all insert_split_supply_cfg_edges >> strip_tac >>
  gvs[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem supply_get_label_subst_is_some:
  !op. IS_SOME (venomState$get_label (subst_label_op old new op)) =
        IS_SOME (venomState$get_label op)
Proof
  Cases >> simp[subst_label_op_def, venomStateTheory.get_label_def] >>
  Cases_on `s = old` >> simp[venomStateTheory.get_label_def]
QED

Theorem supply_parse_dret_subst:
  dretShapeDefs$parse_dret_shape (subst_label_inst old new inst) =
  dretShapeDefs$parse_dret_shape inst
Proof
  simp[subst_label_inst_def, dretShapeDefsTheory.parse_dret_shape_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `h` >>
  gvs[subst_label_op_def] >> Cases_on `s = old` >> gvs[]
QED

Theorem supply_subst_label_inst_wf:
  inst_wf inst /\ is_terminator inst.inst_opcode ==>
  inst_wf (subst_label_inst old new inst)
Proof
  strip_tac >>
  `dretShapeDefs$parse_dret_shape (subst_label_inst old new inst) =
   dretShapeDefs$parse_dret_shape inst` by simp[supply_parse_dret_subst] >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  gvs[inst_wf_def, subst_label_inst_def,
      listTheory.EVERY_MAP, supply_get_label_subst_is_some] >>
  simp[subst_label_op_def] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem supply_subst_terminator_inst_wf:
  EVERY inst_wf bb.bb_instructions ==>
  EVERY inst_wf (subst_label_terminator old new bb).bb_instructions
Proof
  simp[subst_label_terminator_def, listTheory.EVERY_MAP] >>
  rewrite_tac[listTheory.EVERY_MEM] >> rpt strip_tac >>
  gvs[listTheory.MEM_MAP] >> IF_CASES_TAC >> gvs[] >>
  metis_tac[supply_subst_label_inst_wf]
QED

Theorem supply_phi_well_formed_update:
  !ops old new repls. phi_well_formed ops ==>
  phi_well_formed (update_phi_ops old new repls ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, update_phi_ops_def] >> rpt strip_tac >>
  Cases_on `lbl = old` >> gvs[phi_well_formed_def] >>
  Cases_on `ALOOKUP repls v` >> simp[phi_well_formed_def]
QED

Theorem supply_update_phis_inst_wf:
  EVERY inst_wf bb.bb_instructions ==>
  EVERY inst_wf (update_phis_for_split old new repls bb).bb_instructions
Proof
  simp[update_phis_for_split_def, listTheory.EVERY_MAP] >>
  rewrite_tac[listTheory.EVERY_MEM] >> rpt strip_tac >>
  gvs[listTheory.MEM_MAP] >> IF_CASES_TAC >> gvs[] >>
  `inst_wf e` by metis_tac[] >>
  qpat_x_assum `!e'. MEM e' _ ==> _` kall_tac >>
  gvs[inst_wf_def] >> metis_tac[supply_phi_well_formed_update]
QED

Theorem supply_forwarding_inst_wf:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    EVERY inst_wf insts
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (v,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def, inst_wf_def] >> metis_tac[]
QED

Theorem build_split_block_supply_inst_wf:
  build_split_block_supply s pred target = (split,repls,s') ==>
  EVERY inst_wf split.bb_instructions
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lbl,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ = (rs,is,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  gvs[build_split_block_supply_def, inst_wf_def] >>
  metis_tac[supply_forwarding_inst_wf]
QED

Theorem insert_split_supply_fn_inst_wf:
  fn_inst_wf fn /\ MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  fn_inst_wf fn'
Proof
  rpt strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==> EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `EVERY inst_wf split.bb_instructions` by
    metis_tac[build_split_block_supply_inst_wf] >>
  `EVERY inst_wf
    (subst_label_terminator target.bb_label split.bb_label pred).bb_instructions` by
    metis_tac[supply_subst_terminator_inst_wf] >>
  `!bb. MEM bb fn'.fn_blocks ==> EVERY inst_wf bb.bb_instructions` suffices_by
    (simp[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  gvs[insert_split_supply_def, listTheory.MEM_APPEND] >>
  rpt strip_tac >> gvs[] >> qpat_x_assum `MEM bb _` mp_tac >>
  qid_spec_tac `bb` >> ho_match_mp_tac supply_replace_block_property >>
  conj_tac
  >- (ho_match_mp_tac supply_replace_block_property >> simp[]) >>
  irule supply_update_phis_inst_wf >>
  Cases_on `pred.bb_label = target.bb_label` >> simp[]
QED

(* Pointwise image of an original block, including the composed self-edge case. *)
Definition supply_block_image_def:
  supply_block_image pred target split repls bb =
    if bb.bb_label = target.bb_label then
      update_phis_for_split pred.bb_label split.bb_label repls
        (if bb.bb_label = pred.bb_label then
           subst_label_terminator target.bb_label split.bb_label bb
         else bb)
    else if bb.bb_label = pred.bb_label then
      subst_label_terminator target.bb_label split.bb_label bb
    else bb
End

Theorem supply_block_image_label[simp]:
  (supply_block_image pred target split repls bb).bb_label = bb.bb_label
Proof
  simp[supply_block_image_def, update_phis_for_split_def,
       subst_label_terminator_def] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem supply_block_image_length[simp]:
  LENGTH (supply_block_image pred target split repls bb).bb_instructions =
  LENGTH bb.bb_instructions
Proof
  simp[supply_block_image_def, update_phis_for_split_def,
       subst_label_terminator_def] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem supply_subst_terminator_opcodes:
  MAP (\i. i.inst_opcode) (subst_label_terminator old new bb).bb_instructions =
  MAP (\i. i.inst_opcode) bb.bb_instructions
Proof
  simp[subst_label_terminator_def, listTheory.MAP_MAP_o,
       combinTheory.o_DEF, COND_RAND]
QED

Theorem supply_update_phis_opcodes:
  MAP (\i. i.inst_opcode) (update_phis_for_split old new repls bb).bb_instructions =
  MAP (\i. i.inst_opcode) bb.bb_instructions
Proof
  simp[update_phis_for_split_def, listTheory.MAP_MAP_o,
       combinTheory.o_DEF, COND_RAND] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  Cases_on `x.inst_opcode = PHI` >> simp[]
QED

Theorem supply_block_image_opcodes:
  MAP (\i. i.inst_opcode)
    (supply_block_image pred target split repls bb).bb_instructions =
  MAP (\i. i.inst_opcode) bb.bb_instructions
Proof
  simp[supply_block_image_def] >> rpt IF_CASES_TAC >>
  simp[supply_update_phis_opcodes, supply_subst_terminator_opcodes]
QED

Theorem supply_subst_terminator_outputs:
  MAP (\i. i.inst_outputs) (subst_label_terminator old new bb).bb_instructions =
  MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  simp[subst_label_terminator_def, listTheory.MAP_MAP_o,
       combinTheory.o_DEF, COND_RAND, subst_label_inst_def]
QED

Theorem supply_update_phis_outputs:
  MAP (\i. i.inst_outputs) (update_phis_for_split old new repls bb).bb_instructions =
  MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  simp[update_phis_for_split_def, listTheory.MAP_MAP_o,
       combinTheory.o_DEF, COND_RAND]
QED

Theorem supply_block_image_outputs:
  MAP (\i. i.inst_outputs)
    (supply_block_image pred target split repls bb).bb_instructions =
  MAP (\i. i.inst_outputs) bb.bb_instructions
Proof
  simp[supply_block_image_def] >> rpt IF_CASES_TAC >>
  simp[supply_update_phis_outputs, supply_subst_terminator_outputs]
QED

Theorem supply_block_image_index:
  i < LENGTH bb.bb_instructions ==>
  (EL i (supply_block_image pred target split repls bb).bb_instructions).inst_opcode =
    (EL i bb.bb_instructions).inst_opcode /\
  (EL i (supply_block_image pred target split repls bb).bb_instructions).inst_outputs =
    (EL i bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  mp_tac supply_block_image_opcodes >> mp_tac supply_block_image_outputs >>
  rpt strip_tac >> metis_tac[listTheory.EL_MAP, supply_block_image_length]
QED

Theorem insert_split_supply_image_lookup:
  wf_function fn /\ MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  MEM bb fn.fn_blocks /\ split.bb_label <> bb.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  lookup_block bb.bb_label fn'.fn_blocks =
    SOME (supply_block_image pred target split repls bb)
Proof
  rpt strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  Cases_on `bb.bb_label = target.bb_label`
  >- (`bb = target` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
      gvs[] >> drule_all insert_split_supply_target_lookup >> strip_tac >>
      Cases_on `bb.bb_label = pred.bb_label`
      >- (`bb = pred` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
          gvs[supply_block_image_def]) >>
      gvs[supply_block_image_def]) >>
  Cases_on `bb.bb_label = pred.bb_label`
  >- (`bb = pred` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
      gvs[supply_block_image_def] >>
      irule insert_split_supply_pred_lookup >> metis_tac[]) >>
  simp[supply_block_image_def] >>
  `bb.bb_label <> split.bb_label` by metis_tac[] >>
  drule_all insert_split_supply_other_lookup >> simp[]
QED

Theorem insert_split_supply_image_mem:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  MEM (supply_block_image pred target split repls bb) fn'.fn_blocks
Proof
  strip_tac >>
  `MEM bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  drule_all supply_split_label_not_old >> strip_tac >>
  `split.bb_label <> bb.bb_label` by metis_tac[] >>
  drule_all insert_split_supply_image_lookup >>
  metis_tac[venomExecProofsTheory.lookup_block_MEM]
QED

Theorem insert_split_supply_available_endpoint:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  def_available_at fn bb NONE v ==>
  def_available_at fn' (supply_block_image pred target split repls bb) NONE v
Proof
  strip_tac >>
  qpat_x_assum `def_available_at fn bb NONE v` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `?i. i < LENGTH def_bb.bb_instructions /\
       EL i def_bb.bb_instructions = def_inst` by
    metis_tac[listTheory.MEM_EL] >>
  qexistsl [`supply_block_image pred target split repls def_bb`,
    `EL i (supply_block_image pred target split repls def_bb).bb_instructions`] >>
  `MEM (supply_block_image pred target split repls def_bb) fn'.fn_blocks` by
    (irule insert_split_supply_image_mem >> metis_tac[]) >>
  `MEM bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  drule_all insert_split_supply_dominates >> strip_tac >>
  drule supply_block_image_index >> strip_tac >>
  simp[] >> metis_tac[listTheory.MEM_EL, supply_block_image_length]
QED

Theorem supply_old_inst_index_unique:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
  EL i bb.bb_instructions = EL j bb.bb_instructions ==> i = j
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    (qpat_x_assum `wf_function fn` mp_tac >>
     simp[wf_function_def, fn_inst_ids_distinct_def] >> strip_tac >>
     qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
     qpat_x_assum `MEM bb _` mp_tac >>
     qspec_tac (`fn.fn_blocks`, `bbs`) >>
     Induct >> simp[] >> rpt strip_tac >>
     gvs[listTheory.ALL_DISTINCT_APPEND]) >>
  metis_tac[listTheory.ALL_DISTINCT_EL_IMP, listTheory.EL_MAP, listTheory.LENGTH_MAP]
QED

Theorem insert_split_supply_available_inst:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  j < LENGTH bb.bb_instructions /\
  def_available_at fn bb (SOME (EL j bb.bb_instructions)) v ==>
  def_available_at fn' (supply_block_image pred target split repls bb)
    (SOME (EL j (supply_block_image pred target split repls bb).bb_instructions)) v
Proof
  strip_tac >>
  qpat_x_assum `def_available_at fn bb _ v` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `?i. i < LENGTH def_bb.bb_instructions /\
       EL i def_bb.bb_instructions = def_inst /\
       (def_bb = bb ==> i < j)` by
    (Cases_on `def_bb = bb`
     >- (gvs[] >>
         `j' = j` by (irule supply_old_inst_index_unique >> metis_tac[]) >>
         qexists `i` >> simp[]) >>
     metis_tac[listTheory.MEM_EL]) >>
  qexistsl [`supply_block_image pred target split repls def_bb`,
    `EL i (supply_block_image pred target split repls def_bb).bb_instructions`] >>
  `MEM (supply_block_image pred target split repls def_bb) fn'.fn_blocks` by
    (irule insert_split_supply_image_mem >> metis_tac[]) >>
  `MEM bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  drule_all insert_split_supply_dominates >> strip_tac >>
  drule supply_block_image_index >> strip_tac >>
  simp[] >> conj_tac
  >- metis_tac[listTheory.MEM_EL, supply_block_image_length] >>
  strip_tac >>
  `def_bb.bb_label = bb.bb_label` by metis_tac[supply_block_image_label] >>
  `def_bb = bb` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
  gvs[] >> qexistsl [`i`, `j`] >> simp[]
QED

Theorem insert_split_supply_available_split:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  def_available_at fn pred NONE v ==>
  def_available_at fn' split use_inst_opt v
Proof
  strip_tac >>
  qpat_x_assum `def_available_at fn pred NONE v` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `?i. i < LENGTH def_bb.bb_instructions /\
       EL i def_bb.bb_instructions = def_inst` by
    metis_tac[listTheory.MEM_EL] >>
  qexistsl [`supply_block_image pred target split repls def_bb`,
    `EL i (supply_block_image pred target split repls def_bb).bb_instructions`] >>
  `MEM (supply_block_image pred target split repls def_bb) fn'.fn_blocks` by
    (irule insert_split_supply_image_mem >> metis_tac[]) >>
  `MEM def_bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  drule_all supply_split_label_not_old >> strip_tac >>
  `supply_block_image pred target split repls def_bb <> split` by
    metis_tac[supply_block_image_label] >>
  drule_all insert_split_supply_dominates_split >> strip_tac >>
  drule supply_block_image_index >> strip_tac >>
  simp[] >> metis_tac[listTheory.MEM_EL, supply_block_image_length]
QED

Theorem supply_phi_pairs_update:
  !old new repls ops.
    phi_pairs (update_phi_ops old new repls ops) =
    MAP (\p. if FST p = old then
          (new, case ALOOKUP repls (SND p) of NONE => SND p | SOME v => v)
        else p) (phi_pairs ops)
Proof
  recInduct cfgNormDefsTheory.update_phi_ops_ind >>
  rw[update_phi_ops_def, phi_pairs_def]
  >- (Cases_on `val_op` >> simp[phi_pairs_def] >>
      CASE_TAC >> simp[phi_pairs_def])
  >- (Cases_on `val_op` >> simp[phi_pairs_def]) >>
  Cases_on `y` >> simp[phi_pairs_def]
QED

Theorem supply_phi_pairs_update_labels:
  MAP FST (phi_pairs (update_phi_ops old new repls ops)) =
  MAP (\l. if l = old then new else l) (MAP FST (phi_pairs ops))
Proof
  simp[supply_phi_pairs_update, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
  Cases_on `x` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem supply_phi_pairs_update_distinct:
  ALL_DISTINCT (MAP FST (phi_pairs ops)) /\
  ~MEM new (MAP FST (phi_pairs ops)) ==>
  ALL_DISTINCT (MAP FST (phi_pairs (update_phi_ops old new repls ops)))
Proof
  simp[supply_phi_pairs_update_labels] >> strip_tac >>
  irule listTheory.ALL_DISTINCT_MAP_INJ >> simp[] >>
  rpt strip_tac >> Cases_on `x = old` >> Cases_on `y = old` >> gvs[]
QED

Theorem supply_phi_pairs_update_mem:
  MEM (l,v) (phi_pairs (update_phi_ops old new repls ops)) <=>
  (?w. MEM (old,w) (phi_pairs ops) /\ l = new /\
       v = case ALOOKUP repls w of NONE => w | SOME u => u) \/
  (l <> old /\ MEM (l,v) (phi_pairs ops))
Proof
  simp[supply_phi_pairs_update, listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
  eq_tac
  >- (strip_tac >> Cases_on `p_1 = old` >> gvs[] >> metis_tac[]) >>
  strip_tac
  >- (qexistsl [`old`, `w`] >> simp[]) >>
  qexistsl [`l`, `v`] >> simp[]
QED

Theorem supply_definition_available_endpoint:
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM v inst.inst_outputs /\ fn_reachable fn bb.bb_label ==>
  def_available_at fn bb NONE v
Proof
  strip_tac >> simp[def_available_at_def] >>
  qexistsl [`bb`, `inst`] >> simp[supply_dominates_refl]
QED

Theorem supply_forward_outputs_distinct:
  !vars s repls insts s'.
    ir_supply_inst_ok s /\
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
    EVERY (\v. ~MEM v s.irs_used_vars)
      (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  Induct_on `vars` >> rpt gen_tac >> strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (nv,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s2 vars = (rs,is,s3)` >>
  `ir_supply_inst_ok s1` by
    metis_tac[fresh_ir_var_cfg_supply_extends, cfg_supply_extends_def] >>
  drule_all irSupplyTheory.fresh_inst_id_contract >> strip_tac >>
  drule irSupplyTheory.fresh_ir_var_contract >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  gvs[build_forwarding_assigns_supply_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem supply_split_outputs_distinct:
  ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') ==>
  ALL_DISTINCT (cfg_block_decl_vars split) /\
  EVERY (\v. ~MEM v s.irs_used_vars) (cfg_block_decl_vars split)
Proof
  strip_tac >>
  Cases_on `fresh_ir_label s` >> rename1 `fresh_ir_label s = (lab,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ = (rs,is,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  `ir_supply_inst_ok s1` by
    metis_tac[fresh_ir_label_cfg_supply_extends, cfg_supply_extends_def] >>
  drule_all supply_forward_outputs_distinct >> strip_tac >>
  drule irSupplyTheory.fresh_ir_label_contract >> strip_tac >>
  gvs[build_split_block_supply_def, cfg_block_decl_vars_def, listTheory.MAP_APPEND]
QED

Theorem supply_decl_vars_insts_blocks:
  !bbs. FLAT (MAP cfg_block_decl_vars bbs) =
    FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))
Proof
  Induct >> simp[cfg_block_decl_vars_def, fn_insts_blocks_def, listTheory.MAP_APPEND]
QED

Theorem supply_ssa_form_decl_vars:
  ssa_form fn <=> ALL_DISTINCT (cfg_fn_decl_vars fn)
Proof
  simp[ssa_form_def, cfg_fn_decl_vars_def, fn_insts_def, supply_decl_vars_insts_blocks]
QED

Theorem supply_decl_var_ir_var:
  MEM v (cfg_fn_decl_vars fn) ==> MEM v (irSupply$fn_ir_vars fn)
Proof
  strip_tac >>
  gvs[cfg_fn_decl_vars_def, cfg_block_decl_vars_def,
      listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  simp[irSupplyTheory.fn_ir_vars_def, irSupplyTheory.block_ir_vars_def,
       listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  qexists `FLAT (MAP inst_ir_vars y.bb_instructions)` >>
  conj_tac >- (qexists `y` >> simp[]) >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  qexists `inst_ir_vars i` >>
  conj_tac >- (qexists `i` >> simp[]) >>
  simp[irSupplyTheory.inst_ir_vars_def]
QED

Theorem insert_split_supply_ssa_form:
  wf_function fn /\ ssa_form fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  ssa_form fn'
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all insert_split_supply_decl_vars >> strip_tac >>
  `split_bb = split` by metis_tac[pairTheory.PAIR_EQ] >> gvs[] >>
  drule_all supply_split_outputs_distinct >> strip_tac >>
  gvs[supply_ssa_form_decl_vars, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  `MEM e s.irs_used_vars` by
    (gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM] >>
     metis_tac[supply_decl_var_ir_var]) >>
  metis_tac[]
QED

Theorem supply_forward_replacement_assign:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    !v w. MEM (v,w) repls ==>
      ?id. MEM <|inst_id := id; inst_opcode := ASSIGN;
                 inst_operands := [Var v]; inst_outputs := [w]|> insts
Proof
  Induct_on `vars` >> rpt gen_tac >> strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (nv,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem supply_split_replacement_definition:
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM (v,w) repls ==>
  ?inst. MEM inst split.bb_instructions /\ MEM w inst.inst_outputs
Proof
  strip_tac >>
  Cases_on `fresh_ir_label s` >> rename1 `fresh_ir_label s = (lab,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def] >>
  drule supply_forward_replacement_assign >>
  disch_then (drule_then strip_assume_tac) >>
  qexists `<|inst_id := id; inst_opcode := ASSIGN;
              inst_operands := [Var v]; inst_outputs := [w]|>` >> simp[]
QED

Theorem insert_split_supply_replacement_available:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\ fn_reachable fn pred.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\ MEM (v,w) repls ==>
  def_available_at fn' split NONE w
Proof
  strip_tac >>
  drule_all supply_split_label_not_old >> strip_tac >>
  `~MEM split.bb_label (MAP (\b. b.bb_label) fn.fn_blocks)` by gvs[fn_labels_def] >>
  drule_all insert_split_supply_split_lookup >> strip_tac >>
  `MEM split fn'.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  drule_all insert_split_supply_reachable_split >> strip_tac >>
  drule_all supply_split_replacement_definition >> strip_tac >>
  irule supply_definition_available_endpoint >> metis_tac[]
QED

Theorem supply_available_reachable:
  def_available_at fn bb use_inst_opt v ==> fn_reachable fn bb.bb_label
Proof
  simp[def_available_at_def, fn_dominates_def] >> metis_tac[]
QED

Theorem insert_split_supply_phi_pair_available:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  (!l v. MEM (l,v) (phi_pairs ops) ==>
    ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l /\
         def_available_at fn bb NONE v) /\
  MEM (l,v) (phi_pairs
    (update_phi_ops pred.bb_label split.bb_label repls ops)) ==>
  ?bb. MEM bb fn'.fn_blocks /\ bb.bb_label = l /\
       def_available_at fn' bb NONE v
Proof
  strip_tac >>
  qpat_x_assum `MEM (l,v) _` mp_tac >>
  simp[supply_phi_pairs_update_mem] >> strip_tac
  >- (gvs[] >>
      first_x_assum (drule_then strip_assume_tac) >>
      `bb = pred` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
      qpat_x_assum `bb = pred` SUBST_ALL_TAC >>
      `fn_reachable fn pred.bb_label` by
        metis_tac[supply_available_reachable] >>
      `MEM split fn'.fn_blocks` by
        (drule_all supply_split_label_not_old >> strip_tac >>
         `~MEM split.bb_label (MAP (\b. b.bb_label) fn.fn_blocks)` by
           gvs[fn_labels_def] >>
         drule_all insert_split_supply_split_lookup >> strip_tac >>
         metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
      qexists `split` >> simp[] >>
      Cases_on `ALOOKUP repls w` >> gvs[]
      >- (irule insert_split_supply_available_split >> metis_tac[]) >>
      irule insert_split_supply_replacement_available >>
      metis_tac[alistTheory.ALOOKUP_MEM]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists `supply_block_image pred target split repls bb` >>
  simp[supply_block_image_label] >> conj_tac
  >- (irule insert_split_supply_image_mem >> metis_tac[]) >>
  irule insert_split_supply_available_endpoint >> metis_tac[]
QED

Theorem insert_split_supply_incoming_edges:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  (fn_cfg_edge fn' a bb.bb_label <=>
    if bb.bb_label = target.bb_label then
      a = split.bb_label \/ (a <> pred.bb_label /\ fn_cfg_edge fn a bb.bb_label)
    else fn_cfg_edge fn a bb.bb_label)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  `MEM bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  drule_all supply_split_label_not_old >> strip_tac >>
  `bb.bb_label <> split.bb_label` by metis_tac[] >>
  `fn_cfg_edge fn pred.bb_label bb.bb_label <=> MEM bb.bb_label (bb_succs pred)` by
    (irule fn_cfg_edge_member_label >> simp[]) >>
  drule_all insert_split_supply_cfg_edges >>
  disch_then (qspecl_then [`bb.bb_label`, `a`] mp_tac) >>
  Cases_on `bb.bb_label = target.bb_label` >>
  Cases_on `a = pred.bb_label` >> simp[] >> metis_tac[]
QED

Theorem insert_split_supply_phi_edge_target:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  phi_edge_uses_wf fn target inst ==>
  phi_edge_uses_wf fn'
    (supply_block_image pred target split repls target)
    (inst with inst_operands :=
      update_phi_ops pred.bb_label split.bb_label repls inst.inst_operands)
Proof
  strip_tac >>
  `~MEM split.bb_label (fn_labels fn)` by
    (irule supply_split_label_not_old >> metis_tac[]) >>
  `!l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
    ?bb. MEM bb fn.fn_blocks /\ bb.bb_label = l /\
         def_available_at fn bb NONE v` by
    metis_tac[phi_edge_uses_wf_def] >>
  `~MEM split.bb_label (MAP FST (phi_pairs inst.inst_operands))` by
    (simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >>
     metis_tac[fn_labels_def, listTheory.MEM_MAP]) >>
  simp[phi_edge_uses_wf_def] >> conj_tac
  >- (irule supply_phi_well_formed_update >>
      gvs[phi_edge_uses_wf_def]) >>
  conj_tac
  >- (irule supply_phi_pairs_update_distinct >>
      gvs[phi_edge_uses_wf_def]) >>
  conj_tac
  >- (gen_tac >>
      drule_all insert_split_supply_incoming_edges >>
      disch_then (qspec_then `pred'` mp_tac) >>
      simp[supply_phi_pairs_update_mem, pairTheory.EXISTS_PROD] >>
      gvs[phi_edge_uses_wf_def, pairTheory.EXISTS_PROD] >>
      disch_tac >> Cases_on `pred' = split.bb_label` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  drule_all insert_split_supply_phi_pair_available >> strip_tac >>
  qexists `bb` >> simp[] >>
  drule_all insert_split_supply_incoming_edges >>
  disch_then (qspec_then `pred'` mp_tac) >> simp[] >>
  qpat_x_assum `MEM (pred',v) _` mp_tac >>
  simp[supply_phi_pairs_update_mem] >>
  gvs[phi_edge_uses_wf_def] >> metis_tac[]
QED

Theorem insert_split_supply_phi_edge_other:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  bb.bb_label <> target.bb_label /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  phi_edge_uses_wf fn bb inst ==>
  phi_edge_uses_wf fn' (supply_block_image pred target split repls bb) inst
Proof
  strip_tac >>
  `!a. fn_cfg_edge fn' a bb.bb_label <=> fn_cfg_edge fn a bb.bb_label` by
    (drule_all insert_split_supply_incoming_edges >> simp[]) >>
  qpat_x_assum `phi_edge_uses_wf fn bb inst` mp_tac >>
  simp[phi_edge_uses_wf_def] >> strip_tac >>
  rpt conj_tac >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexists `supply_block_image pred target split repls pred_bb` >>
  simp[] >> conj_tac
  >- (irule insert_split_supply_image_mem >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  irule insert_split_supply_available_endpoint >> metis_tac[]
QED

Theorem supply_subst_terminator_index:
  i < LENGTH bb.bb_instructions ==>
  EL i (subst_label_terminator old new bb).bb_instructions =
    if is_terminator (EL i bb.bb_instructions).inst_opcode then
      subst_label_inst old new (EL i bb.bb_instructions)
    else EL i bb.bb_instructions
Proof
  simp[subst_label_terminator_def, listTheory.EL_MAP]
QED

Theorem supply_update_phis_index:
  i < LENGTH bb.bb_instructions ==>
  EL i (update_phis_for_split old new repls bb).bb_instructions =
    if (EL i bb.bb_instructions).inst_opcode = PHI then
      (EL i bb.bb_instructions) with inst_operands :=
        update_phi_ops old new repls (EL i bb.bb_instructions).inst_operands
    else EL i bb.bb_instructions
Proof
  simp[update_phis_for_split_def, listTheory.EL_MAP] >>
  strip_tac >> Cases_on `(EL i bb.bb_instructions).inst_opcode = PHI` >> simp[]
QED

Theorem supply_subst_label_ops_vars:
  MEM (Var v) (MAP (subst_label_op old new) ops) <=>
  MEM (Var v) ops
Proof
  simp[listTheory.MEM_MAP] >>
  eq_tac >- (strip_tac >> Cases_on `y` >> gvs[subst_label_op_def] >>
    Cases_on `s = old` >> gvs[]) >>
  strip_tac >> qexists `Var v` >> simp[subst_label_op_def]
QED

Theorem supply_subst_terminator_index_vars:
  i < LENGTH bb.bb_instructions ==>
  (MEM (Var v) (EL i (subst_label_terminator old new bb).bb_instructions).inst_operands <=>
   MEM (Var v) (EL i bb.bb_instructions).inst_operands)
Proof
  strip_tac >> simp[supply_subst_terminator_index] >>
  IF_CASES_TAC >> simp[subst_label_inst_def, supply_subst_label_ops_vars]
QED

Theorem supply_block_image_index_vars:
  i < LENGTH bb.bb_instructions /\ (EL i bb.bb_instructions).inst_opcode <> PHI ==>
  (MEM (Var v) (EL i (supply_block_image pred target split repls bb).bb_instructions).inst_operands <=>
   MEM (Var v) (EL i bb.bb_instructions).inst_operands)
Proof
  strip_tac >>
  Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >>
  simp[supply_block_image_def] >> rpt IF_CASES_TAC >>
  simp[supply_update_phis_index, subst_label_terminator_def,
       listTheory.EL_MAP, subst_label_inst_def] >>
  simp[supply_subst_label_ops_vars]
QED

Theorem supply_block_image_index_phi:
  i < LENGTH bb.bb_instructions /\ (EL i bb.bb_instructions).inst_opcode = PHI ==>
  EL i (supply_block_image pred target split repls bb).bb_instructions =
    if bb.bb_label = target.bb_label then
      (EL i bb.bb_instructions) with inst_operands :=
        update_phi_ops pred.bb_label split.bb_label repls
          (EL i bb.bb_instructions).inst_operands
    else EL i bb.bb_instructions
Proof
  strip_tac >> simp[supply_block_image_def] >> rpt IF_CASES_TAC >>
  simp[supply_update_phis_index, subst_label_terminator_def,
       listTheory.EL_MAP, is_terminator_def]
QED

Theorem insert_split_supply_old_block_uses:
  wf_function fn /\ def_dominates_uses fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  i < LENGTH bb.bb_instructions ==>
  if (EL i (supply_block_image pred target split repls bb).bb_instructions).inst_opcode = PHI then
    phi_edge_uses_wf fn' (supply_block_image pred target split repls bb)
      (EL i (supply_block_image pred target split repls bb).bb_instructions)
  else
    !v. MEM (Var v)
      (EL i (supply_block_image pred target split repls bb).bb_instructions).inst_operands ==>
      def_available_at fn' (supply_block_image pred target split repls bb)
        (SOME (EL i (supply_block_image pred target split repls bb).bb_instructions)) v
Proof
  strip_tac >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by
    metis_tac[listTheory.MEM_EL] >>
  qpat_x_assum `def_dominates_uses fn` mp_tac >>
  simp[def_dominates_uses_def] >>
  disch_then (drule_then (drule_then assume_tac)) >>
  drule supply_block_image_index >> strip_tac >> simp[] >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = PHI`
  >- (gvs[] >> simp[supply_block_image_index_phi] >>
      Cases_on `bb.bb_label = target.bb_label`
      >- (`bb = target` by metis_tac[venomExecProofsTheory.same_label_same_block] >>
          qpat_x_assum `bb = target` SUBST_ALL_TAC >> simp[] >>
          irule insert_split_supply_phi_edge_target >> metis_tac[]) >>
      simp[] >> irule insert_split_supply_phi_edge_other >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >>
  `MEM (Var v) (EL i bb.bb_instructions).inst_operands` by
    metis_tac[supply_block_image_index_vars] >>
  irule insert_split_supply_available_inst >> metis_tac[]
QED

Theorem supply_forward_inst_source:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    !inst. MEM inst insts ==>
      inst.inst_opcode = ASSIGN /\
      ?v. MEM v vars /\ inst.inst_operands = [Var v]
Proof
  Induct_on `vars` >> rpt gen_tac >> strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (nv,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem supply_split_inst_source:
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM inst split.bb_instructions ==>
  (inst.inst_opcode = JMP /\ inst.inst_operands = [Label target.bb_label]) \/
  (inst.inst_opcode = ASSIGN /\
   ?v. MEM v (phi_vars_needing_forward pred.bb_label pred target.bb_instructions) /\
       inst.inst_operands = [Var v])
Proof
  strip_tac >>
  Cases_on `fresh_ir_label s` >> rename1 `fresh_ir_label s = (lab,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def, listTheory.MEM_APPEND] >>
  drule supply_forward_inst_source >>
  disch_then (drule_then strip_assume_tac) >>
  simp[] >> metis_tac[listTheory.MEM_nub]
QED

Theorem insert_split_supply_split_uses:
  wf_function fn /\ wf_ssa fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst split.bb_instructions ==>
  inst.inst_opcode <> PHI /\
  !v. MEM (Var v) inst.inst_operands ==>
    def_available_at fn' split (SOME inst) v
Proof
  strip_tac >> drule_all supply_split_inst_source >> strip_tac >>
  simp[] >> rpt strip_tac >> gvs[] >>
  `def_available_at fn pred NONE v` by
    (irule phi_forward_sources_available >> metis_tac[]) >>
  irule insert_split_supply_available_split >> metis_tac[]
QED

Theorem insert_split_supply_block_cases:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\ MEM bb' fn'.fn_blocks ==>
  bb' = split \/
  ?bb. MEM bb fn.fn_blocks /\ bb' = supply_block_image pred target split repls bb
Proof
  strip_tac >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  drule_all supply_split_label_not_old >> strip_tac >>
  `fn_labels fn' = fn_labels fn ++ [split.bb_label]` by
    (drule insert_split_supply_labels >> strip_tac >>
     metis_tac[pairTheory.PAIR_EQ]) >>
  Cases_on `bb'.bb_label = split.bb_label`
  >- (disj1_tac >>
      `~MEM split.bb_label (MAP (\b. b.bb_label) fn.fn_blocks)` by
        gvs[fn_labels_def] >>
      drule_all insert_split_supply_split_lookup >> strip_tac >>
      `MEM split fn'.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
      metis_tac[venomExecProofsTheory.same_label_same_block]) >>
  disj2_tac >>
  `MEM bb'.bb_label (fn_labels fn)` by
    (`MEM bb'.bb_label (fn_labels fn')` by
       (pure_rewrite_tac[fn_labels_def, listTheory.MEM_MAP] >>
        qexists `bb'` >> simp[]) >>
     gvs[listTheory.MEM_APPEND]) >>
  `?bb. MEM bb fn.fn_blocks /\ bb.bb_label = bb'.bb_label` by
    (qpat_x_assum `MEM bb'.bb_label (fn_labels fn)` mp_tac >>
     pure_rewrite_tac[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  qexists `bb` >> simp[] >>
  `MEM (supply_block_image pred target split repls bb) fn'.fn_blocks` by
    (irule insert_split_supply_image_mem >> metis_tac[]) >>
  metis_tac[venomExecProofsTheory.same_label_same_block, supply_block_image_label]
QED

Theorem insert_split_supply_reachable_block_cases:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM bb' fn'.fn_blocks /\ fn_reachable fn' bb'.bb_label ==>
  (bb' = split /\ fn_reachable fn pred.bb_label /\
   fn_cfg_edge fn pred.bb_label target.bb_label) \/
  ?bb. MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
       bb' = supply_block_image pred target split repls bb
Proof
  strip_tac >> drule_all insert_split_supply_block_cases >> strip_tac
  >- metis_tac[insert_split_supply_reachable_split_iff] >>
  disj2_tac >> qexists `bb` >> simp[] >>
  `MEM bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  metis_tac[insert_split_supply_reachable_old, supply_block_image_label]
QED

Theorem insert_split_supply_reachable_image_mem:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM inst (supply_block_image pred target split repls bb).bb_instructions /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  MEM (reachable_inst fn' bb.bb_label inst) (fn_insts (reachable_fn fn'))
Proof
  strip_tac >> rewrite_tac[MEM_reachable_fn_insts] >>
  qexistsl [`supply_block_image pred target split repls bb`, `inst`] >>
  simp[] >> conj_tac
  >- metis_tac[insert_split_supply_image_mem] >>
  metis_tac[insert_split_supply_reachable]
QED

Theorem insert_split_supply_reachable_inst_cases:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts (reachable_fn fn')) ==>
  (MEM inst split.bb_instructions /\ fn_reachable fn pred.bb_label /\
   fn_cfg_edge fn pred.bb_label target.bb_label) \/
  ?bb n. MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    n < LENGTH bb.bb_instructions /\
    inst = reachable_inst fn' bb.bb_label
      (EL n (supply_block_image pred target split repls bb).bb_instructions)
Proof
  strip_tac >>
  qpat_x_assum `MEM inst (fn_insts (reachable_fn fn'))` mp_tac >>
  rewrite_tac[MEM_reachable_fn_insts] >> strip_tac >>
  drule_all insert_split_supply_reachable_block_cases >> strip_tac
  >- (disj1_tac >> gvs[] >>
      `i.inst_opcode <> PHI` by
        (drule_all supply_split_inst_source >> strip_tac >> simp[]) >>
      gvs[reachable_inst_fields]) >>
  disj2_tac >> qexists `bb'` >>
  `?n. n < LENGTH bb'.bb_instructions /\
    i = EL n (supply_block_image pred target split repls bb').bb_instructions` by
    metis_tac[listTheory.MEM_EL, supply_block_image_length] >>
  qexists `n` >> gvs[]
QED

Theorem insert_split_supply_reachable_preds:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\ MEM m (fn_labels fn) ==>
  (MEM l (reachable_preds fn' m) <=>
   (l = split.bb_label /\ m = target.bb_label /\
    fn_reachable fn pred.bb_label /\ fn_cfg_edge fn pred.bb_label target.bb_label) \/
   (l <> split.bb_label /\ (l <> pred.bb_label \/ m <> target.bb_label) /\
    MEM l (reachable_preds fn m)))
Proof
  strip_tac >>
  `~MEM split.bb_label (fn_labels fn)` by metis_tac[supply_split_label_not_old] >>
  `m <> split.bb_label` by metis_tac[] >>
  `pred.bb_label <> split.bb_label` by
    (gvs[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `!b. ~fn_cfg_edge fn split.bb_label b` by
    metis_tac[supply_fresh_label_no_edges] >>
  `fn_reachable fn' split.bb_label <=>
   fn_reachable fn pred.bb_label /\ fn_cfg_edge fn pred.bb_label target.bb_label` by
    metis_tac[insert_split_supply_reachable_split_iff] >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  `fn_labels fn' = fn_labels fn ++ [split.bb_label]` by
    (drule insert_split_supply_labels >> strip_tac >> metis_tac[pairTheory.PAIR_EQ]) >>
  `!a b. fn_cfg_edge fn' a b <=>
    (a = split.bb_label /\ b = target.bb_label) \/
    (a = pred.bb_label /\ ?k. MEM k (bb_succs pred) /\
      b = (if k = target.bb_label then split.bb_label else k)) \/
    (a <> pred.bb_label /\ fn_cfg_edge fn a b)` by
    (rpt gen_tac >> drule_all insert_split_supply_cfg_edges >>
     disch_then MATCH_ACCEPT_TAC) >>
  `!b. MEM b (bb_succs pred) <=> fn_cfg_edge fn pred.bb_label b` by
    metis_tac[fn_cfg_edge_member_label] >>
  Cases_on `l = split.bb_label`
  >- (gvs[reachable_preds_def, GSYM fn_labels_def, listTheory.MEM_FILTER,
          listTheory.MEM_APPEND] >>
      metis_tac[insert_split_supply_reachable_split_iff]) >>
  Cases_on `MEM l (fn_labels fn)`
  >- (`fn_reachable fn' l <=> fn_reachable fn l` by
        metis_tac[insert_split_supply_reachable_old] >>
      simp[reachable_preds_def, GSYM fn_labels_def, listTheory.MEM_FILTER,
           listTheory.MEM_APPEND] >>
      Cases_on `l = pred.bb_label` >> simp[] >>
      eq_tac
      >- (strip_tac >> Cases_on `k = target.bb_label` >> gvs[]) >>
      strip_tac >> simp[] >> qexists `m` >> simp[] ) >>
  simp[reachable_preds_def, GSYM fn_labels_def, listTheory.MEM_FILTER,
       listTheory.MEM_APPEND]
QED

Theorem supply_split_phi_label_fresh:
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  phi_well_formed i.inst_operands ==>
  !v. ~MEM (split.bb_label,v) (phi_pairs i.inst_operands)
Proof
  rpt strip_tac >>
  `~MEM split.bb_label s.irs_used_labels` by
    metis_tac[build_split_block_supply_label_fresh] >>
  `MEM split.bb_label (MAP FST (phi_pairs i.inst_operands))` by
    (simp[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  `MEM (Label split.bb_label) i.inst_operands` by
    metis_tac[phi_pair_label_mem] >>
  `MEM split.bb_label (irSupply$fn_ir_labels fn)` by
    (simp[irSupplyTheory.fn_ir_labels_def, irSupplyTheory.block_ir_labels_def,
          irSupplyTheory.inst_ir_labels_def, irSupplyTheory.MEM_operand_ir_labels,
          listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM]
QED

Theorem insert_split_supply_reachable_phi_pair:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  i = EL n bb.bb_instructions /\
  j = EL n (supply_block_image pred target split repls bb).bb_instructions /\
  i.inst_opcode = PHI /\ phi_well_formed i.inst_operands ==>
  (MEM (l,v) (phi_pairs (reachable_inst fn' bb.bb_label j).inst_operands) <=>
   ?k w. MEM (k,w) (phi_pairs (reachable_inst fn bb.bb_label i).inst_operands) /\
     l = (if bb.bb_label = target.bb_label /\ k = pred.bb_label then split.bb_label else k) /\
     v = (if bb.bb_label = target.bb_label /\ k = pred.bb_label then
            (case ALOOKUP repls w of NONE => w | SOME u => u) else w))
Proof
  strip_tac >>
  `j = if bb.bb_label = target.bb_label then
         i with inst_operands := update_phi_ops pred.bb_label split.bb_label repls i.inst_operands
       else i` by metis_tac[supply_block_image_index_phi] >>
  `MEM bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `!a. MEM a (reachable_preds fn' bb.bb_label) <=>
   (a = split.bb_label /\ bb.bb_label = target.bb_label /\
    fn_reachable fn pred.bb_label /\ fn_cfg_edge fn pred.bb_label target.bb_label) \/
   (a <> split.bb_label /\ (a <> pred.bb_label \/ bb.bb_label <> target.bb_label) /\
    MEM a (reachable_preds fn bb.bb_label))` by
    (gen_tac >> drule_all insert_split_supply_reachable_preds >>
     disch_then MATCH_ACCEPT_TAC) >>
  `MEM i bb.bb_instructions` by metis_tac[listTheory.MEM_EL] >>
  `!v. ~MEM (split.bb_label,v) (phi_pairs i.inst_operands)` by
    (drule_all supply_split_phi_label_fresh >> disch_then MATCH_ACCEPT_TAC) >>
  `pred.bb_label <> split.bb_label` by
    metis_tac[supply_split_path_edges] >>
  `MEM pred.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM pred.bb_label (reachable_preds fn bb.bb_label) <=>
       fn_reachable fn pred.bb_label /\ fn_cfg_edge fn pred.bb_label bb.bb_label` by
    simp[reachable_preds_def, GSYM fn_labels_def, listTheory.MEM_FILTER] >>
  qpat_x_assum `i = EL n bb.bb_instructions` kall_tac >>
  qpat_x_assum `j = EL n _` kall_tac >>
  Cases_on `bb.bb_label = target.bb_label` >>
  gvs[reachable_inst_def, filter_phi_ops_pairs, supply_phi_well_formed_update,
      listTheory.MEM_FILTER, supply_phi_pairs_update_mem]
  >- (Cases_on `l = split.bb_label`
      >- (simp[] >> eq_tac
          >- (strip_tac >> qexistsl [`pred.bb_label`, `w`] >> simp[] >> metis_tac[]) >>
          strip_tac >> Cases_on `k = pred.bb_label` >> gvs[] >> metis_tac[]) >>
      simp[] >> eq_tac
      >- (strip_tac >> qexistsl [`l`, `v`] >> simp[]) >>
      strip_tac >> Cases_on `k = pred.bb_label` >> gvs[]) >>
  metis_tac[]
QED

Theorem supply_split_opcodes:
  build_split_block_supply s pred target = (split,repls,s') ==>
  EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = JMP)
    split.bb_instructions
Proof
  strip_tac >> Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lbl,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ = (rs,is,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  gvs[build_split_block_supply_def] >>
  drule supply_forwarding_opcodes >>
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem insert_split_supply_opcode_property:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  P ASSIGN /\ P JMP /\ EVERY (\i. P i.inst_opcode) (fn_insts fn) /\
  insert_split_supply s fn pred target = (fn',s') ==>
  EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = JMP)
     split.bb_instructions` by metis_tac[supply_split_opcodes] >>
  fs[fn_insts_def] >>
  fs[ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM inst bb.bb_instructions` >>
  drule_all insert_split_supply_block_cases >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >>
  `MEM inst.inst_opcode
    (MAP (\i. i.inst_opcode) bb'.bb_instructions)` by
    (qpat_x_assum `MEM inst _` mp_tac >>
     metis_tac[supply_block_image_opcodes, listTheory.MEM_MAP]) >>
  gvs[listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem insert_split_supply_def_dominates_uses:
  wf_function fn /\ wf_ssa fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  def_dominates_uses fn'
Proof
  strip_tac >> simp[def_dominates_uses_def] >> rpt strip_tac >>
  drule_all insert_split_supply_block_cases >> strip_tac
  >- (gvs[] >> drule_all insert_split_supply_split_uses >> simp[]) >>
  gvs[] >>
  rename1 `MEM inst (supply_block_image pred target split repls old_bb).bb_instructions` >>
  `?i. i < LENGTH old_bb.bb_instructions /\
       inst = EL i (supply_block_image pred target split repls old_bb).bb_instructions` by
    metis_tac[listTheory.MEM_EL, supply_block_image_length] >>
  gvs[] >> irule insert_split_supply_old_block_uses >>
  gvs[wf_ssa_def] >> metis_tac[]
QED

Theorem insert_split_supply_wf_ssa:
  wf_function fn /\ wf_ssa fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  wf_ssa fn'
Proof
  strip_tac >> simp[wf_ssa_def] >> conj_tac
  >- (irule insert_split_supply_ssa_form >> gvs[wf_ssa_def] >> metis_tac[]) >>
  irule insert_split_supply_def_dominates_uses >> metis_tac[]
QED

Theorem supply_first_block_no_preds:
  wf_function fn ==>
  (first_block_no_preds fn <=>
   !a. ~fn_cfg_edge fn a (HD fn.fn_blocks).bb_label)
Proof
  simp[first_block_no_preds_def, fn_cfg_edge_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem insert_split_supply_first_block_no_preds:
  wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  insert_split_supply s fn pred target = (fn',s') ==>
  first_block_no_preds fn'
Proof
  strip_tac >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `fn.fn_blocks <> [] /\ fn'.fn_blocks <> []` by
    gvs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label fn' = fn_entry_label fn` by
    (irule insert_split_supply_entry >> metis_tac[]) >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  `MEM (HD fn.fn_blocks).bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >>
     qexists `HD fn.fn_blocks` >> Cases_on `fn.fn_blocks` >> gvs[]) >>
  `~?a. fn_cfg_edge fn a (HD fn.fn_blocks).bb_label` by
    metis_tac[supply_first_block_no_preds] >>
  drule_all insert_split_supply_no_incoming >>
  metis_tac[supply_first_block_no_preds]
QED

Definition supply_norm_inv_def:
  supply_norm_inv s fn <=>
    wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s
End

Theorem supply_norm_inv_projections:
  supply_norm_inv s fn ==>
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s
Proof
  simp[supply_norm_inv_def]
QED

Theorem insert_split_supply_norm_inv:
  supply_norm_inv s fn /\ MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  fn_cfg_edge fn pred.bb_label target.bb_label /\
  insert_split_supply s fn pred target = (fn',s') ==>
  supply_norm_inv s' fn'
Proof
  strip_tac >> drule supply_norm_inv_projections >> strip_tac >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `s1 = s'` by gvs[insert_split_supply_def] >> gvs[] >>
  `wf_ssa fn'` by (irule insert_split_supply_wf_ssa >> metis_tac[]) >>
  `fn_inst_wf fn'` by metis_tac[insert_split_supply_fn_inst_wf] >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `first_block_no_preds fn'` by metis_tac[insert_split_supply_first_block_no_preds] >>
  drule_all insert_split_supply_contract >> strip_tac >>
  `ir_supply_inst_ok s'` by
    gvs[cfg_fn_supply_contract_def, cfg_supply_extends_def] >>
  `cfg_supply_covers_fn s fn` by
    gvs[cfg_supply_covers_fn_def, ir_supply_covers_fn_def,
      list_subset_def, listTheory.EVERY_MEM] >>
  `cfg_supply_covers_block s pred /\ cfg_supply_covers_block s target` by
    (gvs[cfg_supply_covers_fn_blocks, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all insert_split_supply_covered >> strip_tac >>
  gvs[supply_norm_inv_def, cfg_supply_covers_fn_def, ir_supply_covers_fn_def,
      list_subset_def, irSupplyTheory.ir_supply_inst_ok_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem find_and_split_supply_norm_inv:
  supply_norm_inv s fn /\ EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
  find_and_split_supply fn s bbs = (fn',changed,s') ==>
  supply_norm_inv s' fn'
Proof
  strip_tac >> drule find_and_split_supply_cases >> strip_tac
  >- gvs[] >>
  `MEM target fn.fn_blocks` by
    (gvs[listTheory.EVERY_MEM] >> first_x_assum irule >> simp[]) >>
  `fn_cfg_edge fn pred.bb_label target.bb_label` by
    (simp[fn_cfg_edge_def] >> qexists `pred` >> simp[]) >>
  irule insert_split_supply_norm_inv >> metis_tac[]
QED

Theorem cfg_norm_round_supply_norm_inv:
  supply_norm_inv s fn /\ cfg_norm_round_supply s fn = (fn',changed,s') ==>
  supply_norm_inv s' fn'
Proof
  simp[cfg_norm_round_supply_def] >> strip_tac >>
  irule find_and_split_supply_norm_inv >>
  qexistsl [`fn.fn_blocks`, `changed`, `fn`, `s`] >>
  simp[listTheory.EVERY_MEM]
QED

Theorem cfg_norm_iter_supply_norm_inv:
  !n s fn fn' s'.
    supply_norm_inv s fn /\ cfg_norm_iter_supply n s fn = (fn',s') ==>
    supply_norm_inv s' fn'
Proof
  Induct_on `n` >> rpt gen_tac
  >- (strip_tac >> gvs[cfg_norm_iter_supply_def]) >>
  strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (mid,changed,s1)` >>
  `supply_norm_inv s1 mid` by metis_tac[cfg_norm_round_supply_norm_inv] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def] >> metis_tac[]
QED

Theorem cfg_norm_function_supply_norm_inv:
  supply_norm_inv s fn /\ cfg_norm_function_supply s fn = (fn',s') ==>
  supply_norm_inv s' fn'
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_norm_inv]
QED

(* Agreement deliberately ignores fresh variables and control fields. *)
Definition supply_state_agree_def:
  supply_state_agree fn st st' <=>
    execution_frame st = execution_frame st' /\
    !v. MEM v (irSupply$fn_ir_vars fn) ==> lookup_var v st = lookup_var v st'
End

Theorem supply_state_agree_refl[simp]:
  supply_state_agree fn st st
Proof
  simp[supply_state_agree_def]
QED

Theorem supply_state_agree_sym:
  supply_state_agree fn st st' ==> supply_state_agree fn st' st
Proof
  simp[supply_state_agree_def] >> metis_tac[]
QED

Theorem supply_state_agree_trans:
  supply_state_agree fn st1 st2 /\ supply_state_agree fn st2 st3 ==>
  supply_state_agree fn st1 st3
Proof
  simp[supply_state_agree_def] >> metis_tac[]
QED

Theorem supply_state_agree_lookup:
  supply_state_agree fn st st' /\ MEM v (irSupply$fn_ir_vars fn) ==>
  lookup_var v st = lookup_var v st'
Proof
  simp[supply_state_agree_def]
QED

Theorem supply_state_agree_update_fresh:
  supply_state_agree fn st st' /\ ~MEM v (irSupply$fn_ir_vars fn) ==>
  supply_state_agree fn st (update_var v value st')
Proof
  simp[supply_state_agree_def, venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
       execution_frame_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem supply_state_agree_update:
  supply_state_agree fn st st' ==>
  supply_state_agree fn (update_var v value st) (update_var v value st')
Proof
  simp[supply_state_agree_def, venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
       execution_frame_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v' = v` >> simp[]
QED

Theorem supply_fresh_assign_agree:
  supply_state_agree fn st st' /\ ~MEM out (irSupply$fn_ir_vars fn) /\
  lookup_var src st' = SOME value ==>
  step_inst_base
    <|inst_id := id; inst_opcode := ASSIGN;
      inst_operands := [Var src]; inst_outputs := [out]|> st' =
      OK (update_var out value st') /\
  supply_state_agree fn st (update_var out value st')
Proof
  strip_tac >> conj_tac
  >- simp[venomExecSemanticsTheory.step_inst_base_def, venomStateTheory.eval_operand_def] >>
  irule supply_state_agree_update_fresh >> simp[]
QED

Theorem supply_forwarding_run:
  !vars s repls insts s' st fuel ctx.
    ir_supply_inst_ok s /\
    build_forwarding_assigns_supply s vars = (repls,insts,s') /\
    EVERY (\v. MEM v s.irs_used_vars /\ IS_SOME (lookup_var v st)) vars ==>
    ?out. run_insts fuel ctx insts st = OK out /\
      execution_frame out = execution_frame st /\
      (!v. MEM v s.irs_used_vars ==> lookup_var v out = lookup_var v st) /\
      (!src dst. MEM (src,dst) repls ==>
        MEM src vars /\ lookup_var dst out = lookup_var src st)
Proof
  Induct_on `vars`
  >- simp[build_forwarding_assigns_supply_def, run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (nv,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >>
  PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def, Excl "execution_frame_def"] >>
  drule (cj 1 irSupplyTheory.fresh_ir_var_contract) >> strip_tac >>
  drule (cj 2 irSupplyTheory.fresh_ir_var_contract) >> strip_tac >>
  `ir_supply_inst_ok s1` by metis_tac[fresh_ir_var_cfg_supply_extends,
    cfg_supply_extends_def] >>
  drule_all irSupplyTheory.fresh_inst_id_contract >> strip_tac >>
  `EVERY (\v. MEM v s2.irs_used_vars /\
       IS_SOME (lookup_var v (update_var nv (THE (lookup_var h st)) st))) vars` by
    (gvs[listTheory.EVERY_MEM, venomStateTheory.lookup_var_def,
         venomStateTheory.update_var_def, FLOOKUP_UPDATE,
         Excl "execution_frame_def"] >> metis_tac[]) >>
  first_x_assum drule_all >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexists_tac `out` >>
  conj_tac
  >- (simp[run_insts_def, venomExecSemanticsTheory.step_inst_def,
        venomExecSemanticsTheory.step_inst_base_def,
        venomStateTheory.eval_operand_def, optionTheory.IS_SOME_EXISTS,
        optionTheory.THE_DEF] >>
      Cases_on `lookup_var h st` >> gvs[]) >>
  conj_tac
  >- gvs[venomStateTheory.update_var_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum (qspec_then `v` mp_tac) >>
      simp[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
           FLOOKUP_UPDATE] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >>
  gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
      FLOOKUP_UPDATE, listTheory.EVERY_MEM] >>
  Cases_on `FLOOKUP st.vs_vars h` >> gvs[] >> metis_tac[]
QED

Theorem supply_forwarding_run_agree:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  build_forwarding_assigns_supply s vars = (repls,insts,s') /\
  EVERY (\v. MEM v s.irs_used_vars /\ IS_SOME (lookup_var v st')) vars /\
  supply_state_agree fn st st' ==>
  ?out. run_insts fuel ctx insts st' = OK out /\
    supply_state_agree fn st out /\
    (!src dst. MEM (src,dst) repls ==>
      MEM src vars /\ lookup_var dst out = lookup_var src st')
Proof
  strip_tac >> drule_all supply_forwarding_run >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexists_tac `out` >> simp[] >>
  gvs[supply_state_agree_def, ir_supply_covers_fn_def,
      list_subset_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem supply_forwarding_exec_prefix:
  ir_supply_inst_ok s /\
  build_forwarding_assigns_supply s vars = (repls,insts,s') /\
  EVERY (\v. MEM v s.irs_used_vars /\ IS_SOME (lookup_var v st)) vars /\
  bb.bb_instructions = insts ++ rest ==>
  ?out. exec_block fuel ctx bb (st with vs_inst_idx := 0) =
          exec_block fuel ctx bb (out with vs_inst_idx := LENGTH insts) /\
    execution_frame out = execution_frame st /\
    (!v. MEM v s.irs_used_vars ==> lookup_var v out = lookup_var v st) /\
    (!src dst. MEM (src,dst) repls ==>
      MEM src vars /\ lookup_var dst out = lookup_var src st)
Proof
  strip_tac >> drule_all supply_forwarding_run >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts` by
    (drule supply_forwarding_opcodes >>
     rewrite_tac[listTheory.EVERY_MEM] >> disch_tac >>
     rpt strip_tac >>
     qpat_x_assum `!i. MEM i insts ==> _` drule >>
     simp[venomInstTheory.is_terminator_def]) >>
  qexists_tac `out` >> conj_tac
  >- (drule_at (Pat `run_insts _ _ _ _ = _`) exec_block_skip_prefix >>
      disch_then (qspecl_then [`bb`, `0`] mp_tac) >>
      simp[listTheory.EL_APPEND_EQN]) >>
  gvs[] >> metis_tac[]
QED

Theorem supply_assigns_run_control:
  !insts st out fuel ctx.
    EVERY (\i. i.inst_opcode = ASSIGN) insts /\
    run_insts fuel ctx insts st = OK out ==>
    out.vs_current_bb = st.vs_current_bb /\
    out.vs_prev_bb = st.vs_prev_bb /\
    out.vs_inst_idx = st.vs_inst_idx
Proof
  Induct_on `insts`
  >- simp[run_insts_def] >>
  rpt gen_tac >> simp[run_insts_def] >> strip_tac >>
  Cases_on `step_inst fuel ctx h st` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_def,
       venomExecSemanticsTheory.step_inst_base_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[venomStateTheory.update_var_def]
QED

Theorem supply_assigns_exec_jmp:
  EVERY (\i. i.inst_opcode = ASSIGN) insts /\
  run_insts fuel ctx insts st = OK out /\ ~out.vs_halted /\
  bb.bb_instructions = insts ++
    [<|inst_id := id; inst_opcode := JMP;
       inst_operands := [Label target]; inst_outputs := []|>] ==>
  exec_block fuel ctx bb (st with vs_inst_idx := 0) =
    OK (jump_to target (out with vs_inst_idx := LENGTH insts))
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts` by
    (qpat_x_assum `EVERY _ insts` mp_tac >>
     rewrite_tac[listTheory.EVERY_MEM] >> disch_tac >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i insts ==> _` drule >>
     simp[venomInstTheory.is_terminator_def]) >>
  drule_at (Pat `run_insts _ _ _ _ = _`) exec_block_skip_prefix >>
  disch_then (qspecl_then [`bb`, `0`] mp_tac) >>
  simp[listTheory.EL_APPEND_EQN] >> disch_then SUBST1_TAC >>
  once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
  simp[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN] >>
  simp[venomExecSemanticsTheory.step_inst_def] >>
  simp[venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.is_terminator_def] >>
  simp[venomStateTheory.jump_to_def]
QED

Theorem supply_split_exec:
  ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  EVERY (\v. MEM v s.irs_used_vars /\ IS_SOME (lookup_var v st))
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions)) /\
  ~st.vs_halted ==>
  ?out. exec_block fuel ctx split (st with vs_inst_idx := 0) = OK out /\
    execution_frame out = execution_frame st /\
    (!v. MEM v s.irs_used_vars ==> lookup_var v out = lookup_var v st) /\
    (!src dst. MEM (src,dst) repls ==>
       MEM src (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions)) /\
       lookup_var dst out = lookup_var src st) /\
    out.vs_current_bb = target.bb_label /\
    out.vs_prev_bb = SOME st.vs_current_bb /\ out.vs_inst_idx = 0
Proof
  strip_tac >>
  Cases_on `fresh_ir_label s` >> rename1 `fresh_ir_label s = (lbl,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def] >>
  drule irSupplyTheory.fresh_ir_label_contract >> strip_tac >>
  `ir_supply_inst_ok s1` by gvs[irSupplyTheory.ir_supply_inst_ok_def] >>
  `EVERY (\v. MEM v s1.irs_used_vars /\ IS_SOME (lookup_var v st))
     (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` by simp[] >>
  drule_all supply_forwarding_run >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  drule supply_forwarding_opcodes >> disch_tac >>
  `~out.vs_halted` by gvs[] >>
  drule_all supply_assigns_run_control >> strip_tac >>
  qexists_tac `jump_to target.bb_label (out with vs_inst_idx := LENGTH r0)` >>
  conj_tac
  >- (irule supply_assigns_exec_jmp >> simp[] >> metis_tac[]) >>
  gvs[venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def,
      execution_frame_def] >> metis_tac[]
QED

(* Resolution is independent of PHI writes: both reads use fixed snapshots. *)
Theorem supply_eval_one_phi_split:
  st.vs_prev_bb = SOME pred /\ st'.vs_prev_bb = SOME split /\
  resolve_phi split inst.inst_operands = NONE /\
  (!op. resolve_phi pred inst.inst_operands = SOME op ==>
    eval_operand
      (case op of Var v =>
        (case ALOOKUP repls v of NONE => Var v | SOME w => Var w)
       | x => x) st' = eval_operand op st) ==>
  eval_one_phi st'
    (inst with inst_operands := update_phi_ops pred split repls inst.inst_operands) =
  eval_one_phi st inst
Proof
  strip_tac >>
  Cases_on `inst.inst_outputs` >- simp[venomExecSemanticsTheory.eval_one_phi_def] >>
  Cases_on `t` >> simp[venomExecSemanticsTheory.eval_one_phi_def] >>
  Cases_on `resolve_phi pred inst.inst_operands`
  >- (Cases_on `resolve_phi split
        (update_phi_ops pred split repls inst.inst_operands)` >> simp[] >>
      drule_all resolve_phi_update_phi_ops_match_rev >> simp[]) >>
  drule_all resolve_phi_update_phi_ops_match >> disch_tac >>
  gvs[]
QED

(* Sources are evaluated in st/st' throughout the induction, not in the
   recursively returned states. This also covers self-loop PHIs. *)
Theorem supply_eval_phis_agree:
  !insts insts' st st' out.
  LIST_REL (\i j. i.inst_opcode = j.inst_opcode /\
    (i.inst_opcode = PHI ==> eval_one_phi st i = eval_one_phi st' j)) insts insts' /\
  supply_state_agree fn st st' /\ eval_phis st insts = OK out ==>
  ?out'. eval_phis st' insts' = OK out' /\ supply_state_agree fn out out'
Proof
  Induct_on `insts` >> Cases_on `insts'` >>
  simp[venomExecSemanticsTheory.eval_phis_def] >> rpt strip_tac >>
  rename1 `i.inst_opcode = j.inst_opcode` >>
  Cases_on `i.inst_opcode = PHI`
  >- (gvs[] >>
      Cases_on `eval_one_phi st' j` >>
      gvs[venomExecSemanticsTheory.eval_phis_def] >>
      PairCases_on `x` >>
      Cases_on `eval_phis st insts` >> gvs[] >>
      first_x_assum (qspecl_then [`t`, `st`, `st'`, `v`] mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `update_var x0 x1 out'` >>
      simp[venomExecSemanticsTheory.eval_phis_def] >>
      irule supply_state_agree_update >> simp[]) >>
  gvs[venomExecSemanticsTheory.eval_phis_def] >> metis_tac[]
QED

Theorem supply_eval_operand_agree:
  supply_state_agree fn st st' /\
  (!v. op = Var v ==> MEM v (irSupply$fn_ir_vars fn)) ==>
  eval_operand op st = eval_operand op st'
Proof
  strip_tac >> Cases_on `op` >>
  simp[venomStateTheory.eval_operand_def]
  >- metis_tac[supply_state_agree_lookup] >>
  `st.vs_labels = st'.vs_labels` by
    (gvs[supply_state_agree_def] >>
     qpat_x_assum `execution_frame _ = execution_frame _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_labels``) >>
     simp[execution_frame_def]) >> simp[]
QED

Theorem supply_eval_operand_replacement:
  eval_operand op st' = eval_operand op st /\
  (!v w. op = Var v /\ ALOOKUP repls v = SOME w ==>
     lookup_var w st' = lookup_var v st) ==>
  eval_operand
    (case op of Var v =>
       (case ALOOKUP repls v of NONE => Var v | SOME w => Var w)
     | x => x) st' = eval_operand op st
Proof
  Cases_on `op` >> simp[venomStateTheory.eval_operand_def] >>
  Cases_on `ALOOKUP repls s` >> simp[venomStateTheory.eval_operand_def]
QED

Theorem supply_eval_phis_split:
  supply_state_agree fn st st' /\
  st.vs_prev_bb = SOME pred /\ st'.vs_prev_bb = SOME split /\
  (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    resolve_phi split inst.inst_operands = NONE /\
    (!op. resolve_phi pred inst.inst_operands = SOME op ==>
      eval_operand
        (case op of Var v =>
          (case ALOOKUP repls v of NONE => Var v | SOME w => Var w)
         | x => x) st' = eval_operand op st)) /\
  eval_phis st bb.bb_instructions = OK out ==>
  ?out'. eval_phis st'
    (update_phis_for_split pred split repls bb).bb_instructions = OK out' /\
    supply_state_agree fn out out'
Proof
  strip_tac >>
  simp[update_phis_for_split_def] >>
  irule supply_eval_phis_agree >>
  qexistsl_tac [`bb.bb_instructions`, `st`] >> simp[] >>
  simp[listTheory.EVERY2_MAP] >>
  irule listTheory.EVERY2_refl >> rpt strip_tac >>
  rename1 `MEM inst bb.bb_instructions` >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  irule EQ_SYM >> irule supply_eval_one_phi_split >>
  simp[] >> first_x_assum drule >> simp[]
QED

Theorem supply_eval_one_phi_other:
  st.vs_prev_bb = SOME prev /\ st'.vs_prev_bb = SOME prev /\
  prev <> pred /\ prev <> split /\
  (!op. resolve_phi prev inst.inst_operands = SOME op ==>
     eval_operand op st' = eval_operand op st) ==>
  eval_one_phi st'
    (inst with inst_operands := update_phi_ops pred split repls inst.inst_operands) =
  eval_one_phi st inst
Proof
  strip_tac >>
  `resolve_phi prev (update_phi_ops pred split repls inst.inst_operands) =
    resolve_phi prev inst.inst_operands` by
    (irule resolve_phi_update_phi_ops_other >> simp[]) >>
  Cases_on `inst.inst_outputs` >- simp[venomExecSemanticsTheory.eval_one_phi_def] >>
  Cases_on `t` >> simp[venomExecSemanticsTheory.eval_one_phi_def] >>
  Cases_on `resolve_phi prev inst.inst_operands` >> gvs[]
QED

Theorem supply_eval_phis_other:
  supply_state_agree fn st st' /\
  st.vs_prev_bb = SOME prev /\ st'.vs_prev_bb = SOME prev /\
  prev <> pred /\ prev <> split /\
  (!inst op. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
     resolve_phi prev inst.inst_operands = SOME op ==>
     eval_operand op st' = eval_operand op st) /\
  eval_phis st bb.bb_instructions = OK out ==>
  ?out'. eval_phis st'
    (update_phis_for_split pred split repls bb).bb_instructions = OK out' /\
    supply_state_agree fn out out'
Proof
  strip_tac >> simp[update_phis_for_split_def] >>
  irule supply_eval_phis_agree >>
  qexistsl_tac [`bb.bb_instructions`, `st`] >> simp[] >>
  simp[listTheory.EVERY2_MAP] >>
  irule listTheory.EVERY2_refl >> rpt strip_tac >>
  rename1 `MEM inst bb.bb_instructions` >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  irule EQ_SYM >> irule supply_eval_one_phi_other >> simp[] >>
  metis_tac[]
QED

(* A lookup-level interface for callers of the split execution boundary.
   Non-forwarded operands use old-variable agreement; forwarded operands
   use the original pre-PHI snapshot, even on self-loops. *)
Theorem supply_eval_phis_forwarded:
  supply_state_agree fn st st' /\
  st.vs_prev_bb = SOME pred /\ st'.vs_prev_bb = SOME split /\
  (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    resolve_phi split inst.inst_operands = NONE /\
    (!v. MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn))) /\
  (!src dst. ALOOKUP repls src = SOME dst ==>
    lookup_var dst st' = lookup_var src st) /\
  eval_phis st bb.bb_instructions = OK out ==>
  ?out'. eval_phis st'
    (update_phis_for_split pred split repls bb).bb_instructions = OK out' /\
    supply_state_agree fn out out'
Proof
  strip_tac >> irule supply_eval_phis_split >> simp[] >>
  qexists_tac `st` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!inst. MEM inst _ /\ _ ==> _` drule >>
  simp[] >> strip_tac >> simp[] >> rpt strip_tac >>
  irule supply_eval_operand_replacement >> simp[] >>
  irule EQ_SYM >> irule supply_eval_operand_agree >> simp[] >>
  metis_tac[execEquivParamBaseTheory.resolve_phi_MEM]
QED

(* The exception set is exactly the complement of the old names. *)
Theorem supply_state_agree_execution_equiv:
  supply_state_agree fn st st' <=>
  execution_equiv (COMPL (set (irSupply$fn_ir_vars fn))) st st'
Proof
  simp[supply_state_agree_def, stateEquivTheory.execution_equiv_def] >>
  metis_tac[]
QED

Theorem supply_state_agree_state_equiv:
  supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  st.vs_inst_idx = st'.vs_inst_idx /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  state_equiv (COMPL (set (irSupply$fn_ir_vars fn))) st st'
Proof
  simp[stateEquivTheory.state_equiv_def,
       GSYM supply_state_agree_execution_equiv]
QED

Theorem supply_step_inst:
  supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  st.vs_inst_idx = st'.vs_inst_idx /\ st.vs_prev_bb = st'.vs_prev_bb /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn)) ==>
  lift_result (state_equiv (COMPL (set (irSupply$fn_ir_vars fn))))
    (execution_equiv (COMPL (set (irSupply$fn_ir_vars fn))))
    (execution_equiv (COMPL (set (irSupply$fn_ir_vars fn))))
    (step_inst fuel ctx inst st) (step_inst fuel ctx inst st')
Proof
  strip_tac >> irule step_inst_preserves_R >>
  simp[state_equiv_execution_equiv_valid_state_rel] >> conj_tac
  >- metis_tac[supply_state_agree_lookup] >>
  irule supply_state_agree_state_equiv >> simp[]
QED

Theorem supply_operand_in_fn:
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn)
Proof
  simp[irSupplyTheory.fn_ir_vars_def, irSupplyTheory.block_ir_vars_def,
       irSupplyTheory.inst_ir_vars_def, venomInstTheory.inst_uses_def,
       listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS,
       passSharedDefsTheory.MEM_operand_vars_eq_Var] >> metis_tac[]
QED

Theorem supply_exec_block:
  MEM bb fn.fn_blocks /\ supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  st.vs_inst_idx = st'.vs_inst_idx /\ st.vs_prev_bb = st'.vs_prev_bb ==>
  lift_result (state_equiv (COMPL (set (irSupply$fn_ir_vars fn))))
    (execution_equiv (COMPL (set (irSupply$fn_ir_vars fn))))
    (execution_equiv (COMPL (set (irSupply$fn_ir_vars fn))))
    (exec_block fuel ctx bb st) (exec_block fuel ctx bb st')
Proof
  strip_tac >>
  mp_tac (Q.SPEC `fn` (Q.SPECL
    [`state_equiv (COMPL (set (irSupply$fn_ir_vars fn)))`,
     `execution_equiv (COMPL (set (irSupply$fn_ir_vars fn)))`]
    exec_block_preserves_R)) >>
  impl_tac
  >- (simp[state_equiv_execution_equiv_valid_state_rel] >>
      rpt conj_tac
      >- metis_tac[stateEquivPropsTheory.state_equiv_trans]
      >- metis_tac[stateEquivPropsTheory.execution_equiv_trans] >>
      rpt strip_tac >>
      irule supply_state_agree_lookup >>
      qexists_tac `fn` >>
      gvs[GSYM supply_state_agree_execution_equiv, stateEquivTheory.state_equiv_def] >>
      metis_tac[supply_operand_in_fn]) >>
  strip_tac >> first_x_assum irule >> simp[] >>
  irule supply_state_agree_state_equiv >> simp[]
QED

(* Previous-label normalization is needed only after parallel PHI entry. *)
Theorem supply_step_nonterm_prev_bb:
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode ==>
  step_inst fuel ctx inst (st with vs_prev_bb := p) =
  exec_result_map_prev_bb (\s. s with vs_prev_bb := p)
    (step_inst fuel ctx inst st)
Proof
  strip_tac >> simp[venomExecSemanticsTheory.step_inst_def] >>
  irule step_inst_base_prev_bb_indep >> simp[]
QED

Theorem supply_state_agree_prev_bb:
  supply_state_agree fn st (st' with vs_prev_bb := p) <=>
  supply_state_agree fn st st'
Proof
  simp[supply_state_agree_def, stateFrameTheory.execution_frame_def,
       venomStateTheory.lookup_var_def]
QED

Theorem supply_step_nonterm:
  supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  st.vs_inst_idx = st'.vs_inst_idx /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn)) ==>
  lift_result
    (\s t. supply_state_agree fn s t /\
           s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx)
    (supply_state_agree fn) (supply_state_agree fn)
    (step_inst fuel ctx inst st) (step_inst fuel ctx inst st')
Proof
  strip_tac >>
  `supply_state_agree fn st (st' with vs_prev_bb := st.vs_prev_bb)` by
    simp[supply_state_agree_prev_bb] >>
  drule supply_step_inst >>
  disch_then (qspecl_then [`inst`,`fuel`,`ctx`] mp_tac) >>
  simp[supply_step_nonterm_prev_bb] >>
  Cases_on `step_inst fuel ctx inst st` >>
  Cases_on `step_inst fuel ctx inst st'` >>
  simp[exec_result_map_prev_bb_def, stateEquivTheory.lift_result_def,
       stateEquivTheory.state_equiv_def,
       GSYM supply_state_agree_execution_equiv, supply_state_agree_prev_bb]
QED

Theorem supply_bind_outputs_prev_bb:
  bind_outputs outs vals (st with vs_prev_bb := p) =
  OPTION_MAP (\s. s with vs_prev_bb := p) (bind_outputs outs vals st)
Proof
  simp[venomExecSemanticsTheory.bind_outputs_def] >>
  Cases_on `LENGTH outs = LENGTH vals` >> simp[] >>
  qspec_tac (`ZIP (outs,vals)`, `kvs`) >> qid_spec_tac `st` >>
  Induct_on `kvs` >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[] >> first_x_assum (qspec_then `update_var h0 h1 st` mp_tac) >>
  simp[venomStateTheory.update_var_def]
QED

Theorem supply_eval_operand_prev_bb:
  eval_operand op (st with vs_prev_bb := p) = eval_operand op st
Proof
  Cases_on `op` >> simp[venomStateTheory.eval_operand_def,
                       venomStateTheory.lookup_var_def]
QED

Theorem supply_eval_operands_prev_bb:
  !ops. eval_operands ops (st with vs_prev_bb := p) = eval_operands ops st
Proof
  Induct >> simp[venomStateTheory.eval_operands_def, supply_eval_operand_prev_bb]
QED

Theorem supply_step_invoke_prev_bb:
  inst.inst_opcode = INVOKE ==>
  step_inst fuel ctx inst (st with vs_prev_bb := p) =
  case step_inst fuel ctx inst st of
    OK r => OK (r with vs_prev_bb := p)
  | Halt r => Halt r
  | Abort a r => Abort a r
  | IntRet ir r => IntRet ir r
  | Error e => Error e
Proof
  strip_tac >>
  simp[venomExecSemanticsTheory.step_inst_def, supply_eval_operands_prev_bb] >>
  Cases_on `decode_invoke inst` >> simp[] >> PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands x1 st` >> simp[] >>
  `setup_callee x x' (st with vs_prev_bb := p) = setup_callee x x' st` by
    simp[venomExecSemanticsTheory.setup_callee_def] >>
  simp[] >> Cases_on `setup_callee x x' st` >> simp[] >>
  rename1 `setup_callee _ _ st = SOME cs` >>
  Cases_on `run_blocks fuel ctx x cs` >> simp[] >>
  `merge_callee_state (st with vs_prev_bb := p) v =
   merge_callee_state st v with vs_prev_bb := p` by
    simp[venomExecSemanticsTheory.merge_callee_state_def] >>
  simp[] >>
  `adopt_return_fmp i (merge_callee_state st v with vs_prev_bb := p) =
   adopt_return_fmp i (merge_callee_state st v) with vs_prev_bb := p` by
    (simp[venomExecSemanticsTheory.adopt_return_fmp_def] >>
     Cases_on `i.iret_adopt_fmp` >> simp[]) >>
  simp[supply_bind_outputs_prev_bb] >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state st v))` >> simp[]
QED

Theorem supply_step_invoke:
  supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\
  st.vs_inst_idx = st'.vs_inst_idx /\
  inst.inst_opcode = INVOKE /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn)) ==>
  lift_result
    (\s t. supply_state_agree fn s t /\
           s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx)
    (supply_state_agree fn) (supply_state_agree fn)
    (step_inst fuel ctx inst st) (step_inst fuel ctx inst st')
Proof
  strip_tac >>
  `supply_state_agree fn st (st' with vs_prev_bb := st.vs_prev_bb)` by
    simp[supply_state_agree_prev_bb] >>
  drule supply_step_inst >>
  disch_then (qspecl_then [`inst`,`fuel`,`ctx`] mp_tac) >>
  simp[supply_step_invoke_prev_bb] >>
  Cases_on `step_inst fuel ctx inst st` >>
  Cases_on `step_inst fuel ctx inst st'` >>
  simp[stateEquivTheory.lift_result_def, stateEquivTheory.state_equiv_def,
       GSYM supply_state_agree_execution_equiv, supply_state_agree_prev_bb]
QED

(* A data Label in the branch condition is allowed by inst_wf. *)
Theorem supply_redirect_label_condition_probe:
  inst_wf <| inst_id := 0; inst_opcode := JNZ;
             inst_operands := [Label "t"; Label "t"; Label "exit"];
             inst_outputs := [] |> /\
  (step_inst_base
    <| inst_id := 0; inst_opcode := JNZ;
       inst_operands := [Label "t"; Label "t"; Label "exit"];
       inst_outputs := [] |>
    ((init_venom_state "p") with vs_labels := FEMPTY |+ ("t",0w) |+ ("q",1w)) =
   OK (jump_to "exit"
    ((init_venom_state "p") with vs_labels := FEMPTY |+ ("t",0w) |+ ("q",1w)))) /\
  (step_inst_base
    (subst_label_inst "t" "q"
      <| inst_id := 0; inst_opcode := JNZ;
         inst_operands := [Label "t"; Label "t"; Label "exit"];
         inst_outputs := [] |>)
    ((init_venom_state "p") with vs_labels := FEMPTY |+ ("t",0w) |+ ("q",1w)) =
   OK (jump_to "q"
    ((init_venom_state "p") with vs_labels := FEMPTY |+ ("t",0w) |+ ("q",1w))))
Proof
  EVAL_TAC >> simp[wordsTheory.WORD_EQ]
QED

Definition supply_probe_fn_def:
  supply_probe_fn = mk_raw_function "probe"
    [<| bb_label := "p"; bb_instructions :=
         [<| inst_id := 0; inst_opcode := JNZ;
             inst_operands := [Label "t"; Label "t"; Label "exit"];
             inst_outputs := [] |>] |>;
     <| bb_label := "exit"; bb_instructions :=
         [<| inst_id := 1; inst_opcode := STOP;
             inst_operands := []; inst_outputs := [] |>] |>;
     <| bb_label := "other"; bb_instructions :=
         [<| inst_id := 2; inst_opcode := JMP;
             inst_operands := [Label "t"]; inst_outputs := [] |>] |>;
     <| bb_label := "t"; bb_instructions :=
         [<| inst_id := 3; inst_opcode := REVERT;
             inst_operands := [Lit 0w; Lit 0w]; inst_outputs := [] |>] |>]
End

Definition supply_probe_supply_def:
  supply_probe_supply =
    <| irs_next_inst := 4; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [0;1;2;3]; irs_used_vars := [];
       irs_used_labels := ["probe";"p";"exit";"other";"t"] |>
End

Theorem supply_probe_premises:
  wf_ssa supply_probe_fn /\ fn_inst_wf supply_probe_fn /\
  wf_function supply_probe_fn /\ first_block_no_preds supply_probe_fn /\
  ir_supply_covers_fn supply_probe_supply supply_probe_fn /\
  ir_supply_inst_ok supply_probe_supply
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Definition supply_probe_fn'_def:
  supply_probe_fn' = supply_probe_fn with fn_blocks :=
    [<| bb_label := "p"; bb_instructions :=
         [<| inst_id := 0; inst_opcode := JNZ;
             inst_operands := [Label "formal_label_0"; Label "formal_label_0"; Label "exit"];
             inst_outputs := [] |>] |>;
     EL 1 supply_probe_fn.fn_blocks;
     EL 2 supply_probe_fn.fn_blocks;
     EL 3 supply_probe_fn.fn_blocks;
     <| bb_label := "formal_label_0"; bb_instructions :=
         [<| inst_id := 4; inst_opcode := JMP;
             inst_operands := [Label "t"]; inst_outputs := [] |>] |>]
End

Theorem supply_probe_transform:
  cfg_norm_function_supply supply_probe_supply supply_probe_fn =
  (supply_probe_fn', supply_probe_supply with
    <| irs_next_inst := 5; irs_next_label := 1;
       irs_used_inst_ids := [4;0;1;2;3];
       irs_used_labels := "formal_label_0" :: supply_probe_supply.irs_used_labels |>)
Proof
  EVAL_TAC
QED

Definition supply_probe_state_def:
  supply_probe_state = (init_venom_state "p") with
    vs_labels := FEMPTY |+ ("t",0w) |+ ("formal_label_0",1w)
End

(* Counterexample certificates for the unconstrained entry label table. *)
Theorem supply_probe_entry:
  fn_entry_state supply_probe_fn supply_probe_state
Proof
  EVAL_TAC
QED

Theorem supply_probe_original_terminates:
  terminates (run_blocks 3 ctx supply_probe_fn supply_probe_state)
Proof
  EVAL_TAC
QED

Theorem supply_probe_no_match:
  !fuel. ~frame_result_rel
    (run_blocks 3 ctx supply_probe_fn supply_probe_state)
    (run_blocks fuel ctx supply_probe_fn' supply_probe_state)
Proof
  gen_tac >> Cases_on `fuel` >- EVAL_TAC >>
  rename1 `SUC n` >>
  once_rewrite_tac[venomExecSemanticsTheory.run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  simp[wordsTheory.WORD_EQ] >>
  Cases_on `n`
  >- (once_rewrite_tac[venomExecSemanticsTheory.run_blocks_def] >>
      CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[]) >>
  once_rewrite_tac[venomExecSemanticsTheory.run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  rename1 `run_blocks n _ _ _` >> Cases_on `n` >>
  once_rewrite_tac[venomExecSemanticsTheory.run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[]
QED

Theorem supply_probe_not_fn_bisim:
  ~fn_bisim supply_probe_fn supply_probe_fn'
Proof
  simp[fn_bisim_def] >>
  metis_tac[supply_probe_entry, supply_probe_original_terminates,
            supply_probe_no_match]
QED

(* A counterexample to the first frozen contract, without using that contract. *)
Theorem supply_probe_frozen_contract_counterexample:
  wf_ssa supply_probe_fn /\ fn_inst_wf supply_probe_fn /\
  wf_function supply_probe_fn /\ first_block_no_preds supply_probe_fn /\
  ir_supply_covers_fn supply_probe_supply supply_probe_fn /\
  ir_supply_inst_ok supply_probe_supply /\
  cfg_norm_function_supply supply_probe_supply supply_probe_fn =
    (supply_probe_fn', supply_probe_supply with
      <| irs_next_inst := 5; irs_next_label := 1;
         irs_used_inst_ids := [4;0;1;2;3];
         irs_used_labels := "formal_label_0" :: supply_probe_supply.irs_used_labels |>) /\
  ~fn_bisim supply_probe_fn supply_probe_fn'
Proof
  metis_tac[supply_probe_premises, supply_probe_transform,
            supply_probe_not_fn_bisim]
QED

(* The historical counterexample is excluded by the restated contracts. *)
Theorem supply_probe_not_label_positions_ok:
  ~EVERY label_positions_ok (fn_insts supply_probe_fn)
Proof
  EVAL_TAC
QED

Theorem supply_subst_label_op_nonlabel:
  ~is_label_operand op ==> subst_label_op old new op = op
Proof
  Cases_on `op` >>
  simp[stackPlanTypesTheory.is_label_operand_def, subst_label_op_def]
QED

Theorem supply_subst_label_inst_no_labels:
  EVERY (\op. ~is_label_operand op) inst.inst_operands ==>
  subst_label_inst old new inst = inst
Proof
  strip_tac >> simp[subst_label_inst_def] >>
  `MAP (subst_label_op old new) inst.inst_operands = inst.inst_operands` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     SPEC_TAC (``inst.inst_operands``, ``ops:operand list``) >> Induct >>
     simp[supply_subst_label_op_nonlabel]) >>
  simp[]
QED

Theorem supply_subst_label_nonjump_terminator:
  is_terminator inst.inst_opcode /\ label_positions_ok inst /\
  inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ ==>
  subst_label_inst old new inst = inst
Proof
  strip_tac >> irule supply_subst_label_inst_no_labels >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, label_positions_ok_def]
QED

Theorem supply_subst_label_JNZ:
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [c; Label t; Label f] /\ ~is_label_operand c ==>
  step_inst_base (subst_label_inst old new inst) st =
    (case step_inst_base inst st of
       OK v => OK (if v.vs_current_bb = old
                   then v with vs_current_bb := new else v)
     | Halt v => Halt v
     | Abort a v => Abort a v
     | IntRet r v => IntRet r v
     | Error e => Error e)
Proof
  strip_tac >>
  simp[venomExecSemanticsTheory.step_inst_base_def, subst_label_inst_def,
       supply_subst_label_op_nonlabel, subst_label_op_def] >>
  Cases_on `t = old` >> Cases_on `f = old` >> simp[] >>
  Cases_on `eval_operand c st` >> simp[] >>
  rename1 `SOME w` >> Cases_on `w = 0w` >>
  gvs[venomStateTheory.jump_to_def]
QED

Theorem supply_subst_label_JMP:
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label l] ==>
  step_inst_base (subst_label_inst old new inst) st =
    (case step_inst_base inst st of
       OK v => OK (if v.vs_current_bb = old
                   then v with vs_current_bb := new else v)
     | Halt v => Halt v
     | Abort a v => Abort a v
     | IntRet r v => IntRet r v
     | Error e => Error e)
Proof
  strip_tac >>
  simp[venomExecSemanticsTheory.step_inst_base_def, subst_label_inst_def,
       subst_label_op_def] >>
  Cases_on `l = old` >> gvs[venomStateTheory.jump_to_def]
QED

Theorem supply_label_safe_JNZ_shape:
  inst_wf inst /\ inst.inst_opcode = JNZ /\ label_positions_ok inst ==>
  ?c t f. inst.inst_operands = [c; Label t; Label f] /\ ~is_label_operand c
Proof
  strip_tac >> gvs[inst_wf_def] >>
  gvs[label_positions_ok_def] >> metis_tac[]
QED

Theorem supply_subst_label_terminator_base:
  inst_wf inst /\ is_terminator inst.inst_opcode /\ label_positions_ok inst ==>
  step_inst_base (subst_label_inst old new inst) st =
    (if inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ then
       case step_inst_base inst st of
         OK v => OK (if v.vs_current_bb = old
                     then v with vs_current_bb := new else v)
       | Halt v => Halt v
       | Abort a v => Abort a v
       | IntRet r v => IntRet r v
       | Error e => Error e
     else step_inst_base inst st)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = JMP`
  >- (gvs[inst_wf_def] >> irule supply_subst_label_JMP >> simp[]) >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (drule_all supply_label_safe_JNZ_shape >> strip_tac >>
      simp[] >> irule supply_subst_label_JNZ >> metis_tac[]) >>
  simp[] >> drule_all supply_subst_label_nonjump_terminator >> simp[]
QED

Theorem supply_subst_label_terminator_step:
  inst_wf inst /\ is_terminator inst.inst_opcode /\ label_positions_ok inst ==>
  step_inst fuel ctx (subst_label_inst old new inst) st =
    (if inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ then
       case step_inst fuel ctx inst st of
         OK v => OK (if v.vs_current_bb = old
                     then v with vs_current_bb := new else v)
       | Halt v => Halt v
       | Abort a v => Abort a v
       | IntRet r v => IntRet r v
       | Error e => Error e
     else step_inst fuel ctx inst st)
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  ` (subst_label_inst old new inst).inst_opcode <> INVOKE` by
    simp[subst_label_inst_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  irule supply_subst_label_terminator_base >> simp[]
QED

Theorem supply_subst_label_preserves_label_positions:
  inst_wf inst /\ label_positions_ok inst /\ is_terminator inst.inst_opcode /\
  ~MEM new (inst_ir_labels inst) ==>
  label_positions_ok (subst_label_inst old new inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = JMP`
  >- (gvs[inst_wf_def] >> Cases_on `lbl = old` >>
      simp[subst_label_inst_def, subst_label_op_def, label_positions_ok_def]) >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (drule_all supply_label_safe_JNZ_shape >> strip_tac >>
      gvs[irSupplyTheory.inst_ir_labels_def, irSupplyTheory.MEM_operand_ir_labels,
          label_positions_ok_def] >>
      Cases_on `t = old` >> Cases_on `f = old` >>
      gvs[subst_label_inst_def, supply_subst_label_op_nonlabel,
           subst_label_op_def, label_positions_ok_def]) >>
  drule_all supply_subst_label_nonjump_terminator >> simp[]
QED

Theorem supply_update_phis_label_positions:
  EVERY label_positions_ok bb.bb_instructions ==>
  EVERY label_positions_ok
    (update_phis_for_split old new repls bb).bb_instructions
Proof
  rewrite_tac[update_phis_for_split_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[listTheory.EVERY_MAP] >>
  pure_rewrite_tac[listTheory.EVERY_MEM] >>
  rpt strip_tac >> rename1 `MEM inst _` >>
  Cases_on `inst.inst_opcode = PHI`
  >- simp[label_positions_ok_def] >> simp[]
QED

Theorem supply_subst_terminator_label_positions:
  EVERY inst_wf bb.bb_instructions /\
  EVERY label_positions_ok bb.bb_instructions /\
  ~MEM new (block_ir_labels bb) ==>
  EVERY label_positions_ok (subst_label_terminator old new bb).bb_instructions
Proof
  rewrite_tac[subst_label_terminator_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >> rename1 `MEM inst _` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  irule supply_subst_label_preserves_label_positions >>
  gvs[irSupplyTheory.block_ir_labels_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

Theorem supply_forwarding_label_positions:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    EVERY label_positions_ok insts
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (v,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def, label_positions_ok_def,
      stackPlanTypesTheory.is_label_operand_def] >> metis_tac[]
QED

Theorem supply_split_label_positions:
  build_split_block_supply s pred target = (split,repls,s') ==>
  EVERY label_positions_ok split.bb_instructions
Proof
  rpt strip_tac >> Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lbl,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ = (rs,is,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  gvs[build_split_block_supply_def, label_positions_ok_def] >>
  metis_tac[supply_forwarding_label_positions]
QED

Theorem insert_split_supply_label_positions_ok:
  ir_supply_covers_fn s fn /\
  fn_inst_wf fn /\ EVERY label_positions_ok (fn_insts fn) /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  insert_split_supply s fn pred target = (fn',s') ==>
  EVERY label_positions_ok (fn_insts fn')
Proof
  rpt strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==> EVERY inst_wf bb.bb_instructions` by
    (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!bb. MEM bb fn.fn_blocks ==> EVERY label_positions_ok bb.bb_instructions` by
    (qpat_x_assum `EVERY label_positions_ok _` mp_tac >>
     rewrite_tac[fn_insts_def, ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
     simp[listTheory.EVERY_MEM]) >>
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  rename1 `build_split_block_supply s pred target = (split,repls,s1)` >>
  `~MEM split.bb_label s.irs_used_labels` by
    (qpat_x_assum `build_split_block_supply _ _ _ = _` mp_tac >>
     simp[build_split_block_supply_def] >>
     Cases_on `fresh_ir_label s` >>
     rename1 `fresh_ir_label s = (lbl,s0)` >>
     drule irSupplyTheory.fresh_ir_label_contract >> strip_tac >>
     Cases_on `build_forwarding_assigns_supply s0
       (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
     PairCases_on `r` >> Cases_on `fresh_inst_id r1` >>
     simp[] >> strip_tac >> gvs[]) >>
  `~MEM split.bb_label (block_ir_labels pred)` by
    (gvs[ir_supply_covers_fn_def, list_subset_def, irSupplyTheory.fn_ir_labels_def,
         listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[]) >>
  `EVERY label_positions_ok split.bb_instructions` by
    metis_tac[supply_split_label_positions] >>
  `EVERY label_positions_ok
    (subst_label_terminator target.bb_label split.bb_label pred).bb_instructions` by
    metis_tac[supply_subst_terminator_label_positions] >>
  `!bb. MEM bb fn'.fn_blocks ==> EVERY label_positions_ok bb.bb_instructions` suffices_by
    (rewrite_tac[fn_insts_def, ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
     simp[listTheory.EVERY_MEM]) >>
  gvs[insert_split_supply_def, listTheory.MEM_APPEND] >>
  rpt strip_tac >> gvs[] >> qpat_x_assum `MEM bb _` mp_tac >>
  qid_spec_tac `bb` >> ho_match_mp_tac supply_replace_block_property >>
  conj_tac
  >- (ho_match_mp_tac supply_replace_block_property >> simp[]) >>
  irule supply_update_phis_label_positions >>
  Cases_on `pred.bb_label = target.bb_label` >> simp[]
QED

(* Reverse successful PHI entry uses the same fixed-snapshot operand equality. *)
Theorem supply_eval_phis_agree_reverse:
  LIST_REL (\i j. i.inst_opcode = j.inst_opcode /\
    (i.inst_opcode = PHI ==> eval_one_phi st i = eval_one_phi st' j)) insts insts' /\
  supply_state_agree fn st st' /\ eval_phis st' insts' = OK out' ==>
  ?out. eval_phis st insts = OK out /\ supply_state_agree fn out out'
Proof
  strip_tac >>
  `LIST_REL (\j i. j.inst_opcode = i.inst_opcode /\
    (j.inst_opcode = PHI ==> eval_one_phi st' j = eval_one_phi st i)) insts' insts` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     map_every qid_spec_tac [`insts'`, `insts`] >>
     Induct >> Cases >> simp[] >> metis_tac[]) >>
  `supply_state_agree fn st' st` by metis_tac[supply_state_agree_sym] >>
  drule_all supply_eval_phis_agree >> strip_tac >>
  metis_tac[supply_state_agree_sym]
QED

Theorem supply_eval_phis_split_reverse:
  supply_state_agree fn st st' /\
  st.vs_prev_bb = SOME pred /\ st'.vs_prev_bb = SOME split /\
  (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    resolve_phi split inst.inst_operands = NONE /\
    (!op. resolve_phi pred inst.inst_operands = SOME op ==>
      eval_operand
        (case op of Var v =>
          (case ALOOKUP repls v of NONE => Var v | SOME w => Var w)
         | x => x) st' = eval_operand op st)) /\
  eval_phis st' (update_phis_for_split pred split repls bb).bb_instructions = OK out' ==>
  ?out. eval_phis st bb.bb_instructions = OK out /\ supply_state_agree fn out out'
Proof
  strip_tac >> irule supply_eval_phis_agree_reverse >>
  qexistsl_tac [`(update_phis_for_split pred split repls bb).bb_instructions`, `st'`] >>
  simp[] >> simp[update_phis_for_split_def, listTheory.EVERY2_MAP] >>
  irule listTheory.EVERY2_refl >> rpt strip_tac >>
  rename1 `MEM inst bb.bb_instructions` >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  irule EQ_SYM >> irule supply_eval_one_phi_split >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem supply_eval_phis_forwarded_reverse:
  supply_state_agree fn st st' /\
  st.vs_prev_bb = SOME pred /\ st'.vs_prev_bb = SOME split /\
  (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    resolve_phi split inst.inst_operands = NONE /\
    (!v. MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn))) /\
  (!src dst. ALOOKUP repls src = SOME dst ==>
    lookup_var dst st' = lookup_var src st) /\
  eval_phis st' (update_phis_for_split pred split repls bb).bb_instructions = OK out' ==>
  ?out. eval_phis st bb.bb_instructions = OK out /\ supply_state_agree fn out out'
Proof
  strip_tac >> irule supply_eval_phis_split_reverse >> simp[] >>
  qexistsl_tac [`repls`, `split`, `st'`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!inst. MEM inst _ /\ _ ==> _` drule >>
  simp[] >> strip_tac >> simp[] >> rpt strip_tac >>
  irule supply_eval_operand_replacement >> simp[] >>
  irule EQ_SYM >> irule supply_eval_operand_agree >> simp[] >>
  metis_tac[execEquivParamBaseTheory.resolve_phi_MEM]
QED

Theorem supply_eval_phis_other_reverse:
  supply_state_agree fn st st' /\
  st.vs_prev_bb = SOME prev /\ st'.vs_prev_bb = SOME prev /\
  prev <> pred /\ prev <> split /\
  (!inst op. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
     resolve_phi prev inst.inst_operands = SOME op ==>
     eval_operand op st' = eval_operand op st) /\
  eval_phis st' (update_phis_for_split pred split repls bb).bb_instructions = OK out' ==>
  ?out. eval_phis st bb.bb_instructions = OK out /\ supply_state_agree fn out out'
Proof
  strip_tac >> irule supply_eval_phis_agree_reverse >>
  qexistsl_tac [`(update_phis_for_split pred split repls bb).bb_instructions`, `st'`] >>
  simp[] >> simp[update_phis_for_split_def, listTheory.EVERY2_MAP] >>
  irule listTheory.EVERY2_refl >> rpt strip_tac >>
  rename1 `MEM inst bb.bb_instructions` >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  irule EQ_SYM >> irule supply_eval_one_phi_other >> simp[] >> metis_tac[]
QED

(* After PHI entry, the image differs only at redirected terminators. *)
Theorem supply_block_image_body_index:
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> PHI ==>
  EL i (supply_block_image pred target split repls bb).bb_instructions =
    if bb.bb_label = pred.bb_label /\
       is_terminator (EL i bb.bb_instructions).inst_opcode then
      subst_label_inst target.bb_label split.bb_label (EL i bb.bb_instructions)
    else EL i bb.bb_instructions
Proof
  strip_tac >>
  simp[supply_block_image_def, update_phis_for_split_def,
       subst_label_terminator_def, listTheory.EL_MAP, subst_label_inst_def] >>
  rpt IF_CASES_TAC >> gvs[listTheory.EL_MAP]
QED

Theorem supply_eval_phis_subst_terminator:
  eval_phis st (subst_label_terminator old new bb).bb_instructions =
  eval_phis st bb.bb_instructions
Proof
  simp[subst_label_terminator_def] >>
  qspec_tac (`bb.bb_instructions`, `insts`) >> Induct_on `insts` >> simp[] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  Cases_on `is_terminator h.inst_opcode` >>
  gvs[venomExecSemanticsTheory.eval_phis_def, subst_label_inst_def,
      venomInstTheory.is_terminator_def]
QED

Theorem supply_eval_phis_update_subst_terminator:
  eval_phis st (update_phis_for_split pred split repls
    (subst_label_terminator old new bb)).bb_instructions =
  eval_phis st (update_phis_for_split pred split repls bb).bb_instructions
Proof
  simp[update_phis_for_split_def, subst_label_terminator_def] >>
  qspec_tac (`bb.bb_instructions`, `insts`) >> Induct_on `insts` >> simp[] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  Cases_on `is_terminator h.inst_opcode` >>
  gvs[venomExecSemanticsTheory.eval_phis_def, subst_label_inst_def,
      venomInstTheory.is_terminator_def]
QED

Theorem supply_eval_phis_block_image:
  eval_phis st (supply_block_image pred target split repls bb).bb_instructions =
  if bb.bb_label = target.bb_label then
    eval_phis st (update_phis_for_split pred.bb_label split.bb_label repls bb).bb_instructions
  else eval_phis st bb.bb_instructions
Proof
  simp[supply_block_image_def] >> rpt IF_CASES_TAC >>
  simp[supply_eval_phis_subst_terminator,
       supply_eval_phis_update_subst_terminator]
QED

Theorem supply_block_image_step_body:
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_inst_idx = st'.vs_inst_idx /\
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  ~is_terminator (EL i bb.bb_instructions).inst_opcode ==>
  lift_result
    (\s t. supply_state_agree fn s t /\
           s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx)
    (supply_state_agree fn) (supply_state_agree fn)
    (step_inst fuel ctx (EL i bb.bb_instructions) st)
    (step_inst fuel ctx
      (EL i (supply_block_image pred target split repls bb).bb_instructions) st')
Proof
  strip_tac >> simp[supply_block_image_body_index] >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
       MEM v (irSupply$fn_ir_vars fn)` by
    (rpt strip_tac >> irule supply_operand_in_fn >>
     qexistsl_tac [`bb`, `EL i bb.bb_instructions`] >>
     simp[listTheory.EL_MEM]) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = INVOKE`
  >- (irule supply_step_invoke >> simp[]) >>
  irule supply_step_nonterm >> simp[]
QED

Theorem supply_resolve_phi_label_mem:
  !lbl ops op. resolve_phi lbl ops = SOME op ==> MEM (Label lbl) ops
Proof
  recInduct venomExecSemanticsTheory.resolve_phi_ind >>
  simp[venomExecSemanticsTheory.resolve_phi_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem supply_split_resolve_phi_fresh:
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
  resolve_phi split.bb_label inst.inst_operands = NONE
Proof
  strip_tac >>
  `~MEM split.bb_label s.irs_used_labels` by
    metis_tac[build_split_block_supply_label_fresh] >>
  Cases_on `resolve_phi split.bb_label inst.inst_operands` >> simp[] >>
  drule supply_resolve_phi_label_mem >> strip_tac >>
  `MEM split.bb_label (irSupply$fn_ir_labels fn)` by
    (simp[irSupplyTheory.fn_ir_labels_def, irSupplyTheory.block_ir_labels_def,
          irSupplyTheory.inst_ir_labels_def, irSupplyTheory.MEM_operand_ir_labels,
          listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM]
QED

(* Bridge forwarding execution to the old-name relation, retaining the
   pre-PHI source snapshot rather than requiring identical control fields. *)
Theorem supply_split_exec_agree:
  MEM target fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_state_agree fn st st' /\
  EVERY (\v. MEM v s.irs_used_vars /\ IS_SOME (lookup_var v st))
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions)) /\
  ~st'.vs_halted /\ st'.vs_current_bb = split.bb_label ==>
  ?mid. exec_block fuel ctx split (st' with vs_inst_idx := 0) = OK mid /\
    supply_state_agree fn st mid /\
    (!src dst. ALOOKUP repls src = SOME dst ==>
       lookup_var dst mid = lookup_var src st) /\
    mid.vs_current_bb = target.bb_label /\
    mid.vs_prev_bb = SOME split.bb_label /\ mid.vs_inst_idx = 0
Proof
  strip_tac >>
  `!v. MEM v (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions)) ==>
       MEM v (irSupply$fn_ir_vars fn)` by
    (simp[] >> rpt strip_tac >> drule MEM_phi_vars_needing_forward_block_vars >>
     strip_tac >>
     gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
     simp[irSupplyTheory.fn_ir_vars_def, irSupplyTheory.block_ir_vars_def,
          listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `EVERY (\v. MEM v s.irs_used_vars /\ IS_SOME (lookup_var v st'))
     (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     rewrite_tac[listTheory.EVERY_MEM] >> rpt strip_tac >> simp[] >>
     metis_tac[supply_state_agree_lookup]) >>
  drule_all supply_split_exec >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexists_tac `out` >> simp[] >> conj_tac
  >- (gvs[supply_state_agree_def, ir_supply_covers_fn_def,
          list_subset_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  rpt strip_tac >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  metis_tac[supply_state_agree_lookup]
QED

(* Both entry directions share one forwarding execution and one pre-PHI
   snapshot. The block image handles pred = target without a side condition. *)
Theorem supply_split_entry_phis:
  MEM target fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_state_agree fn st st' /\ st.vs_prev_bb = SOME pred.bb_label /\
  EVERY (\v. MEM v s.irs_used_vars /\ IS_SOME (lookup_var v st))
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions)) /\
  ~st'.vs_halted /\ st'.vs_current_bb = split.bb_label ==>
  ?mid. exec_block fuel ctx split (st' with vs_inst_idx := 0) = OK mid /\
    supply_state_agree fn st mid /\
    mid.vs_current_bb = target.bb_label /\
    mid.vs_prev_bb = SOME split.bb_label /\ mid.vs_inst_idx = 0 /\
    (!out. eval_phis st target.bb_instructions = OK out ==>
      ?out'. eval_phis mid
        (supply_block_image pred target split repls target).bb_instructions = OK out' /\
        supply_state_agree fn out out') /\
    (!out'. eval_phis mid
        (supply_block_image pred target split repls target).bb_instructions = OK out' ==>
      ?out. eval_phis st target.bb_instructions = OK out /\
        supply_state_agree fn out out')
Proof
  strip_tac >> drule_all supply_split_exec_agree >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  `!inst. MEM inst target.bb_instructions /\ inst.inst_opcode = PHI ==>
     resolve_phi split.bb_label inst.inst_operands = NONE /\
     (!v. MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn))` by
    (rpt strip_tac
     >- (irule supply_split_resolve_phi_fresh >> metis_tac[]) >>
     irule supply_operand_in_fn >> metis_tac[]) >>
  qexists_tac `mid` >> simp[supply_eval_phis_block_image] >> conj_tac
  >- (rpt strip_tac >> irule supply_eval_phis_forwarded >>
      simp[] >> conj_tac >- metis_tac[] >>
      qexists_tac `st` >> simp[]) >>
  rpt strip_tac >> irule supply_eval_phis_forwarded_reverse >>
  qexistsl_tac [`pred.bb_label`, `repls`, `split.bb_label`, `mid`] >>
  simp[] >> metis_tac[]
QED

Theorem supply_mcopy_prev_bb:
  mcopy dst src sz (st with vs_prev_bb := p) =
  mcopy dst src sz st with vs_prev_bb := p
Proof
  simp[venomExecSemanticsTheory.mcopy_def, venomStateTheory.write_memory_with_expansion_def,
       venomStateTheory.venom_state_component_equality]
QED

Theorem supply_pack_dret_dynamic_prev_bb:
  !pairs cursor st p.
    pack_dret_dynamic cursor pairs (st with vs_prev_bb := p) =
      case pack_dret_dynamic cursor pairs st of
        (ptrs,final,out) => (ptrs,final,out with vs_prev_bb := p)
Proof
  Induct >> simp[venomExecSemanticsTheory.pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[venomExecSemanticsTheory.pack_dret_dynamic_def, supply_mcopy_prev_bb] >>
  Cases_on `pack_dret_dynamic (cursor + n2w (ceil32 (w2n h1))) pairs
    (mcopy (w2n cursor) (w2n h0) (w2n h1) st)` >> PairCases_on `r` >> simp[]
QED

Theorem supply_nonjump_terminator_prev_bb:
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> JMP /\
  inst.inst_opcode <> JNZ /\ inst.inst_opcode <> DJMP ==>
  step_inst_base inst (st with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s. s with vs_prev_bb := p) (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
  simp[supply_eval_operand_prev_bb, supply_eval_operands_prev_bb,
       supply_pack_dret_dynamic_prev_bb,
       venomStateTheory.halt_state_def, venomStateTheory.revert_state_def,
       venomStateTheory.set_returndata_def, exec_result_map_prev_bb_def]
  >- (Cases_on `eval_operands inst.inst_operands st` >>
      simp[exec_result_map_prev_bb_def] >> Cases_on `x` >>
      simp[exec_result_map_prev_bb_def])
  >- (namedCases_on `inst.inst_operands` ["", "off rest"]
      >- simp[exec_result_map_prev_bb_def] >>
      namedCases_on `rest` ["", "sz tail"]
      >- simp[exec_result_map_prev_bb_def] >>
      Cases_on `tail` >> simp[exec_result_map_prev_bb_def] >>
      Cases_on `eval_operand off st` >> simp[exec_result_map_prev_bb_def] >>
      Cases_on `eval_operand sz st` >>
      simp[exec_result_map_prev_bb_def, venomStateTheory.venom_state_component_equality])
  >- (namedCases_on `inst.inst_operands` ["", "off rest"]
      >- simp[exec_result_map_prev_bb_def] >>
      namedCases_on `rest` ["", "sz tail"]
      >- simp[exec_result_map_prev_bb_def] >>
      Cases_on `tail` >> simp[exec_result_map_prev_bb_def] >>
      Cases_on `eval_operand off st` >> simp[exec_result_map_prev_bb_def] >>
      Cases_on `eval_operand sz st` >>
      simp[exec_result_map_prev_bb_def, venomStateTheory.venom_state_component_equality])
  >- (Cases_on `inst.inst_outputs = []` >> simp[exec_result_map_prev_bb_def] >>
      Cases_on `parse_dret_shape inst` >> simp[exec_result_map_prev_bb_def] >>
      PairCases_on `x` >> simp[] >>
      Cases_on `eval_operands inst.inst_operands st` >>
      simp[exec_result_map_prev_bb_def] >>
      rename1 `eval_operands _ _ = SOME vals` >>
      Cases_on `pair_dret_words (TAKE (2 * x1) (DROP (x0 + 1) vals))` >>
      simp[exec_result_map_prev_bb_def] >>
      rename1 `pair_dret_words _ = SOME pairs` >>
      Cases_on `pack_dret_dynamic st.vs_call_entry_fmp pairs st` >>
      PairCases_on `r` >>
      simp[exec_result_map_prev_bb_def, venomStateTheory.venom_state_component_equality])
  >- (Cases_on `eval_operands inst.inst_operands st` >>
      simp[exec_result_map_prev_bb_def] >> Cases_on `x` >>
      simp[exec_result_map_prev_bb_def])
  >> IF_CASES_TAC
  >- simp[exec_result_map_prev_bb_def,
          venomStateTheory.venom_state_component_equality]
  >> namedCases_on `inst.inst_operands` ["", "addr rest"]
  >- simp[exec_result_map_prev_bb_def] >>
  Cases_on `rest` >> simp[exec_result_map_prev_bb_def] >>
  Cases_on `eval_operand addr st` >>
  simp[exec_result_map_prev_bb_def, venomStateTheory.venom_state_component_equality]
QED

Theorem supply_nonjump_terminator_not_ok:
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> JMP /\
  inst.inst_opcode <> JNZ /\ inst.inst_opcode <> DJMP ==>
  step_inst_base inst st <> OK out
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac >> pairarg_tac >> gvs[]
QED

Theorem supply_step_terminator:
  supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_inst_idx = st'.vs_inst_idx /\
  is_terminator inst.inst_opcode /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn)) ==>
  lift_result
    (\u v. supply_state_agree fn u v /\
       (~u.vs_halted ==> u.vs_current_bb = v.vs_current_bb /\
          u.vs_inst_idx = v.vs_inst_idx /\ u.vs_prev_bb = v.vs_prev_bb))
    (supply_state_agree fn) (supply_state_agree fn)
    (step_inst fuel ctx inst st) (step_inst fuel ctx inst st')
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `supply_state_agree fn st (st' with vs_prev_bb := st.vs_prev_bb)` by
    simp[supply_state_agree_prev_bb] >>
  drule supply_step_inst >>
  disch_then (qspecl_then [`inst`,`fuel`,`ctx`] mp_tac) >>
  simp[venomExecSemanticsTheory.step_inst_def] >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/ inst.inst_opcode = DJMP`
  >- (`step_inst_base inst (st' with vs_prev_bb := st.vs_prev_bb) =
        step_inst_base inst st'` by
        (irule step_inst_base_jump_prev_bb >> simp[]) >> simp[] >>
      Cases_on `step_inst_base inst st` >> Cases_on `step_inst_base inst st'` >>
      simp[stateEquivTheory.lift_result_def, stateEquivTheory.state_equiv_def,
           GSYM supply_state_agree_execution_equiv]) >>
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\ inst.inst_opcode <> DJMP` by metis_tac[] >>
  simp[supply_nonjump_terminator_prev_bb] >>
  Cases_on `step_inst_base inst st`
  >- metis_tac[supply_nonjump_terminator_not_ok] >>
  Cases_on `step_inst_base inst st'` >>
  simp[exec_result_map_prev_bb_def, stateEquivTheory.lift_result_def,
       GSYM supply_state_agree_execution_equiv, supply_state_agree_prev_bb]
QED

Theorem supply_state_agree_current_bb:
  supply_state_agree fn u (v with vs_current_bb := l) <=>
  supply_state_agree fn u v
Proof
  simp[supply_state_agree_def, stateFrameTheory.execution_frame_def,
       venomStateTheory.lookup_var_def]
QED

Theorem supply_block_image_step_terminator:
  MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  inst = EL i bb.bb_instructions /\ inst_wf inst /\ label_positions_ok inst /\
  is_terminator inst.inst_opcode /\ supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_inst_idx = st'.vs_inst_idx ==>
  lift_result
    (\u v. supply_state_agree fn u v /\
      (~u.vs_halted ==>
        v.vs_current_bb =
          (if bb.bb_label = pred.bb_label /\
              (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) /\
              u.vs_current_bb = target.bb_label
           then split.bb_label else u.vs_current_bb) /\
        v.vs_inst_idx = u.vs_inst_idx /\ v.vs_prev_bb = u.vs_prev_bb))
    (supply_state_agree fn) (supply_state_agree fn)
    (step_inst fuel ctx inst st)
    (step_inst fuel ctx
      (EL i (supply_block_image pred target split repls bb).bb_instructions) st')
Proof
  strip_tac >>
  `inst.inst_opcode <> PHI` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `!v. MEM (Var v) inst.inst_operands ==> MEM v (irSupply$fn_ir_vars fn)` by
    (rpt strip_tac >> irule supply_operand_in_fn >>
     qexistsl_tac [`bb`, `inst`] >> simp[listTheory.EL_MEM]) >>
  `EL i (supply_block_image pred target split repls bb).bb_instructions =
     if bb.bb_label = pred.bb_label then
       subst_label_inst target.bb_label split.bb_label inst else inst` by
    (drule supply_block_image_body_index >> simp[] >> metis_tac[]) >>
  `step_inst fuel ctx (subst_label_inst target.bb_label split.bb_label inst) st' =
    (if inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ then
       case step_inst fuel ctx inst st' of
         OK v => OK (if v.vs_current_bb = target.bb_label
                     then v with vs_current_bb := split.bb_label else v)
       | Halt v => Halt v | Abort a v => Abort a v
       | IntRet r v => IntRet r v | Error e => Error e
     else step_inst fuel ctx inst st')` by
    (irule supply_subst_label_terminator_step >> simp[]) >>
  drule_all supply_step_terminator >>
  disch_then (qspecl_then [`fuel`,`ctx`] assume_tac) >>
  Cases_on `bb.bb_label = pred.bb_label` >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ` >>
  Cases_on `step_inst fuel ctx inst st` >>
  Cases_on `step_inst fuel ctx inst st'` >>
  gvs[stateEquivTheory.lift_result_def] >>
  rpt IF_CASES_TAC >> gvs[stateEquivTheory.lift_result_def,
    supply_state_agree_current_bb] >> metis_tac[]
QED

Theorem supply_other_entry_phis:
  MEM bb fn.fn_blocks /\ supply_state_agree fn st st' /\
  st.vs_prev_bb = st'.vs_prev_bb /\
  (bb.bb_label = target.bb_label ==>
    st.vs_prev_bb <> SOME pred.bb_label /\ st.vs_prev_bb <> SOME split.bb_label) /\
  eval_phis st bb.bb_instructions = OK out ==>
  ?out'. eval_phis st'
    (supply_block_image pred target split repls bb).bb_instructions = OK out' /\
    supply_state_agree fn out out'
Proof
  strip_tac >> simp[supply_eval_phis_block_image] >>
  `!prev inst op. MEM inst bb.bb_instructions /\
     resolve_phi prev inst.inst_operands = SOME op ==>
     eval_operand op st' = eval_operand op st` by
    (rpt strip_tac >> irule EQ_SYM >> irule supply_eval_operand_agree >>
     qexists_tac `fn` >> simp[] >> rpt strip_tac >> irule supply_operand_in_fn >>
     qexistsl_tac [`bb`, `inst`] >> simp[] >>
     metis_tac[execEquivParamBaseTheory.resolve_phi_MEM]) >>
  Cases_on `bb.bb_label = target.bb_label` >> simp[]
  >- (Cases_on `st.vs_prev_bb`
      >- (irule supply_eval_phis_agree >>
          qexistsl_tac [`bb.bb_instructions`, `st`] >>
          simp[update_phis_for_split_def, listTheory.EVERY2_MAP] >>
          irule listTheory.EVERY2_refl >> rpt strip_tac >>
          Cases_on `x.inst_opcode = PHI` >> simp[] >>
          Cases_on `x.inst_outputs` >>
          gvs[venomExecSemanticsTheory.eval_one_phi_def]) >>
      irule supply_eval_phis_other >> qexistsl_tac [`x`, `st`] >> simp[] >> metis_tac[]) >>
  irule supply_eval_phis_agree >>
  qexistsl_tac [`bb.bb_instructions`, `st`] >> simp[] >>
  irule listTheory.EVERY2_refl >> rpt strip_tac >> simp[] >>
  Cases_on `x.inst_outputs` >> simp[venomExecSemanticsTheory.eval_one_phi_def] >>
  Cases_on `t` >> simp[venomExecSemanticsTheory.eval_one_phi_def] >>
  namedCases_on `st.vs_prev_bb` ["", "prev"]
  >- (qpat_x_assum `NONE = st'.vs_prev_bb`
        (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_x_assum `SOME prev = st'.vs_prev_bb`
    (fn th => rewrite_tac[GSYM th]) >>
  Cases_on `resolve_phi prev x.inst_operands` >> simp[] >>
  `eval_operand x' st' = eval_operand x' st` by metis_tac[] >> simp[]
QED

Theorem supply_other_entry_phis_reverse:
  MEM bb fn.fn_blocks /\ supply_state_agree fn st st' /\
  st.vs_prev_bb = st'.vs_prev_bb /\
  (bb.bb_label = target.bb_label ==>
    st.vs_prev_bb <> SOME pred.bb_label /\ st.vs_prev_bb <> SOME split.bb_label) /\
  eval_phis st'
    (supply_block_image pred target split repls bb).bb_instructions = OK out' ==>
  ?out. eval_phis st bb.bb_instructions = OK out /\ supply_state_agree fn out out'
Proof
  strip_tac >>
  `!prev inst op. MEM inst bb.bb_instructions /\
     resolve_phi prev inst.inst_operands = SOME op ==>
     eval_operand op st' = eval_operand op st` by
    (rpt strip_tac >> irule EQ_SYM >> irule supply_eval_operand_agree >>
     qexists_tac `fn` >> simp[] >> rpt strip_tac >> irule supply_operand_in_fn >>
     qexistsl_tac [`bb`, `inst`] >> simp[] >>
     metis_tac[execEquivParamBaseTheory.resolve_phi_MEM]) >>
  Cases_on `bb.bb_label = target.bb_label`
  >- (qpat_x_assum `eval_phis st' _ = OK out'` mp_tac >>
      simp[supply_eval_phis_block_image] >> strip_tac >>
      Cases_on `st.vs_prev_bb`
      >- (irule supply_eval_phis_agree_reverse >>
          qexistsl_tac [`(update_phis_for_split pred.bb_label split.bb_label repls bb).bb_instructions`, `st'`] >>
          gvs[update_phis_for_split_def, listTheory.EVERY2_MAP] >>
          irule listTheory.EVERY2_refl >> rpt strip_tac >>
          Cases_on `x.inst_opcode = PHI` >> simp[] >>
          Cases_on `x.inst_outputs` >>
          gvs[venomExecSemanticsTheory.eval_one_phi_def]) >>
      irule supply_eval_phis_other_reverse >>
      qexistsl_tac [`pred.bb_label`, `x`, `repls`, `split.bb_label`, `st'`] >>
      simp[] >> metis_tac[]) >>
  `eval_phis st' bb.bb_instructions = OK out'` by
    metis_tac[supply_eval_phis_block_image] >>
  `supply_state_agree fn st' st` by metis_tac[supply_state_agree_sym] >>
  `?out. eval_phis st (supply_block_image pred target split repls bb).bb_instructions = OK out /\
     supply_state_agree fn out' out` by
    (irule supply_other_entry_phis >> simp[] >> qexists_tac `st'` >> simp[]) >>
  metis_tac[supply_state_agree_sym, supply_eval_phis_block_image]
QED

(* Control exposed by a whole original-block body. *)
Definition supply_body_exit_def:
  supply_body_exit fn pred target split bb u v <=>
    supply_state_agree fn u v /\
    (~u.vs_halted ==>
      v.vs_inst_idx = u.vs_inst_idx /\ v.vs_prev_bb = u.vs_prev_bb /\
      v.vs_current_bb =
        (if bb.bb_label = pred.bb_label /\
            ((LAST bb.bb_instructions).inst_opcode = JMP \/
             (LAST bb.bb_instructions).inst_opcode = JNZ) /\
            u.vs_current_bb = target.bb_label
         then split.bb_label else u.vs_current_bb))
End

Theorem supply_phi_prefix_initial_segment[local]:
  !insts i. i < LENGTH insts /\
    (!j. j <= i ==> (EL j insts).inst_opcode = PHI) ==>
    i < phi_prefix_length insts
Proof
  Induct_on `insts` >> simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  rpt strip_tac >>
  `h.inst_opcode = PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  Cases_on `i` >> gvs[] >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
QED

Theorem supply_body_non_phi:
  bb_well_formed bb /\ phi_prefix_length bb.bb_instructions <= i /\
  i < LENGTH bb.bb_instructions ==> (EL i bb.bb_instructions).inst_opcode <> PHI
Proof
  strip_tac >> strip_tac >>
  `!j. j <= i ==> (EL j bb.bb_instructions).inst_opcode = PHI` by
    (rpt strip_tac >> Cases_on `j = i` >> gvs[bb_well_formed_def] >>
     metis_tac[arithmeticTheory.LESS_OR_EQ]) >>
  metis_tac[supply_phi_prefix_initial_segment, arithmeticTheory.NOT_LESS]
QED

Theorem supply_state_agree_halted:
  supply_state_agree fn u v ==> u.vs_halted = v.vs_halted
Proof
  simp[supply_state_agree_def] >> strip_tac >>
  qpat_x_assum `execution_frame _ = execution_frame _`
    (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >>
  simp[stateFrameTheory.execution_frame_def]
QED

Theorem supply_state_agree_inst_idx:
  supply_state_agree fn (u with vs_inst_idx := i) (v with vs_inst_idx := j) <=>
  supply_state_agree fn u v
Proof
  simp[supply_state_agree_def, stateFrameTheory.execution_frame_def,
       venomStateTheory.lookup_var_def]
QED

Theorem supply_block_image_exec_body:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\ MEM bb fn.fn_blocks /\
  supply_state_agree fn st st' /\
  st.vs_current_bb = st'.vs_current_bb /\ st.vs_inst_idx = st'.vs_inst_idx /\
  phi_prefix_length bb.bb_instructions <= st.vs_inst_idx ==>
  lift_result (supply_body_exit fn pred target split bb)
    (supply_state_agree fn) (supply_state_agree fn)
    (exec_block fuel ctx bb st)
    (exec_block fuel ctx (supply_block_image pred target split repls bb) st')
Proof
  qid_spec_tac `st'` >>
  measureInduct_on `LENGTH bb.bb_instructions - st.vs_inst_idx` >>
  rpt strip_tac >>
  `bb_well_formed bb` by gvs[wf_function_def, listTheory.EVERY_MEM] >>
  Cases_on `st.vs_inst_idx < LENGTH bb.bb_instructions`
  >- (`(EL st.vs_inst_idx bb.bb_instructions).inst_opcode <> PHI` by
        metis_tac[supply_body_non_phi] >>
      `inst_wf (EL st.vs_inst_idx bb.bb_instructions) /\
       label_positions_ok (EL st.vs_inst_idx bb.bb_instructions)` by
        (qpat_x_assum `EVERY label_positions_ok _` mp_tac >>
         rewrite_tac[fn_insts_def, ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
         gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >>
         metis_tac[listTheory.EL_MEM]) >>
      Cases_on `is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode`
      >- (`EL st.vs_inst_idx bb.bb_instructions = LAST bb.bb_instructions` by
            (gvs[bb_well_formed_def, listTheory.LAST_EL] >> metis_tac[]) >>
          mp_tac (Q.INST [`i` |-> `st.vs_inst_idx`,
            `inst` |-> `EL st.vs_inst_idx bb.bb_instructions`]
            supply_block_image_step_terminator) >>
          simp[] >>
          strip_tac >>
          once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
          simp[get_instruction_def, supply_block_image_length,
               supply_block_image_index] >>
          Cases_on `step_inst fuel ctx (LAST bb.bb_instructions) st` >>
          Cases_on `step_inst fuel ctx
            (EL st'.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions) st'` >>
          gvs[stateEquivTheory.lift_result_def, supply_body_exit_def] >>
          imp_res_tac supply_state_agree_halted >>
          rpt IF_CASES_TAC >> gvs[stateEquivTheory.lift_result_def, supply_body_exit_def]) >>
      mp_tac (Q.INST [`i` |-> `st.vs_inst_idx`] supply_block_image_step_body) >>
      simp[] >> strip_tac >>
      once_rewrite_tac[venomExecSemanticsTheory.exec_block_def] >>
      simp[get_instruction_def, supply_block_image_length, supply_block_image_index] >>
      Cases_on `step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st` >>
      Cases_on `step_inst fuel ctx
        (EL st'.vs_inst_idx (supply_block_image pred target split repls bb).bb_instructions) st'` >>
      gvs[stateEquivTheory.lift_result_def] >>
      first_x_assum irule >>
      simp[supply_state_agree_inst_idx] >> decide_tac) >>
  simp[Once venomExecSemanticsTheory.exec_block_def,
       get_instruction_def] >>
  simp[Once venomExecSemanticsTheory.exec_block_def,
       get_instruction_def,
       supply_block_image_length, stateEquivTheory.lift_result_def]
QED

(* Entry compatibility abstracts the two possible predecessor-label phases. *)
Definition supply_ready_def:
  supply_ready fn pred target split repls u v <=>
    supply_entry_defined fn u /\ supply_state_agree fn u v /\
    ~u.vs_halted /\ ~v.vs_halted /\ u.vs_current_bb = v.vs_current_bb /\
    (!bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb ==>
      (!out. eval_phis u bb.bb_instructions = OK out ==>
        ?out'. eval_phis v (supply_block_image pred target split repls bb).bb_instructions = OK out' /\
          supply_state_agree fn out out') /\
      (!out'. eval_phis v (supply_block_image pred target split repls bb).bb_instructions = OK out' ==>
        ?out. eval_phis u bb.bb_instructions = OK out /\ supply_state_agree fn out out'))
End

Definition supply_pending_def:
  supply_pending fn s pred target split u v <=>
    supply_entry_defined fn u /\ supply_state_agree fn u v /\
    ~u.vs_halted /\ ~v.vs_halted /\
    u.vs_current_bb = target.bb_label /\ v.vs_current_bb = split.bb_label /\
    u.vs_prev_bb = SOME pred.bb_label /\
    EVERY (\x. MEM x s.irs_used_vars /\ IS_SOME (lookup_var x u))
      (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))
End

Theorem supply_ready_other_entry:
  supply_entry_defined fn u /\ supply_state_agree fn u v /\
  ~u.vs_halted /\ ~v.vs_halted /\ u.vs_current_bb = v.vs_current_bb /\
  u.vs_prev_bb = v.vs_prev_bb /\
  (u.vs_current_bb = target.bb_label ==>
    u.vs_prev_bb <> SOME pred.bb_label /\ u.vs_prev_bb <> SOME split.bb_label) ==>
  supply_ready fn pred target split repls u v
Proof
  strip_tac >> simp[supply_ready_def] >> rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = u.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, lookup_block_label] >>
  metis_tac[supply_other_entry_phis, supply_other_entry_phis_reverse]
QED

Theorem supply_ready_entry:
  fn_entry_state fn u ==> supply_ready fn pred target split repls u u
Proof
  strip_tac >> irule supply_ready_other_entry >>
  gvs[o1PassLiftTheory.fn_entry_state_def, supply_entry_defined_entry]
QED

Theorem supply_split_no_phi_entry:
  build_split_block_supply s pred target = (split,repls,s') ==>
  eval_phis u split.bb_instructions = OK u /\
  phi_prefix_length split.bb_instructions = 0
Proof
  strip_tac >>
  Cases_on `fresh_ir_label s` >>
  Cases_on `build_forwarding_assigns_supply r
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  rename1 `build_forwarding_assigns_supply r _ = (rs,rest)` >>
  PairCases_on `rest` >>
  Cases_on `fresh_inst_id rest1` >>
  gvs[build_split_block_supply_def] >>
  drule supply_forwarding_opcodes >> strip_tac >>
  Cases_on `rest0` >>
  gvs[listTheory.EVERY_DEF, venomExecSemanticsTheory.eval_phis_def,
      venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem supply_pending_contract:
  wf_function fn /\ MEM target fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_pending fn s pred target split u v ==>
  ?m. run_block_entry fuel ctx split v = OK m /\
      supply_ready fn pred target split repls u m
Proof
  strip_tac >>
  qpat_x_assum `supply_pending _ _ _ _ _ _ _` mp_tac >>
  simp[supply_pending_def] >> strip_tac >>
  drule_all supply_split_entry_phis >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexists_tac `mid` >>
  `~mid.vs_halted` by metis_tac[supply_state_agree_halted] >>
  drule supply_split_no_phi_entry >>
  disch_then (qspec_then `v` strip_assume_tac) >>
  conj_tac
  >- simp[venomExecSemanticsTheory.run_block_entry_def] >>
  simp[supply_ready_def] >> rpt strip_tac >>
  `bb = target` by
    (`lookup_block target.bb_label fn.fn_blocks = SOME target` by
       (irule venomExecProofsTheory.MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
     gvs[]) >>
  gvs[]
QED

Theorem supply_ready_image_lookup:
  wf_function fn /\ MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  supply_ready fn pred target split repls u v /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb ==>
  lookup_block v.vs_current_bb fn'.fn_blocks =
    SOME (supply_block_image pred target split repls bb)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = u.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, lookup_block_label] >>
  `split.bb_label <> bb.bb_label` by
    (drule_all supply_split_label_not_old >>
     simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `u.vs_current_bb = v.vs_current_bb` by gvs[supply_ready_def] >>
  metis_tac[insert_split_supply_image_lookup]
QED

Theorem supply_pending_split_lookup:
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  supply_pending fn s pred target split u v ==>
  lookup_block v.vs_current_bb fn'.fn_blocks = SOME split
Proof
  strip_tac >>
  `~MEM split.bb_label (fn_labels fn)` by metis_tac[supply_split_label_not_old] >>
  gvs[supply_pending_def, fn_labels_def] >>
  metis_tac[insert_split_supply_split_lookup]
QED

Theorem insert_split_supply_entry_state:
  insert_split_supply s fn pred target = (fn',s') /\ fn_entry_state fn u ==>
  fn_entry_state fn' u
Proof
  strip_tac >>
  `fn.fn_blocks <> []` by
    (Cases_on `fn.fn_blocks` >>
     gvs[o1PassLiftTheory.fn_entry_state_def, fn_entry_label_def, entry_block_def]) >>
  drule_all insert_split_supply_entry >>
  gvs[o1PassLiftTheory.fn_entry_state_def]
QED

Theorem insert_split_supply_name:
  insert_split_supply s fn pred target = (fn',s') ==> fn'.fn_name = fn.fn_name
Proof
  Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
  simp[insert_split_supply_def] >> rpt strip_tac >> gvs[]
QED

Theorem supply_get_successors_no_labels:
  EVERY (\op. ~is_label_operand op) inst.inst_operands ==>
  get_successors inst = []
Proof
  strip_tac >> simp[get_successors_def] >>
  `FILTER IS_SOME (MAP get_label inst.inst_operands) = []` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     SPEC_TAC (``inst.inst_operands``, ``ops:operand list``) >>
     Induct >> simp[] >> Cases_on `h` >>
     simp[stackPlanTypesTheory.is_label_operand_def, venomStateTheory.get_label_def]) >> simp[]
QED

Theorem supply_multi_successor_jump:
  EVERY label_positions_ok bb.bb_instructions /\ 1 < num_succs bb ==>
  (LAST bb.bb_instructions).inst_opcode = JMP \/
  (LAST bb.bb_instructions).inst_opcode = JNZ
Proof
  strip_tac >>
  `bb.bb_instructions <> []` by
    (Cases_on `bb.bb_instructions` >> gvs[num_succs_def, bb_succs_def]) >>
  `label_positions_ok (LAST bb.bb_instructions)` by
    (gvs[listTheory.EVERY_EL, listTheory.LAST_EL] >>
     first_x_assum irule >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  spose_not_then strip_assume_tac >>
  `get_successors (LAST bb.bb_instructions) = []` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     simp[get_successors_def, is_terminator_def] >>
     gvs[label_positions_ok_def] >>
     imp_res_tac supply_get_successors_no_labels >>
     qpat_x_assum `get_successors _ = []` mp_tac >>
     simp[get_successors_def, is_terminator_def]) >>
  gvs[num_succs_def, bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem supply_run_block_entry_control:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = u.vs_current_bb /\ run_block_entry fuel ctx bb u = OK out ==>
  out.vs_prev_bb = SOME bb.bb_label /\ ~out.vs_halted
Proof
  strip_tac >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions` by
    (gvs[wf_function_def, fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (`out.vs_prev_bb = SOME u.vs_current_bb` suffices_by simp[] >>
      irule venomExecProofsTheory.run_block_ok_prev_bb_exact >>
      qexistsl_tac [`bb`, `ctx`, `fuel`] >> simp[] >>
      gvs[bb_well_formed_def] >> rpt strip_tac >>
      `i < LENGTH bb.bb_instructions` by decide_tac >>
      `i = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >> decide_tac) >>
  metis_tac[venomExecProofsTheory.run_block_OK_not_halted]
QED

Theorem supply_phi_prefix_opcodes:
  !xs ys. MAP (\i. i.inst_opcode) xs = MAP (\i. i.inst_opcode) ys ==>
  phi_prefix_length xs = phi_prefix_length ys
Proof
  Induct >> Cases_on `ys` >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem supply_block_image_phi_prefix:
  phi_prefix_length (supply_block_image pred target split repls bb).bb_instructions =
  phi_prefix_length bb.bb_instructions
Proof
  irule supply_phi_prefix_opcodes >> simp[supply_block_image_opcodes]
QED

Theorem supply_ready_run_block_body:
  wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  supply_ready fn pred target split repls u v /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb ==>
  lift_result (supply_body_exit fn pred target split bb)
    (supply_state_agree fn) (supply_state_agree fn)
    (run_block_entry fuel ctx bb u)
    (run_block_entry fuel ctx (supply_block_image pred target split repls bb) v)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  qpat_x_assum `supply_ready _ _ _ _ _ _ _` mp_tac >>
  simp[supply_ready_def] >> strip_tac >>
  qspec_then `u` (qspec_then `bb.bb_instructions` strip_assume_tac)
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs
  >- (`?out'. eval_phis v (supply_block_image pred target split repls bb).bb_instructions = OK out' /\
         supply_state_agree fn s' out'` by metis_tac[] >>
      simp[venomExecSemanticsTheory.run_block_entry_def] >>
      simp[supply_block_image_phi_prefix] >>
      irule supply_block_image_exec_body >>
      simp[supply_state_agree_inst_idx] >>
      metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb]) >>
  `?e'. eval_phis v (supply_block_image pred target split repls bb).bb_instructions = Error e'` by
    (qspec_then `v` (qspec_then `(supply_block_image pred target split repls bb).bb_instructions`
       strip_assume_tac) venomExecSemanticsTheory.eval_phis_ok_or_error_defs
     >- (first_x_assum drule >> simp[]) >> metis_tac[]) >>
  simp[venomExecSemanticsTheory.run_block_entry_def, stateEquivTheory.lift_result_def]
QED

Definition supply_entry_pair_def:
  supply_entry_pair fn s pred target split repls u v <=>
    supply_ready fn pred target split repls u v \/
    supply_pending fn s pred target split u v
End

Theorem supply_forward_sources_ready_exit:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn s fn /\ MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  supply_entry_defined fn u /\ pred.bb_label = u.vs_current_bb /\
  run_block_entry fuel ctx pred u = OK out ==>
  EVERY (\x. MEM x s.irs_used_vars /\ IS_SOME (lookup_var x out))
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))
Proof
  strip_tac >>
  `EVERY (\x. MEM x s.irs_used_vars) (block_ir_vars target)` by
    (gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM,
         irSupplyTheory.fn_ir_vars_def] >> metis_tac[listTheory.MEM_FLAT, listTheory.MEM_MAP]) >>
  drule EVERY_phi_vars_needing_forward_covered >>
  disch_then (qspecl_then [`pred.bb_label`, `pred`] assume_tac) >>
  gvs[listTheory.EVERY_MEM] >> rpt strip_tac >> simp[] >>
  `x IN FDOM out.vs_vars` by
    metis_tac[phi_forward_sources_entry_defined] >>
  simp[venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem supply_body_exit_entry_pair:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_entry_defined fn u /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block_entry fuel ctx bb u = OK m /\
  supply_body_exit fn pred target split bb m n ==>
  supply_entry_pair fn s pred target split repls m n
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = u.vs_current_bb` by
    metis_tac[venomExecProofsTheory.lookup_block_MEM, lookup_block_label] >>
  `supply_entry_defined fn m` by metis_tac[supply_entry_defined_run_block_entry,
    venomExecProofsTheory.run_block_OK_not_halted] >>
  `m.vs_prev_bb = SOME bb.bb_label /\ ~m.vs_halted` by
    metis_tac[supply_run_block_entry_control] >>
  `~n.vs_halted` by metis_tac[supply_body_exit_def, supply_state_agree_halted] >>
  `bb.bb_label = pred.bb_label <=> bb = pred` by
    metis_tac[venomExecProofsTheory.same_label_same_block] >>
  `split.bb_label <> bb.bb_label` by
    (drule_all supply_split_label_not_old >>
     simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `EVERY label_positions_ok pred.bb_instructions` by
    (qpat_x_assum `EVERY label_positions_ok _` mp_tac >>
     rewrite_tac[fn_insts_def, ctxLookupAgreeHelpersTheory.fn_insts_EVERY_block] >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `bb = pred ==> ((LAST bb.bb_instructions).inst_opcode = JMP \/
    (LAST bb.bb_instructions).inst_opcode = JNZ)` by
    metis_tac[supply_multi_successor_jump] >>
  Cases_on `bb = pred /\ m.vs_current_bb = target.bb_label`
  >- (gvs[supply_entry_pair_def] >> disj2_tac >>
      simp[supply_pending_def] >>
      gvs[supply_body_exit_def] >>
      drule_all supply_forward_sources_ready_exit >> simp[]) >>
  simp[supply_entry_pair_def] >> disj1_tac >>
  irule supply_ready_other_entry >> Cases_on `bb = pred` >>
  gvs[supply_body_exit_def] >> metis_tac[]
QED

Theorem supply_ready_run_block:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_ready fn pred target split repls u v /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb ==>
  lift_result (supply_entry_pair fn s pred target split repls)
    (supply_state_agree fn) (supply_state_agree fn)
    (run_block_entry fuel ctx bb u)
    (run_block_entry fuel ctx (supply_block_image pred target split repls bb) v)
Proof
  strip_tac >>
  drule_all supply_ready_run_block_body >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  `supply_entry_defined fn u` by gvs[supply_ready_def] >>
  Cases_on `run_block_entry fuel ctx bb u` >>
  Cases_on `run_block_entry fuel ctx (supply_block_image pred target split repls bb) v` >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >>
  drule_all supply_body_exit_entry_pair >> simp[]
QED

Theorem supply_ready_run_block_forward:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_ready fn pred target split repls u v /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block_entry fuel ctx bb u = r /\ (!e. r <> Error e) ==>
  ?r'. run_block_entry fuel ctx (supply_block_image pred target split repls bb) v = r' /\
    lift_result (supply_entry_pair fn s pred target split repls)
      (supply_state_agree fn) (supply_state_agree fn) r r'
Proof
  strip_tac >> drule_all supply_ready_run_block >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >> simp[]
QED

Theorem supply_ready_run_block_reverse:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  supply_ready fn pred target split repls u v /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block_entry fuel ctx (supply_block_image pred target split repls bb) v = r' /\
  (!e. r' <> Error e) ==>
  ?r. run_block_entry fuel ctx bb u = r /\
    lift_result (supply_entry_pair fn s pred target split repls)
      (supply_state_agree fn) (supply_state_agree fn) r r'
Proof
  strip_tac >> drule_all supply_ready_run_block >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >> simp[]
QED

(* Fuel padding is supplied by venomExecProofsTheory.run_block_fuel_mono
   and the run_blocks conjunct of venomExecProofsTheory.fuel_mono. *)
Theorem supply_run_blocks_assemble:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block_entry k ctx bb u = OK v /\ ~v.vs_halted /\
  run_blocks n ctx fn v = r /\ terminates r ==>
  ?N. run_blocks N ctx fn u = r
Proof
  strip_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> gvs[passSimulationDefsTheory.terminates_def]) >>
  `run_block_entry (k + n) ctx bb u = OK v` by
    (irule venomExecProofsTheory.run_block_fuel_mono >> simp[] >>
     qexists_tac `k` >> simp[]) >>
  `run_blocks (k + n) ctx fn v = r` by
    (irule (cj 3 venomExecProofsTheory.fuel_mono) >> simp[] >>
     qexists_tac `n` >> simp[]) >>
  qexists_tac `SUC (k + n)` >>
  once_rewrite_tac[venomExecSemanticsTheory.run_blocks_unfold] >> simp[]
QED

Theorem supply_run_blocks_terminal:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block_entry k ctx bb u = r /\ terminates r /\ (!v. r <> OK v) ==>
  run_blocks (SUC k) ctx fn u = r
Proof
  strip_tac >> once_rewrite_tac[venomExecSemanticsTheory.run_blocks_unfold] >>
  Cases_on `r` >> gvs[passSimulationDefsTheory.terminates_def]
QED

Theorem supply_run_blocks_halted:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block_entry k ctx bb u = OK v /\ v.vs_halted ==>
  run_blocks (SUC k) ctx fn u = Halt v
Proof
  strip_tac >> once_rewrite_tac[venomExecSemanticsTheory.run_blocks_unfold] >> simp[]
QED

Theorem supply_terminal_result_frame:
  terminates r /\ (!u. r <> OK u) /\
  lift_result R (supply_state_agree fn) (supply_state_agree fn) r r' ==>
  frame_result_rel r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[passSimulationDefsTheory.terminates_def, stateEquivTheory.lift_result_def,
       o1PassLiftTheory.frame_result_rel_def, supply_state_agree_def] >> metis_tac[]
QED

Theorem supply_run_blocks_forward:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  !n u v. supply_entry_pair fn s pred target split repls u v /\
    terminates (run_blocks n ctx fn u) ==>
    ?m. frame_result_rel (run_blocks n ctx fn u) (run_blocks m ctx fn' v)
Proof
  strip_tac >> completeInduct_on `n` >>
  `!u v. supply_ready fn pred target split repls u v /\
     terminates (run_blocks n ctx fn u) ==>
     ?m. frame_result_rel (run_blocks n ctx fn u) (run_blocks m ctx fn' v)` by
    (suspend "ready") >>
  rpt strip_tac >>
  gvs[supply_entry_pair_def] >>
  drule_all supply_pending_contract >>
  disch_then (qspecl_then [`0`, `ctx`] strip_assume_tac) >>
  first_x_assum (drule_then mp_tac) >> simp[] >> strip_tac >>
  drule_all supply_pending_split_lookup >> strip_tac >>
  `~m.vs_halted` by gvs[supply_ready_def] >>
  drule frame_result_rel_terminates >> strip_tac >>
  `?N. run_blocks N ctx fn' v = run_blocks m' ctx fn' m` by
    (irule supply_run_blocks_assemble >> metis_tac[]) >>
  metis_tac[]
QED

Resume supply_run_blocks_forward[ready]:
  rpt strip_tac >> Cases_on `n`
  >- gvs[Once venomExecSemanticsTheory.run_blocks_def,
         passSimulationDefsTheory.terminates_def] >>
  rename1 `SUC k` >>
  Cases_on `lookup_block u.vs_current_bb fn.fn_blocks`
  >- gvs[venomExecSemanticsTheory.run_blocks_unfold,
         passSimulationDefsTheory.terminates_def] >>
  rename1 `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` >>
  drule_all supply_ready_image_lookup >> strip_tac >>
  drule_all supply_ready_run_block >>
  disch_then (qspecl_then [`k`, `ctx`] mp_tac) >>
  Cases_on `run_block_entry k ctx bb u` >>
  Cases_on `run_block_entry k ctx (supply_block_image pred target split repls bb) v` >>
  simp[stateEquivTheory.lift_result_def] >> rpt strip_tac >>
  gvs[venomExecSemanticsTheory.run_blocks_unfold,
      passSimulationDefsTheory.terminates_def]
  >- suspend "continue" >>
  qexists_tac `SUC k` >>
  simp[venomExecSemanticsTheory.run_blocks_unfold,
       o1PassLiftTheory.frame_result_rel_def] >>
  gvs[supply_state_agree_def]
QED

Resume supply_run_blocks_forward[continue]:
  `~v'.vs_halted /\ ~v''.vs_halted` by
    gvs[supply_entry_pair_def, supply_ready_def, supply_pending_def] >>
  gvs[] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
  disch_then (drule_then mp_tac) >> simp[] >> strip_tac >>
  drule frame_result_rel_terminates >> strip_tac >>
  `?N. run_blocks N ctx fn' v = run_blocks m ctx fn' v''` by
    (irule supply_run_blocks_assemble >> metis_tac[]) >>
  metis_tac[]
QED

Finalise supply_run_blocks_forward

Theorem supply_entry_defined_lookup:
  wf_function fn /\ supply_entry_defined fn u ==>
  ?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb
Proof
  strip_tac >> gvs[supply_entry_defined_def, fn_reachable_def] >>
  gvs[Once relationTheory.RTC_CASES2]
  >- (gvs[fn_entry_label_def, entry_block_def] >>
      Cases_on `fn.fn_blocks` >> gvs[] >> qexists_tac `h` >>
      irule venomExecProofsTheory.MEM_lookup_block >>
      gvs[wf_function_def, fn_labels_def]) >>
  `MEM u.vs_current_bb (fn_labels fn)` by
    (gvs[fn_cfg_edge_def, wf_function_def] >>
     metis_tac[fn_succs_closed_def]) >>
  gvs[fn_labels_def, listTheory.MEM_MAP] >>
  metis_tac[venomExecProofsTheory.MEM_lookup_block, wf_function_def, fn_labels_def]
QED

Theorem supply_run_blocks_reverse:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') ==>
  !m u v. supply_entry_pair fn s pred target split repls u v /\
    terminates (run_blocks m ctx fn' v) ==>
    ?n. frame_result_rel (run_blocks n ctx fn u) (run_blocks m ctx fn' v)
Proof
  strip_tac >> completeInduct_on `m` >> rpt strip_tac >>
  Cases_on `m`
  >- gvs[Once venomExecSemanticsTheory.run_blocks_def,
         passSimulationDefsTheory.terminates_def] >>
  rename1 `SUC k` >>
  qpat_x_assum `supply_entry_pair _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[supply_entry_pair_def] >> strip_tac
  >- suspend "ready"
  >- suspend "pending"
QED

Resume supply_run_blocks_reverse[pending]:
  drule_all supply_pending_contract >>
  disch_then (qspecl_then [`k`, `ctx`] strip_assume_tac) >>
  drule_all supply_pending_split_lookup >> strip_tac >>
  `~m.vs_halted` by gvs[supply_ready_def] >>
  gvs[venomExecSemanticsTheory.run_blocks_unfold] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`u`, `m`] mp_tac) >>
  simp[supply_entry_pair_def]
QED

Resume supply_run_blocks_reverse[ready]:
  `supply_entry_defined fn u` by gvs[supply_ready_def] >>
  drule_all supply_entry_defined_lookup >> strip_tac >>
  drule_all supply_ready_image_lookup >> strip_tac >>
  drule_all supply_ready_run_block >>
  disch_then (qspecl_then [`k`, `ctx`] mp_tac) >>
  Cases_on `run_block_entry k ctx bb u` >>
  Cases_on `run_block_entry k ctx (supply_block_image pred target split repls bb) v` >>
  simp[stateEquivTheory.lift_result_def] >> rpt strip_tac >>
  gvs[venomExecSemanticsTheory.run_blocks_unfold,
      passSimulationDefsTheory.terminates_def]
  >- suspend "continue" >>
  qexists_tac `SUC k` >>
  simp[venomExecSemanticsTheory.run_blocks_unfold,
       o1PassLiftTheory.frame_result_rel_def] >>
  gvs[supply_state_agree_def]
QED

Resume supply_run_blocks_reverse[continue]:
  `~v'.vs_halted /\ ~v''.vs_halted` by
    gvs[supply_entry_pair_def, supply_ready_def, supply_pending_def] >>
  gvs[] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
  disch_then (drule_then mp_tac) >> simp[] >> strip_tac >>
  drule frame_result_rel_terminates >> strip_tac >>
  `?N. run_blocks N ctx fn u = run_blocks n ctx fn v'` by
    (irule supply_run_blocks_assemble >> metis_tac[]) >>
  metis_tac[]
QED

Finalise supply_run_blocks_reverse

(* Residual execution is independent of split construction. *)
Theorem supply_exec_block_step_residual:
  v.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL v.vs_inst_idx bb.bb_instructions /\
  step_inst fuel ctx inst v = OK w /\ exec_block fuel ctx bb v = OK m ==>
  (is_terminator inst.inst_opcode ==> w = m /\ ~w.vs_halted) /\
  (~is_terminator inst.inst_opcode ==>
    exec_block fuel ctx bb (w with vs_inst_idx := SUC v.vs_inst_idx) = OK m)
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [venomExecSemanticsTheory.exec_block_def]) >>
  simp[venomInstTheory.get_instruction_def] >>
  Cases_on `is_terminator (EL v.vs_inst_idx bb.bb_instructions).inst_opcode` >> simp[] >>
  Cases_on `w.vs_halted` >> simp[]
QED

Theorem supply_assign_fuel_independent:
  inst.inst_opcode = ASSIGN ==>
  step_inst fuel ctx inst v = step_inst fuel' ctx' inst v
Proof
  simp[venomExecSemanticsTheory.step_inst_def]
QED

Theorem supply_assign_step_agree:
  inst.inst_opcode = ASSIGN /\
  EVERY (\x. ~MEM x (irSupply$fn_ir_vars fn)) inst.inst_outputs /\
  supply_state_agree fn a v /\ ~v.vs_halted /\
  step_inst fuel ctx inst v = OK w ==>
  supply_state_agree fn a w /\ ~w.vs_halted
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_def,
       venomExecSemanticsTheory.step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  irule supply_state_agree_update_fresh >> gvs[]
QED

Theorem supply_split_index_shape:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  build_split_block_supply s pred target = (split,repls,s') /\
  i < LENGTH split.bb_instructions ==>
  ((EL i split.bb_instructions).inst_opcode = ASSIGN /\
   EVERY (\x. ~MEM x (irSupply$fn_ir_vars fn))
     (EL i split.bb_instructions).inst_outputs) \/
  (i = PRE (LENGTH split.bb_instructions) /\
   (EL i split.bb_instructions).inst_opcode = JMP)
Proof
  strip_tac >>
  `EVERY (\x. ~MEM x s.irs_used_vars) (cfg_block_decl_vars split)` by
    metis_tac[supply_split_outputs_distinct] >>
  Cases_on `fresh_ir_label s` >>
  Cases_on `build_forwarding_assigns_supply r
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  rename1 `build_forwarding_assigns_supply r _ = (rs,rest)` >>
  PairCases_on `rest` >> Cases_on `fresh_inst_id rest1` >>
  drule supply_forwarding_opcodes >> strip_tac >>
  gvs[build_split_block_supply_def] >>
  Cases_on `i < LENGTH rest0`
  >- (disj1_tac >> simp[listTheory.EL_APPEND_EQN] >> conj_tac
      >- gvs[listTheory.EVERY_EL] >>
      gvs[cfg_block_decl_vars_def, listTheory.EVERY_MEM,
          listTheory.MEM_FLAT, listTheory.MEM_MAP,
          ir_supply_covers_fn_def, list_subset_def] >>
      rpt strip_tac >> metis_tac[listTheory.MEM_EL]) >>
  `i = LENGTH rest0` by decide_tac >>
  gvs[listTheory.EL_APPEND_EQN]
QED

Theorem supply_split_step_agree:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  build_split_block_supply s pred target = (split,repls,s') /\
  v.vs_inst_idx < LENGTH split.bb_instructions /\
  inst = EL v.vs_inst_idx split.bb_instructions /\
  ~is_terminator inst.inst_opcode /\
  supply_state_agree fn a v /\ ~v.vs_halted /\
  step_inst fuel ctx inst v = OK w ==>
  supply_state_agree fn a w /\ ~w.vs_halted /\ inst.inst_opcode = ASSIGN
Proof
  strip_tac >> drule_all supply_split_index_shape >> strip_tac >>
  gvs[is_terminator_def] >>
  metis_tac[supply_assign_step_agree]
QED

Theorem supply_terminator_step_self_agree:
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst a = OK u ==>
  supply_state_agree fn a u
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `step_inst_base inst a = OK u` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >> simp[Once venomExecSemanticsTheory.step_inst_def]) >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def] >>
  gvs[venomExecSemanticsTheory.step_inst_base_opcode_eqs, AllCaseEqs()] >>
  gvs[venomStateTheory.jump_to_def, supply_state_agree_def,
      stateFrameTheory.execution_frame_def, venomStateTheory.lookup_var_def] >>
  pairarg_tac >> gvs[]
QED

(* Local-label origins through splitting. INVOKE labels remain external. *)
Theorem supply_phi_value_label_mem[local]:
  (Label l =
    (case op of Var v => (case ALOOKUP repls v of
       SOME w => Var w | NONE => Var v) | other => other)) <=>
  Label l = op
Proof
  Cases_on `op` >> simp[optionTheory.option_case_compute, COND_RAND, COND_RATOR]
QED

Theorem supply_update_phi_ops_label_origin:
  !old new repls ops l.
    MEM (Label l) (update_phi_ops old new repls ops) ==>
    l = new \/ MEM (Label l) ops
Proof
  recInduct update_phi_ops_ind >> rpt strip_tac >>
  fs[Once update_phi_ops_def, COND_RAND, supply_phi_value_label_mem] >>
  Cases_on `l = old_label` >> fs[supply_phi_value_label_mem] >> metis_tac[]
QED

Theorem supply_subst_label_ops_label_origin:
  !ops old new l.
    MEM (Label l) (MAP (subst_label_op old new) ops) ==>
    l = new \/ MEM (Label l) ops
Proof
  Induct_on `ops` >> simp[] >> rpt gen_tac >>
  Cases_on `h` >> simp[cfgTransformTheory.subst_label_op_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem supply_subst_terminator_label_refs:
  EVERY (\i. i.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) i.inst_operands ==> P l) bb.bb_instructions /\ P new ==>
  EVERY (\i. i.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) i.inst_operands ==> P l)
    (subst_label_terminator old new bb).bb_instructions
Proof
  simp[cfgTransformTheory.subst_label_terminator_def] >>
  pure_rewrite_tac[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  simp[] >> rpt strip_tac >> Cases_on `is_terminator e.inst_opcode` >>
  gvs[cfgTransformTheory.subst_label_inst_def] >> metis_tac[supply_subst_label_ops_label_origin]
QED

Theorem supply_update_phis_label_refs:
  EVERY (\i. i.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) i.inst_operands ==> P l) bb.bb_instructions /\ P new ==>
  EVERY (\i. i.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) i.inst_operands ==> P l)
    (update_phis_for_split old new repls bb).bb_instructions
Proof
  simp[update_phis_for_split_def] >>
  pure_rewrite_tac[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  simp[] >> rpt strip_tac >> Cases_on `e.inst_opcode = PHI` >>
  gvs[] >- (drule supply_update_phi_ops_label_origin >>
    strip_tac >> gvs[] >> first_x_assum drule >> simp[]) >> metis_tac[]
QED

Theorem supply_block_image_label_refs:
  EVERY (\i. i.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) i.inst_operands ==> P l) bb.bb_instructions /\
  P split.bb_label ==>
  EVERY (\i. i.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) i.inst_operands ==> P l)
    (supply_block_image pred target split repls bb).bb_instructions
Proof
  strip_tac >> simp[supply_block_image_def] >> rpt IF_CASES_TAC >>
  metis_tac[supply_subst_terminator_label_refs, supply_update_phis_label_refs]
QED

Theorem supply_forwarding_no_labels:
  !s vars repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    EVERY (\i. !l. ~MEM (Label l) i.inst_operands) insts
Proof
  Induct_on `vars` >> rpt gen_tac
  >- simp[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (v,s1)` >>
  Cases_on `fresh_inst_id s1` >>
  Cases_on `build_forwarding_assigns_supply r vars` >>
  rename1 `build_forwarding_assigns_supply r vars = (rs,tail)` >>
  PairCases_on `tail` >>
  simp[build_forwarding_assigns_supply_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem supply_split_label_refs:
  build_split_block_supply s pred target = (split,repls,s') /\
  P target.bb_label ==>
  EVERY (\i. i.inst_opcode <> INVOKE ==>
    !l. MEM (Label l) i.inst_operands ==> P l) split.bb_instructions
Proof
  strip_tac >> Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lbl,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ = (rs,is,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  gvs[build_split_block_supply_def] >>
  drule supply_forwarding_no_labels >> simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

(* Each generated copy records exactly its source/destination correspondence. *)
Theorem supply_forward_inst_replacement:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    !inst x. MEM inst insts /\ MEM x inst.inst_outputs ==>
      inst.inst_opcode = ASSIGN /\
      ?v. MEM (v,x) repls /\ inst.inst_operands = [Var v]
Proof
  Induct_on `vars` >> rpt gen_tac >> strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (nv,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem supply_split_inst_replacement:
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM inst split.bb_instructions /\ MEM x inst.inst_outputs ==>
  inst.inst_opcode = ASSIGN /\
  ?v. MEM (v,x) repls /\ inst.inst_operands = [Var v]
Proof
  strip_tac >> Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lab,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >> Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def, listTheory.MEM_APPEND] >>
  drule supply_forward_inst_replacement >>
  disch_then (drule_then mp_tac) >> metis_tac[]
QED

Theorem supply_phi_value_var_origin[local]:
  Var x = (case op of
    Var v => (case ALOOKUP repls v of SOME w => Var w | NONE => Var v)
    | other => other) ==>
  Var x = op \/ ?v. op = Var v /\ MEM (v,x) repls
Proof
  Cases_on `op` >> simp[] >>
  Cases_on `ALOOKUP repls s` >> simp[] >>
  metis_tac[alistTheory.ALOOKUP_MEM]
QED

Theorem supply_update_phi_ops_var_origin:
  !old new repls ops x.
    MEM (Var x) (update_phi_ops old new repls ops) ==>
    MEM (Var x) ops \/
    ?v. MEM (Var v) ops /\ MEM (v,x) repls
Proof
  recInduct update_phi_ops_ind >> rpt strip_tac >>
  gvs[Once update_phi_ops_def, AllCaseEqs()] >>
  Cases_on `l = old_label` >> gvs[] >>
  metis_tac[supply_phi_value_var_origin]
QED

Theorem supply_forward_replacement_outputs:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    MAP SND repls = FLAT (MAP (\i. i.inst_outputs) insts)
Proof
  Induct_on `vars` >> rpt gen_tac >> strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (nv,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def] >> metis_tac[]
QED

Theorem supply_split_replacement_outputs:
  build_split_block_supply s pred target = (split,repls,s') ==>
  MAP SND repls = cfg_block_decl_vars split
Proof
  strip_tac >> Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lab,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >> Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def, cfg_block_decl_vars_def,
      listTheory.MAP_APPEND] >>
  metis_tac[supply_forward_replacement_outputs]
QED

Theorem supply_split_replacement_sources_unique:
  ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM (v,x) repls /\ MEM (w,x) repls ==> v = w
Proof
  strip_tac >> drule_all supply_split_outputs_distinct >> strip_tac >>
  drule supply_split_replacement_outputs >> strip_tac >>
  `ALL_DISTINCT (MAP SND repls)` by metis_tac[] >>
  `(v,x) = (w,x)` suffices_by simp[] >>
  irule (ISPEC ``SND : string # string -> string`` all_distinct_map_mem_inj_cfg) >>
  simp[] >> qexists `repls` >> simp[]
QED

Theorem supply_split_replacement_not_old:
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM (v,x) repls ==> ~MEM x (irSupply$fn_ir_vars fn)
Proof
  strip_tac >> drule_all supply_split_outputs_distinct >> strip_tac >>
  drule supply_split_replacement_outputs >> strip_tac >>
  `MEM x (cfg_block_decl_vars split)` by
    (qpat_x_assum `MAP SND repls = _` (mp_tac o GSYM) >>
     disch_then SUBST1_TAC >> simp[listTheory.MEM_MAP] >>
     qexists `(v,x)` >> simp[]) >>
  gvs[listTheory.EVERY_MEM, ir_supply_covers_fn_def, list_subset_def] >>
  metis_tac[]
QED

Theorem supply_inst_output_ir_var:
  MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
  MEM x (irSupply$fn_ir_vars fn)
Proof
  strip_tac >> irule supply_decl_var_ir_var >>
  simp[cfg_fn_decl_vars_def, supply_decl_vars_insts_blocks,
       GSYM fn_insts_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  qexists `inst.inst_outputs` >> simp[] >> qexists `inst` >> simp[]
QED

Theorem supply_copy_phi_var_ir_var:
  !origin fn x. copy_phi_var origin fn x ==>
  MEM x (irSupply$fn_ir_vars fn)
Proof
  Induct_on `copy_phi_var` >> metis_tac[supply_inst_output_ir_var]
QED

Theorem supply_forward_replacement_sources:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    MAP FST repls = vars
Proof
  Induct_on `vars` >> rpt gen_tac >> strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (nv,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def] >> metis_tac[]
QED

Theorem supply_split_replacement_source_ir_var:
  MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM (v,x) repls ==> MEM v (irSupply$fn_ir_vars fn)
Proof
  strip_tac >> Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (lab,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  PairCases_on `r` >> Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def] >>
  rename1 `MEM (v,x) repls` >>
  drule supply_forward_replacement_sources >> strip_tac >>
  `MEM v (MAP FST repls)` by
    (simp[listTheory.MEM_MAP] >> qexists `(v,x)` >> simp[]) >>
  `MEM v (phi_vars_needing_forward pred.bb_label pred target.bb_instructions)` by
    metis_tac[listTheory.MEM_nub] >>
  drule MEM_phi_vars_needing_forward_block_vars >> strip_tac >>
  simp[irSupplyTheory.fn_ir_vars_def, listTheory.MEM_FLAT,
       listTheory.MEM_MAP] >>
  qexists `block_ir_vars target` >>
  conj_tac >- (qexists `target` >> simp[]) >>
  gvs[irSupplyTheory.block_ir_vars_def]
QED

(* Instruction-level image relation: consumers need no block/index plumbing. *)
Definition supply_inst_image_def:
  supply_inst_image pred target split repls i j <=>
    j = i \/
    (i.inst_opcode = PHI /\ j = i with inst_operands :=
      update_phi_ops pred split repls i.inst_operands) \/
    (is_terminator i.inst_opcode /\ j = subst_label_inst target split i)
End

Theorem supply_block_image_index_image:
  n < LENGTH bb.bb_instructions ==>
  supply_inst_image pred.bb_label target.bb_label split.bb_label repls
    (EL n bb.bb_instructions)
    (EL n (supply_block_image pred target split repls bb).bb_instructions)
Proof
  strip_tac >>
  Cases_on `(EL n bb.bb_instructions).inst_opcode = PHI`
  >- (simp[supply_block_image_index_phi, supply_inst_image_def] >>
      Cases_on `bb.bb_label = target.bb_label` >> simp[]) >>
  simp[supply_block_image_def] >> rpt IF_CASES_TAC >>
  simp[supply_update_phis_index, supply_subst_terminator_index,
       supply_inst_image_def] >>
  Cases_on `is_terminator (EL n bb.bb_instructions).inst_opcode` >>
  simp[update_phis_for_split_def, subst_label_terminator_def,
       listTheory.EL_MAP, subst_label_inst_def]
QED

Theorem supply_fn_insts_blocks_mem[local]:
  !bbs inst. MEM inst (fn_insts_blocks bbs) <=>
    ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem insert_split_supply_inst_image:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts fn') ==>
  MEM inst split.bb_instructions \/
  ?old. MEM old (fn_insts fn) /\
    supply_inst_image pred.bb_label target.bb_label split.bb_label repls old inst
Proof
  strip_tac >>
  `?bb. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[fn_insts_def] >>
     metis_tac[supply_fn_insts_blocks_mem]) >>
  drule_all insert_split_supply_block_cases >> strip_tac
  >- (gvs[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  gvs[] >> disj2_tac >>
  qpat_x_assum `MEM inst _` mp_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [listTheory.MEM_EL]) >>
  gvs[] >>
  qexists `EL n bb'.bb_instructions` >>
  conj_tac
  >- (simp[fn_insts_def] >> irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
      qexists `bb'` >> simp[listTheory.MEM_EL] >> metis_tac[]) >>
  irule supply_block_image_index_image >> gvs[]
QED

Theorem supply_inst_image_metadata:
  supply_inst_image pred target split repls i j ==>
  j.inst_opcode = i.inst_opcode /\ j.inst_outputs = i.inst_outputs
Proof
  rw[supply_inst_image_def, subst_label_inst_def] >> simp[]
QED

Theorem supply_inst_image_unchanged:
  supply_inst_image pred target split repls i j /\
  i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode ==> j = i
Proof
  simp[supply_inst_image_def] >> metis_tac[]
QED

Theorem supply_inst_image_nonphi_vars:
  supply_inst_image pred target split repls i j /\ i.inst_opcode <> PHI ==>
  (MEM (Var x) j.inst_operands <=> MEM (Var x) i.inst_operands)
Proof
  rw[supply_inst_image_def, subst_label_inst_def] >>
  simp[supply_subst_label_ops_vars]
QED

Theorem supply_inst_image_phi_vars:
  supply_inst_image pred target split repls i j /\ i.inst_opcode = PHI /\
  MEM (Var x) j.inst_operands ==>
  MEM (Var x) i.inst_operands \/
  ?v. MEM (Var v) i.inst_operands /\ MEM (v,x) repls
Proof
  rw[supply_inst_image_def] >>
  gvs[is_terminator_def] >> metis_tac[supply_update_phi_ops_var_origin]
QED

Theorem supply_subst_label_gas_use:
  gas_use_ok i x ==> gas_use_ok (subst_label_inst old new i) x
Proof
  rw[gas_use_ok_def, subst_label_inst_def] >>
  simp[subst_label_op_def, supply_subst_label_ops_vars]
QED

Theorem supply_subst_label_retpc_use:
  retpc_use_ok i x ==> retpc_use_ok (subst_label_inst old new i) x
Proof
  rw[retpc_use_ok_def, subst_label_inst_def] >>
  simp[listTheory.MAP_APPEND, subst_label_op_def, supply_subst_label_ops_vars]
QED

Theorem supply_inst_image_gas_use:
  supply_inst_image pred target split repls i j /\ gas_use_ok i x ==>
  gas_use_ok j x
Proof
  rw[supply_inst_image_def]
  >- simp[]
  >- simp[gas_use_ok_def] >>
  irule supply_subst_label_gas_use >> simp[]
QED

Theorem supply_inst_image_retpc_use:
  supply_inst_image pred target split repls i j /\ retpc_use_ok i x ==>
  retpc_use_ok j x
Proof
  rw[supply_inst_image_def]
  >- simp[]
  >- simp[retpc_use_ok_def] >>
  irule supply_subst_label_retpc_use >> simp[]
QED

Theorem supply_inst_image_assign:
  supply_inst_image pred target split repls i j /\ i.inst_opcode = ASSIGN ==>
  j = i
Proof
  strip_tac >> irule supply_inst_image_unchanged >>
  simp[is_terminator_def] >> goal_assum (drule_at Any)
QED

Theorem supply_inst_image_dalloca:
  supply_inst_image pred target split repls i j /\ i.inst_opcode = DALLOCA ==>
  j = i
Proof
  strip_tac >> irule supply_inst_image_unchanged >>
  simp[is_terminator_def] >> goal_assum (drule_at Any)
QED

Theorem supply_inst_operand_ir_var:
  MEM inst (fn_insts fn) /\ MEM (Var v) inst.inst_operands ==>
  MEM v (irSupply$fn_ir_vars fn)
Proof
  simp[fn_insts_def, supply_fn_insts_blocks_mem] >>
  metis_tac[supply_operand_in_fn]
QED

Theorem insert_split_supply_old_inst_image:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts fn) ==>
  ?j. MEM j (fn_insts fn') /\
    supply_inst_image pred.bb_label target.bb_label split.bb_label repls inst j
Proof
  strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[fn_insts_def, supply_fn_insts_blocks_mem] >> metis_tac[]) >>
  qpat_x_assum `MEM inst bb.bb_instructions` mp_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [listTheory.MEM_EL]) >>
  qexists `EL n (supply_block_image pred target split repls bb).bb_instructions` >>
  conj_tac
  >- (rewrite_tac[fn_insts_def] >>
      irule unitShapeDefsTheory.MEM_fn_insts_blocks >>
      qexists `supply_block_image pred target split repls bb` >>
      conj_tac >- metis_tac[insert_split_supply_image_mem] >>
      simp[listTheory.MEM_EL] >> metis_tac[supply_block_image_length]) >>
  gvs[] >> irule supply_block_image_index_image >> simp[]
QED

Theorem supply_update_phi_ops_var_forward:
  !old new repls ops v.
    MEM (Var v) ops ==>
    MEM (Var v) (update_phi_ops old new repls ops) \/
    ?w. MEM (v,w) repls /\ MEM (Var w) (update_phi_ops old new repls ops)
Proof
  recInduct update_phi_ops_ind >> rpt strip_tac >>
  simp[update_phi_ops_def] >>
  TRY (Cases_on `l = old_label` >> gvs[] >>
       Cases_on `ALOOKUP var_repls v` >> gvs[]) >>
  metis_tac[alistTheory.ALOOKUP_MEM]
QED

Theorem insert_split_supply_copy_phi_fresh_forward:
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\ MEM (v,w) repls /\
  copy_phi_var origin fn' v ==> copy_phi_var origin fn' w
Proof
  strip_tac >>
  drule_all supply_split_replacement_definition >> strip_tac >>
  drule_all supply_split_inst_replacement >> strip_tac >>
  `v' = v` by metis_tac[supply_split_replacement_sources_unique] >> gvs[] >>
  `MEM split fn'.fn_blocks` by
    (irule venomExecProofsTheory.lookup_block_MEM >>
     qexists `split.bb_label` >> irule insert_split_supply_split_lookup >>
     goal_assum (drule_at Any) >>
     metis_tac[supply_split_label_not_old, fn_labels_def]) >>
  irule copy_phi_var_assign >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[fn_insts_def, supply_fn_insts_blocks_mem] >> metis_tac[]
QED

Theorem insert_split_supply_copy_phi_forward:
  !origin fn x. copy_phi_var origin fn x ==>
  !s fn' pred target split repls s'.
    wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
    build_split_block_supply s pred target = (split,repls,s') /\
    insert_split_supply s fn pred target = (fn',s') /\
    origin <> PHI /\ ~is_terminator origin ==>
    copy_phi_var origin fn' x
Proof
  ho_match_mp_tac copy_phi_var_ind >> rpt conj_tac
  >- suspend "seed"
  >- suspend "assign"
  >> suspend "phi"
QED

Resume insert_split_supply_copy_phi_forward[seed]:
  rpt strip_tac >> drule_all insert_split_supply_old_inst_image >> strip_tac >>
  `j = inst` by metis_tac[supply_inst_image_unchanged] >> gvs[] >>
  irule copy_phi_var_seed >> goal_assum (drule_at Any) >> simp[]
QED

Resume insert_split_supply_copy_phi_forward[assign]:
  rpt strip_tac >> first_x_assum (drule_all_then assume_tac) >>
  drule_all insert_split_supply_old_inst_image >> strip_tac >>
  `j = inst` by metis_tac[supply_inst_image_assign] >> gvs[] >>
  irule copy_phi_var_assign >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume insert_split_supply_copy_phi_forward[phi]:
  rpt strip_tac >> first_x_assum (drule_all_then assume_tac) >>
  drule_all insert_split_supply_old_inst_image >> strip_tac >>
  drule supply_inst_image_metadata >> strip_tac >>
  qpat_x_assum `supply_inst_image _ _ _ _ _ _` mp_tac >>
  simp[supply_inst_image_def] >> strip_tac
  >- (gvs[] >> irule copy_phi_var_phi >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) 
  >- (gvs[] >> drule supply_update_phi_ops_var_forward >>
      disch_then (qspecl_then [`pred.bb_label`, `split.bb_label`, `repls`] mp_tac) >>
      strip_tac
      >- (irule copy_phi_var_phi >> goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >> simp[]) >>
      `copy_phi_var origin fn' w` by
        (irule insert_split_supply_copy_phi_fresh_forward >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
         goal_assum (drule_at Any) >> simp[]) >>
      irule copy_phi_var_phi >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[is_terminator_def]
QED

Finalise insert_split_supply_copy_phi_forward

Theorem insert_split_supply_copy_phi_projection:
  !origin fn' x. copy_phi_var origin fn' x ==>
  !s fn pred target split repls s'.
    wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
    build_split_block_supply s pred target = (split,repls,s') /\
    insert_split_supply s fn pred target = (fn',s') /\
    origin <> ASSIGN /\ origin <> PHI /\ origin <> JMP ==>
    copy_phi_var origin fn x \/
    ?v. MEM (v,x) repls /\ copy_phi_var origin fn v
Proof
  ho_match_mp_tac copy_phi_var_ind >> rpt conj_tac
  >- suspend "seed"
  >- suspend "assign"
  >> suspend "phi"
QED

Resume insert_split_supply_copy_phi_projection[seed]:
  rpt strip_tac >>
  drule_all insert_split_supply_inst_image >> strip_tac
  >- (drule_all supply_split_inst_replacement >> simp[])
  >> drule supply_inst_image_metadata >> strip_tac >>
  disj1_tac >> irule copy_phi_var_seed >> goal_assum (drule_at Any) >> gvs[]
QED

Resume insert_split_supply_copy_phi_projection[assign]:
  rpt strip_tac >>
  first_x_assum (drule_all_then mp_tac) >> disch_tac >>
  drule_all insert_split_supply_inst_image >> strip_tac
  >- (drule_all supply_split_inst_replacement >> strip_tac >>
      `v = x'` by gvs[] >>
      `MEM x' (irSupply$fn_ir_vars fn)` by
        metis_tac[supply_split_replacement_source_ir_var] >>
      `copy_phi_var origin fn x'` by
        metis_tac[supply_split_replacement_not_old] >>
      disj2_tac >> qexists `x'` >> metis_tac[]) >>
  drule supply_inst_image_metadata >> strip_tac >>
  `inst = old` by metis_tac[supply_inst_image_assign] >> gvs[] >>
  `MEM x' (irSupply$fn_ir_vars fn)` by
    (irule supply_inst_operand_ir_var >> goal_assum (drule_at Any) >> simp[]) >>
  `copy_phi_var origin fn x'` by
    metis_tac[supply_split_replacement_not_old] >>
  disj1_tac >> irule copy_phi_var_assign >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Resume insert_split_supply_copy_phi_projection[phi]:
  rpt strip_tac >>
  first_x_assum (drule_all_then mp_tac) >> disch_tac >>
  drule_all insert_split_supply_inst_image >> strip_tac
  >- (drule_all supply_split_inst_replacement >> simp[]) >>
  drule supply_inst_image_metadata >> strip_tac >>
  `old.inst_opcode = PHI` by metis_tac[] >>
  drule_all supply_inst_image_phi_vars >> strip_tac
  >- (`MEM x' (irSupply$fn_ir_vars fn)` by
        metis_tac[supply_inst_operand_ir_var] >>
      `copy_phi_var origin fn x'` by
        metis_tac[supply_split_replacement_not_old] >>
      disj1_tac >> irule copy_phi_var_phi >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> gvs[]) >>
  `~MEM x' (irSupply$fn_ir_vars fn)` by
    metis_tac[supply_split_replacement_not_old] >>
  `copy_phi_var origin fn v` by
    metis_tac[supply_copy_phi_var_ir_var,
              supply_split_replacement_sources_unique] >>
  disj1_tac >> irule copy_phi_var_phi >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> gvs[]
QED

Finalise insert_split_supply_copy_phi_projection

Theorem insert_split_supply_copy_phi_old_var:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  origin <> ASSIGN /\ origin <> PHI /\ origin <> JMP /\
  MEM x (irSupply$fn_ir_vars fn) /\ copy_phi_var origin fn' x ==>
  copy_phi_var origin fn x
Proof
  strip_tac >> drule_all insert_split_supply_copy_phi_projection >>
  metis_tac[supply_split_replacement_not_old]
QED

Theorem insert_split_supply_copy_phi_replacement:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  origin <> ASSIGN /\ origin <> PHI /\ origin <> JMP /\
  MEM (v,x) repls /\ copy_phi_var origin fn' x ==>
  copy_phi_var origin fn v
Proof
  strip_tac >>
  `~MEM x (irSupply$fn_ir_vars fn)` by
    metis_tac[supply_split_replacement_not_old] >>
  drule_all insert_split_supply_copy_phi_projection >>
  metis_tac[supply_copy_phi_var_ir_var,
            supply_split_replacement_sources_unique]
QED

(* Reachable instruction boundaries for seeded copy/PHI closure transport. *)
Theorem insert_split_supply_reachable_nonphi_forward:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts (reachable_fn fn)) /\ inst.inst_opcode <> PHI /\
  ~is_terminator inst.inst_opcode ==>
  MEM inst (fn_insts (reachable_fn fn'))
Proof
  strip_tac >>
  qpat_x_assum `MEM inst (fn_insts (reachable_fn fn))`
    (strip_assume_tac o REWRITE_RULE [MEM_reachable_fn_insts]) >>
  `i.inst_opcode <> PHI` by metis_tac[reachable_inst_fields] >>
  `inst = i` by metis_tac[reachable_inst_fields] >> gvs[] >>
  qpat_x_assum `MEM i bb.bb_instructions` mp_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [listTheory.MEM_EL]) >>
  `supply_inst_image pred.bb_label target.bb_label split.bb_label repls i
    (EL n (supply_block_image pred target split repls bb).bb_instructions)` by
    metis_tac[supply_block_image_index_image] >>
  `EL n (supply_block_image pred target split repls bb).bb_instructions = i` by
    metis_tac[supply_inst_image_unchanged] >>
  `MEM i (supply_block_image pred target split repls bb).bb_instructions` by
    metis_tac[listTheory.MEM_EL, supply_block_image_length] >>
  `MEM (reachable_inst fn' bb.bb_label i) (fn_insts (reachable_fn fn'))` by
    (irule insert_split_supply_reachable_image_mem >> metis_tac[]) >>
  gvs[reachable_inst_fields]
QED

Theorem supply_split_assign_replacement:
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM inst split.bb_instructions /\ ~is_terminator inst.inst_opcode ==>
  ?v w. MEM (v,w) repls /\ inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Var v] /\ inst.inst_outputs = [w]
Proof
  strip_tac >>
  `inst_wf inst` by
    metis_tac[build_split_block_supply_inst_wf, listTheory.EVERY_MEM] >>
  `inst.inst_opcode = ASSIGN` by
    (drule_all supply_split_inst_source >> strip_tac >> gvs[is_terminator_def]) >>
  `LENGTH inst.inst_outputs = 1` by gvs[inst_wf_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  `MEM h inst.inst_outputs` by simp[] >>
  drule_all supply_split_inst_replacement >> strip_tac >> metis_tac[]
QED

Theorem insert_split_supply_reachable_nonphi_backward:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts (reachable_fn fn')) /\ inst.inst_opcode <> PHI /\
  ~is_terminator inst.inst_opcode ==>
  MEM inst (fn_insts (reachable_fn fn)) \/
  ?v w. MEM (v,w) repls /\ fn_reachable fn pred.bb_label /\
    fn_cfg_edge fn pred.bb_label target.bb_label /\ inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Var v] /\ inst.inst_outputs = [w]
Proof
  strip_tac >> drule_all insert_split_supply_reachable_inst_cases >> strip_tac
  >- (disj2_tac >> drule_all supply_split_assign_replacement >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `inst = reachable_inst fn' bb.bb_label j` >>
  `supply_inst_image pred.bb_label target.bb_label split.bb_label repls
    (EL n bb.bb_instructions) j` by
    (simp[Abbr `j`] >> irule supply_block_image_index_image >> simp[]) >>
  `j.inst_opcode <> PHI /\ ~is_terminator j.inst_opcode` by
    metis_tac[reachable_inst_fields] >>
  `inst = j` by metis_tac[reachable_inst_fields] >>
  `j = EL n bb.bb_instructions` by
    metis_tac[supply_inst_image_unchanged, supply_inst_image_metadata] >>
  disj1_tac >> rewrite_tac[MEM_reachable_fn_insts] >>
  qexistsl [`bb`, `j`] >> simp[] >>
  conj_tac >- metis_tac[listTheory.MEM_EL] >>
  metis_tac[reachable_inst_fields]
QED

Theorem insert_split_supply_reachable_fresh_definition:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  fn_reachable fn pred.bb_label /\ fn_cfg_edge fn pred.bb_label target.bb_label /\
  MEM (v,w) repls ==>
  ?inst. MEM inst (fn_insts (reachable_fn fn')) /\ inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [Var v] /\ inst.inst_outputs = [w]
Proof
  strip_tac >> drule_all supply_split_replacement_definition >> strip_tac >>
  drule_all supply_split_inst_replacement >> strip_tac >>
  `v' = v` by metis_tac[supply_split_replacement_sources_unique] >> gvs[] >>
  `?u z. MEM (u,z) repls /\ inst.inst_opcode = ASSIGN /\
     inst.inst_operands = [Var u] /\ inst.inst_outputs = [z]` by
    (irule supply_split_assign_replacement >>
     simp[is_terminator_def] >> metis_tac[]) >>
  `z = w` by gvs[] >> gvs[] >> qexists `inst` >> simp[] >>
  rewrite_tac[MEM_reachable_fn_insts] >> qexistsl [`split`, `inst`] >>
  simp[reachable_inst_fields] >> conj_tac
  >- (irule venomExecProofsTheory.lookup_block_MEM >>
      qexists `split.bb_label` >> irule insert_split_supply_split_lookup >>
      goal_assum (drule_at Any) >>
      metis_tac[supply_split_label_not_old, fn_labels_def]) >>
  metis_tac[insert_split_supply_reachable_split_iff]
QED

Theorem insert_split_supply_reachable_phi_forward:
  wf_function fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts (reachable_fn fn)) /\ inst.inst_opcode = PHI ==>
  ?j. MEM j (fn_insts (reachable_fn fn')) /\ j.inst_opcode = PHI /\
    j.inst_outputs = inst.inst_outputs /\
    (!v. MEM (Var v) inst.inst_operands ==>
      MEM (Var v) j.inst_operands \/
      ?w. MEM (v,w) repls /\ fn_reachable fn pred.bb_label /\
        fn_cfg_edge fn pred.bb_label target.bb_label /\ MEM (Var w) j.inst_operands)
Proof
  strip_tac >>
  qpat_x_assum `MEM inst (fn_insts (reachable_fn fn))`
    (strip_assume_tac o REWRITE_RULE [MEM_reachable_fn_insts]) >>
  `i.inst_opcode = PHI` by metis_tac[reachable_inst_fields] >>
  `phi_well_formed i.inst_operands` by
    (irule (cj 1 cfgNormBaseTheory.inst_wf_phi_well_formed) >>
     gvs[fn_inst_wf_def] >> metis_tac[]) >>
  qpat_x_assum `MEM i bb.bb_instructions`
    (strip_assume_tac o REWRITE_RULE [listTheory.MEM_EL]) >>
  qabbrev_tac `j = EL n (supply_block_image pred target split repls bb).bb_instructions` >>
  `supply_inst_image pred.bb_label target.bb_label split.bb_label repls i j` by
    (simp[Abbr `j`] >> irule supply_block_image_index_image >> simp[]) >>
  `j.inst_opcode = PHI /\ j.inst_outputs = i.inst_outputs` by
    metis_tac[supply_inst_image_metadata] >>
  qexists `reachable_inst fn' bb.bb_label j` >>
  simp[reachable_inst_fields] >> conj_tac
  >- (`MEM j (supply_block_image pred target split repls bb).bb_instructions` by
        (simp[Abbr `j`, listTheory.MEM_EL] >> metis_tac[supply_block_image_length]) >>
      irule insert_split_supply_reachable_image_mem >> metis_tac[]) >>
  suspend "vars"
QED

Resume insert_split_supply_reachable_phi_forward[vars]:
  `phi_well_formed inst.inst_operands` by
    (gvs[reachable_inst_def] >>
     metis_tac[simplifyCfgStructTheory.filter_phi_ops_well_formed]) >>
  `!l v. MEM (l,v) (phi_pairs (reachable_inst fn' bb.bb_label j).inst_operands) <=>
    ?k w. MEM (k,w) (phi_pairs inst.inst_operands) /\
      l = (if bb.bb_label = target.bb_label /\ k = pred.bb_label then split.bb_label else k) /\
      v = (if bb.bb_label = target.bb_label /\ k = pred.bb_label then
             (case ALOOKUP repls w of NONE => w | SOME u => u) else w)` by
    (rpt gen_tac >>
     `j = EL n (supply_block_image pred target split repls bb).bb_instructions` by
       simp[Abbr `j`] >>
     drule_all insert_split_supply_reachable_phi_pair >>
     disch_then (qspecl_then [`v`, `l`] mp_tac) >>
     qpat_x_assum `inst = reachable_inst _ _ _` SUBST_ALL_TAC >>
     disch_then MATCH_ACCEPT_TAC) >>
  rpt strip_tac >>
  `MEM (Var v) inst.inst_operands` by metis_tac[] >>
  drule_all phi_well_formed_var_pair >> strip_tac >>
  `MEM (if bb.bb_label = target.bb_label /\ lbl = pred.bb_label then split.bb_label else lbl,
        if bb.bb_label = target.bb_label /\ lbl = pred.bb_label then
           (case ALOOKUP repls v of NONE => v | SOME u => u) else v)
    (phi_pairs (reachable_inst fn' bb.bb_label j).inst_operands)` by metis_tac[] >>
  qpat_x_assum `!l v. _` kall_tac >>
  Cases_on `bb.bb_label = target.bb_label /\ lbl = pred.bb_label`
  >- (gvs[] >> Cases_on `ALOOKUP repls v` >> gvs[]
      >- metis_tac[cfgNormBaseTheory.phi_pairs_mem_var] >>
      disj2_tac >> qexists `x` >>
      `MEM pred.bb_label (reachable_preds fn target.bb_label)` by
        (qpat_x_assum `MEM (_,v) (phi_pairs inst.inst_operands)` mp_tac >>
         simp[reachable_inst_def, filter_phi_ops_pairs, listTheory.MEM_FILTER]) >>
      gvs[reachable_preds_def, listTheory.MEM_FILTER] >>
      metis_tac[alistTheory.ALOOKUP_MEM, cfgNormBaseTheory.phi_pairs_mem_var]) >>
  gvs[] >> metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]
QED

Finalise insert_split_supply_reachable_phi_forward

Theorem insert_split_supply_reachable_phi_backward_active:
  wf_function fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts (reachable_fn fn')) /\ inst.inst_opcode = PHI ==>
  ?i. MEM i (fn_insts (reachable_fn fn)) /\ i.inst_opcode = PHI /\
    i.inst_outputs = inst.inst_outputs /\
    (!w. MEM (Var w) inst.inst_operands ==>
      MEM (Var w) i.inst_operands \/
      ?v. MEM (v,w) repls /\ MEM (Var v) i.inst_operands /\
          fn_reachable fn pred.bb_label /\ fn_cfg_edge fn pred.bb_label target.bb_label)
Proof
  strip_tac >> drule_all insert_split_supply_reachable_inst_cases >> strip_tac
  >- (drule_all supply_split_inst_source >> simp[]) >>
  qmatch_asmsub_abbrev_tac `inst = reachable_inst fn' bb.bb_label j` >>
  qabbrev_tac `i = EL n bb.bb_instructions` >>
  `supply_inst_image pred.bb_label target.bb_label split.bb_label repls i j` by
    (simp[Abbr `i`, Abbr `j`] >> irule supply_block_image_index_image >> simp[]) >>
  `j.inst_opcode = PHI` by metis_tac[reachable_inst_fields] >>
  `i.inst_opcode = PHI /\ i.inst_outputs = j.inst_outputs` by
    metis_tac[supply_inst_image_metadata] >>
  `MEM i bb.bb_instructions` by
    (simp[Abbr `i`, listTheory.MEM_EL] >> metis_tac[]) >>
  `phi_well_formed i.inst_operands` by
    (irule (cj 1 cfgNormBaseTheory.inst_wf_phi_well_formed) >>
     gvs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed j.inst_operands` by
    (qpat_x_assum `supply_inst_image _ _ _ _ _ _` mp_tac >>
     simp[supply_inst_image_def, is_terminator_def] >>
     strip_tac >> gvs[] >> metis_tac[supply_phi_well_formed_update]) >>
  `phi_well_formed inst.inst_operands` by
    (gvs[reachable_inst_def] >>
     metis_tac[simplifyCfgStructTheory.filter_phi_ops_well_formed]) >>
  qexists `reachable_inst fn bb.bb_label i` >> simp[reachable_inst_fields] >>
  conj_tac
  >- (rewrite_tac[MEM_reachable_fn_insts] >> qexistsl [`bb`, `i`] >> simp[]) >>
  suspend "vars"
QED

Resume insert_split_supply_reachable_phi_backward_active[vars]:
  `!l v. MEM (l,v) (phi_pairs inst.inst_operands) <=>
    ?k w. MEM (k,w) (phi_pairs (reachable_inst fn bb.bb_label i).inst_operands) /\
      l = (if bb.bb_label = target.bb_label /\ k = pred.bb_label then split.bb_label else k) /\
      v = (if bb.bb_label = target.bb_label /\ k = pred.bb_label then
             (case ALOOKUP repls w of NONE => w | SOME u => u) else w)` by
    (rpt gen_tac >>
     `i = EL n bb.bb_instructions` by simp[Abbr `i`] >>
     `j = EL n (supply_block_image pred target split repls bb).bb_instructions` by
       simp[Abbr `j`] >>
     drule_all insert_split_supply_reachable_phi_pair >>
     disch_then (qspecl_then [`v`, `l`] mp_tac) >>
     qpat_x_assum `inst = reachable_inst _ _ _` SUBST_ALL_TAC >>
     disch_then MATCH_ACCEPT_TAC) >>
  rpt strip_tac >>
  `MEM (Var w) inst.inst_operands` by metis_tac[] >>
  drule_all phi_well_formed_var_pair >> strip_tac >>
  qpat_x_assum `!l v. _` (qspecl_then [`lbl`, `w`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `bb.bb_label = target.bb_label /\ k = pred.bb_label` >> gvs[]
  >- (Cases_on `ALOOKUP repls w'` >> gvs[]
      >- metis_tac[cfgNormBaseTheory.phi_pairs_mem_var] >>
      `MEM pred.bb_label (reachable_preds fn target.bb_label)` by
        (qpat_x_assum `MEM (_,w') (phi_pairs _)` mp_tac >>
         simp[reachable_inst_def, filter_phi_ops_pairs, listTheory.MEM_FILTER]) >>
      gvs[reachable_preds_def, listTheory.MEM_FILTER] >>
      metis_tac[cfgNormBaseTheory.phi_pairs_mem_var, alistTheory.ALOOKUP_MEM]) >>
  metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]
QED

Finalise insert_split_supply_reachable_phi_backward_active

Theorem insert_split_supply_reachable_phi_backward:
  wf_function fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM inst (fn_insts (reachable_fn fn')) /\ inst.inst_opcode = PHI ==>
  ?i. MEM i (fn_insts (reachable_fn fn)) /\ i.inst_opcode = PHI /\
    i.inst_outputs = inst.inst_outputs /\
    (!w. MEM (Var w) inst.inst_operands ==>
      MEM (Var w) i.inst_operands \/
      ?v. MEM (v,w) repls /\ MEM (Var v) i.inst_operands)
Proof
  strip_tac >> drule_all insert_split_supply_reachable_phi_backward_active >>
  metis_tac[]
QED

Theorem insert_split_supply_reachable_copy_phi_fresh_forward:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  fn_reachable fn pred.bb_label /\ fn_cfg_edge fn pred.bb_label target.bb_label /\
  MEM (v,w) repls /\ copy_phi_var origin (reachable_fn fn') v ==>
  copy_phi_var origin (reachable_fn fn') w
Proof
  strip_tac >> drule_all insert_split_supply_reachable_fresh_definition >> strip_tac >>
  irule copy_phi_var_assign >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem insert_split_supply_reachable_copy_phi_forward:
  !origin g x. copy_phi_var origin g x ==>
  !s fn fn' pred target split repls s'.
    g = reachable_fn fn /\ wf_function fn /\ fn_inst_wf fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
    build_split_block_supply s pred target = (split,repls,s') /\
    insert_split_supply s fn pred target = (fn',s') /\
    origin <> PHI /\ ~is_terminator origin ==>
    copy_phi_var origin (reachable_fn fn') x
Proof
  ho_match_mp_tac copy_phi_var_ind >> rpt conj_tac
  >- suspend "seed"
  >- suspend "assign"
  >> suspend "phi"
QED

Resume insert_split_supply_reachable_copy_phi_forward[seed]:
  rpt strip_tac >> gvs[] >>
  `MEM inst (fn_insts (reachable_fn fn'))` by
    (irule insert_split_supply_reachable_nonphi_forward >> metis_tac[]) >>
  irule copy_phi_var_seed >> goal_assum (drule_at Any) >> simp[]
QED

Resume insert_split_supply_reachable_copy_phi_forward[assign]:
  rpt strip_tac >> first_x_assum (drule_all_then assume_tac) >> gvs[] >>
  `MEM inst (fn_insts (reachable_fn fn'))` by
    (irule insert_split_supply_reachable_nonphi_forward >> simp[is_terminator_def] >>
     metis_tac[]) >>
  irule copy_phi_var_assign >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume insert_split_supply_reachable_copy_phi_forward[phi]:
  rpt strip_tac >> first_x_assum (drule_all_then assume_tac) >> gvs[] >>
  drule_all insert_split_supply_reachable_phi_forward >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac)
  >- (irule copy_phi_var_phi >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  `copy_phi_var origin (reachable_fn fn') w` by
    (irule insert_split_supply_reachable_copy_phi_fresh_forward >> metis_tac[]) >>
  irule copy_phi_var_phi >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise insert_split_supply_reachable_copy_phi_forward

Theorem supply_reachable_copy_phi_var_ir_var[local]:
  copy_phi_var origin (reachable_fn fn) x ==> MEM x (irSupply$fn_ir_vars fn)
Proof
  simp[Once copy_phi_var_cases] >> rpt strip_tac >>
  drule reachable_fn_insts_mem >> strip_tac >>
  irule supply_inst_output_ir_var >> goal_assum (drule_at Any) >>
  metis_tac[reachable_inst_fields]
QED

Theorem insert_split_supply_reachable_copy_phi_projection:
  !origin g x. copy_phi_var origin g x ==>
  !s fn fn' pred target split repls s'.
    g = reachable_fn fn' /\ wf_function fn /\ fn_inst_wf fn /\
    ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
    MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
    build_split_block_supply s pred target = (split,repls,s') /\
    insert_split_supply s fn pred target = (fn',s') /\
    origin <> ASSIGN /\ origin <> PHI /\ ~is_terminator origin ==>
    copy_phi_var origin (reachable_fn fn) x \/
    ?v. MEM (v,x) repls /\ copy_phi_var origin (reachable_fn fn) v
Proof
  ho_match_mp_tac copy_phi_var_ind >> rpt conj_tac
  >- suspend "seed"
  >- suspend "assign"
  >> suspend "phi"
QED

Resume insert_split_supply_reachable_copy_phi_projection[seed]:
  rpt strip_tac >> gvs[] >>
  drule_all insert_split_supply_reachable_nonphi_backward >> strip_tac >> gvs[] >>
  disj1_tac >> irule copy_phi_var_seed >> goal_assum (drule_at Any) >> simp[]
QED

Resume insert_split_supply_reachable_copy_phi_projection[assign]:
  rpt strip_tac >> first_x_assum (drule_all_then mp_tac) >> disch_tac >>
  qpat_x_assum `g = _` SUBST_ALL_TAC >>
  `inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode` by
    simp[is_terminator_def] >>
  drule_all insert_split_supply_reachable_nonphi_backward >> strip_tac
  >- (`MEM x' (irSupply$fn_ir_vars fn)` by
        (`MEM (Var x') inst.inst_operands` by simp[] >>
         qpat_assum `MEM inst (fn_insts (reachable_fn fn))`
           (mp_then Any strip_assume_tac reachable_fn_insts_operand) >>
         irule supply_inst_operand_ir_var >> metis_tac[]) >>
      `copy_phi_var origin (reachable_fn fn) x'` by
        metis_tac[supply_split_replacement_not_old] >>
      disj1_tac >> irule copy_phi_var_assign >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  `v = x' /\ w = x` by gvs[] >>
  `MEM x' (irSupply$fn_ir_vars fn)` by
    metis_tac[supply_split_replacement_source_ir_var] >>
  `copy_phi_var origin (reachable_fn fn) x'` by
    metis_tac[supply_split_replacement_not_old] >>
  disj2_tac >> qexists `x'` >> metis_tac[]
QED

Resume insert_split_supply_reachable_copy_phi_projection[phi]:
  rpt strip_tac >> first_x_assum (drule_all_then mp_tac) >> disch_tac >>
  qpat_x_assum `g = _` SUBST_ALL_TAC >>
  drule_all insert_split_supply_reachable_phi_backward >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac)
  >- (`MEM x' (irSupply$fn_ir_vars fn)` by
        (qpat_assum `MEM i (fn_insts (reachable_fn fn))`
           (mp_then Any mp_tac reachable_fn_insts_operand) >>
         disch_then (qspec_then `Var x'` mp_tac) >> simp[] >> strip_tac >>
         irule supply_inst_operand_ir_var >> metis_tac[]) >>
      `copy_phi_var origin (reachable_fn fn) x'` by
        metis_tac[supply_split_replacement_not_old] >>
      disj1_tac >> irule copy_phi_var_phi >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  `~MEM x' (irSupply$fn_ir_vars fn)` by
    metis_tac[supply_split_replacement_not_old] >>
  `copy_phi_var origin (reachable_fn fn) v` by
    metis_tac[supply_reachable_copy_phi_var_ir_var,
              supply_split_replacement_sources_unique] >>
  disj1_tac >> irule copy_phi_var_phi >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise insert_split_supply_reachable_copy_phi_projection

Theorem insert_split_supply_retpc_old_var:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM x (irSupply$fn_ir_vars fn) ==>
  (retpc_var fn' x <=> retpc_var fn x)
Proof
  simp[retpc_var_def] >> strip_tac >> eq_tac >> strip_tac
  >- (irule insert_split_supply_copy_phi_old_var >> simp[] >> metis_tac[]) >>
  irule insert_split_supply_copy_phi_forward >> simp[is_terminator_def] >> metis_tac[]
QED

Theorem insert_split_supply_retpc_replacement:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\ MEM (v,w) repls ==>
  (retpc_var fn' w <=> retpc_var fn v)
Proof
  simp[retpc_var_def] >> strip_tac >> eq_tac >> strip_tac
  >- (irule insert_split_supply_copy_phi_replacement >> simp[] >> metis_tac[]) >>
  `copy_phi_var RETPC_PARAM fn' v` by
    (irule insert_split_supply_copy_phi_forward >> simp[is_terminator_def] >> metis_tac[]) >>
  irule insert_split_supply_copy_phi_fresh_forward >> metis_tac[]
QED

Theorem insert_split_supply_reachable_retpc_old_var:
  wf_function fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  MEM x (irSupply$fn_ir_vars fn) ==>
  (retpc_var (reachable_fn fn') x <=> retpc_var (reachable_fn fn) x)
Proof
  simp[retpc_var_def] >> strip_tac >> eq_tac >> strip_tac
  >- (`copy_phi_var RETPC_PARAM (reachable_fn fn) x \/
       ?v. MEM (v,x) repls /\ copy_phi_var RETPC_PARAM (reachable_fn fn) v` by
        (irule insert_split_supply_reachable_copy_phi_projection >>
         simp[is_terminator_def] >> metis_tac[]) >>
      metis_tac[supply_split_replacement_not_old]) >>
  irule insert_split_supply_reachable_copy_phi_forward >> simp[is_terminator_def] >> metis_tac[]
QED

Theorem insert_split_supply_reachable_retpc_replacement:
  wf_function fn /\ fn_inst_wf fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,s') /\
  insert_split_supply s fn pred target = (fn',s') /\
  fn_reachable fn pred.bb_label /\ fn_cfg_edge fn pred.bb_label target.bb_label /\
  MEM (v,w) repls ==>
  (retpc_var (reachable_fn fn') w <=> retpc_var (reachable_fn fn) v)
Proof
  simp[retpc_var_def] >> strip_tac >> eq_tac >> strip_tac
  >- (`~MEM w (irSupply$fn_ir_vars fn)` by
        metis_tac[supply_split_replacement_not_old] >>
      `copy_phi_var RETPC_PARAM (reachable_fn fn) w \/
       ?u. MEM (u,w) repls /\ copy_phi_var RETPC_PARAM (reachable_fn fn) u` by
        (irule insert_split_supply_reachable_copy_phi_projection >>
         simp[is_terminator_def] >> metis_tac[]) >>
      metis_tac[supply_reachable_copy_phi_var_ir_var,
                supply_split_replacement_sources_unique]) >>
  `copy_phi_var RETPC_PARAM (reachable_fn fn') v` by
    (irule insert_split_supply_reachable_copy_phi_forward >>
     simp[is_terminator_def] >> metis_tac[]) >>
  irule insert_split_supply_reachable_copy_phi_fresh_forward >> metis_tac[]
QED

(* Allocation observes all supply fields except the used instruction-ID list. *)
Definition supply_eq_mod_ids_def:
  supply_eq_mod_ids s t <=>
    (s with irs_used_inst_ids := []) = (t with irs_used_inst_ids := [])
End

Theorem supply_eq_mod_ids_fields:
  supply_eq_mod_ids s t <=>
    s.irs_next_inst = t.irs_next_inst /\
    s.irs_next_var = t.irs_next_var /\
    s.irs_next_label = t.irs_next_label /\
    s.irs_used_vars = t.irs_used_vars /\
    s.irs_used_labels = t.irs_used_labels
Proof
  simp[supply_eq_mod_ids_def, irSupplyTheory.ir_supply_component_equality]
QED

Theorem supply_fresh_inst_id_cong:
  supply_eq_mod_ids s t /\ fresh_inst_id s = (x,s') /\
  fresh_inst_id t = (y,t') ==> x = y /\ supply_eq_mod_ids s' t'
Proof
  simp[irSupplyTheory.fresh_inst_id_def, supply_eq_mod_ids_fields] >> rpt strip_tac >> gvs[]
QED

Theorem supply_fresh_ir_var_cong:
  supply_eq_mod_ids s t /\ fresh_ir_var s = (x,s') /\
  fresh_ir_var t = (y,t') ==> x = y /\ supply_eq_mod_ids s' t'
Proof
  simp[supply_eq_mod_ids_fields, irSupplyTheory.fresh_ir_var_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> gvs[]
QED

Theorem supply_fresh_ir_label_cong:
  supply_eq_mod_ids s t /\ fresh_ir_label s = (x,s') /\
  fresh_ir_label t = (y,t') ==> x = y /\ supply_eq_mod_ids s' t'
Proof
  simp[supply_eq_mod_ids_fields, irSupplyTheory.fresh_ir_label_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> gvs[]
QED

Theorem supply_forwarding_cong:
  !vars s t rs is s' rt it t'.
    supply_eq_mod_ids s t /\
    build_forwarding_assigns_supply s vars = (rs,is,s') /\
    build_forwarding_assigns_supply t vars = (rt,it,t') ==>
    rs = rt /\ is = it /\ supply_eq_mod_ids s' t'
Proof
  Induct >- simp[build_forwarding_assigns_supply_def] >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `fresh_ir_var s` ["v ss"] >>
  namedCases_on `fresh_ir_var t` ["w tt"] >>
  `v = w /\ supply_eq_mod_ids ss tt` by
    metis_tac[supply_fresh_ir_var_cong] >> gvs[] >>
  namedCases_on `fresh_inst_id ss` ["i su"] >>
  namedCases_on `fresh_inst_id tt` ["j tu"] >>
  `i = j /\ supply_eq_mod_ids su tu` by
    metis_tac[supply_fresh_inst_id_cong] >> gvs[] >>
  namedCases_on `build_forwarding_assigns_supply su vars` ["rr ii ss1"] >>
  namedCases_on `build_forwarding_assigns_supply tu vars` ["rr' ii' tt1"] >>
  gvs[build_forwarding_assigns_supply_def] >> metis_tac[]
QED

Theorem supply_build_split_cong:
  supply_eq_mod_ids s t /\
  build_split_block_supply s p b = (bb,rs,s') /\
  build_split_block_supply t p b = (bc,rt,t') ==>
  bb = bc /\ rs = rt /\ supply_eq_mod_ids s' t'
Proof
  strip_tac >>
  namedCases_on `fresh_ir_label s` ["l ss"] >>
  namedCases_on `fresh_ir_label t` ["m tt"] >>
  `l = m /\ supply_eq_mod_ids ss tt` by
    metis_tac[supply_fresh_ir_label_cong] >> gvs[] >>
  namedCases_on `build_forwarding_assigns_supply ss
    (nub (phi_vars_needing_forward p.bb_label p b.bb_instructions))`
    ["rr ii su"] >>
  namedCases_on `build_forwarding_assigns_supply tt
    (nub (phi_vars_needing_forward p.bb_label p b.bb_instructions))`
    ["rr' ii' tu"] >>
  `rr = rr' /\ ii = ii' /\ supply_eq_mod_ids su tu` by
    metis_tac[supply_forwarding_cong] >> gvs[] >>
  namedCases_on `fresh_inst_id su` ["i ss1"] >>
  namedCases_on `fresh_inst_id tu` ["j tt1"] >>
  drule_all supply_fresh_inst_id_cong >> strip_tac >>
  gvs[build_split_block_supply_def]
QED

Theorem supply_insert_split_cong:
  supply_eq_mod_ids s t /\
  insert_split_supply s fn p b = (g,s') /\
  insert_split_supply t fn p b = (h,t') ==>
  g = h /\ supply_eq_mod_ids s' t'
Proof
  strip_tac >>
  namedCases_on `build_split_block_supply s p b` ["bb rs ss"] >>
  namedCases_on `build_split_block_supply t p b` ["bc rt tt"] >>
  drule_all supply_build_split_cong >> strip_tac >>
  gvs[insert_split_supply_def]
QED

Theorem supply_find_split_cong:
  !bbs fn s t g c s' h d t'.
    supply_eq_mod_ids s t /\
    find_and_split_supply fn s bbs = (g,c,s') /\
    find_and_split_supply fn t bbs = (h,d,t') ==>
    g = h /\ c = d /\ supply_eq_mod_ids s' t'
Proof
  Induct >- simp[find_and_split_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[]) >>
  Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[]) >>
  gvs[find_and_split_supply_def, AllCaseEqs()] >>
  metis_tac[supply_insert_split_cong]
QED

Theorem supply_round_cong:
  supply_eq_mod_ids s t /\
  cfg_norm_round_supply s fn = (g,c,s') /\
  cfg_norm_round_supply t fn = (h,d,t') ==>
  g = h /\ c = d /\ supply_eq_mod_ids s' t'
Proof
  simp[cfg_norm_round_supply_def] >> metis_tac[supply_find_split_cong]
QED

Theorem supply_iter_cong:
  !n s t fn g s' h t'.
    supply_eq_mod_ids s t /\
    cfg_norm_iter_supply n s fn = (g,s') /\
    cfg_norm_iter_supply n t fn = (h,t') ==>
    g = h /\ supply_eq_mod_ids s' t'
Proof
  Induct >- simp[cfg_norm_iter_supply_def] >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `cfg_norm_round_supply s fn` ["ff c ss"] >>
  namedCases_on `cfg_norm_round_supply t fn` ["gg d tt"] >>
  `ff = gg /\ c = d /\ supply_eq_mod_ids ss tt` by
    metis_tac[supply_round_cong] >> gvs[] >>
  Cases_on `c` >> gvs[cfg_norm_iter_supply_def] >> metis_tac[]
QED

Theorem cfg_norm_function_supply_cong:
  supply_eq_mod_ids s t /\
  cfg_norm_function_supply s fn = (g,s') /\
  cfg_norm_function_supply t fn = (h,t') ==>
  g = h /\ supply_eq_mod_ids s' t'
Proof
  simp[cfg_norm_function_supply_def] >> metis_tac[supply_iter_cong]
QED
