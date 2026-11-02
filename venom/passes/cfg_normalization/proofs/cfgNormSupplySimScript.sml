Theory cfgNormSupplySim
Ancestors
  cfgNormSupplyProofs cfgTransformProps cfgNormDefs cfgTransform venomExecProps venomInst venomWf
  sccpCorrectnessProofs finite_map

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
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
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
