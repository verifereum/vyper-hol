Theory cfgNormSupplySim
Ancestors
  cfgNormSupplyProofs cfgTransformProps cfgNormDefs cfgTransform venomExecProps venomInst venomWf
  sccpCorrectnessProofs finite_map venomFnScheduleRunner

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
    (rpt gen_tac >> drule_all insert_split_supply_cfg_edges >> simp[]) >>
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
  drule_all cfgNormBaseTheory.wf_function_block_inst_ids_distinct >>
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
