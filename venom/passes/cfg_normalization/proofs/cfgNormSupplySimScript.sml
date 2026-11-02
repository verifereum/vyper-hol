Theory cfgNormSupplySim
Ancestors
  cfgNormSupplyProofs cfgTransformProps cfgNormDefs cfgTransform venomExecProps venomInst venomWf

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
