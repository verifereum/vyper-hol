Theory simplifyCfgReachuses
Ancestors
  simplifyCfgDefs simplifyCfgStruct simplifyCfgPhiRepair
  simplifyCfgDataflow simplifyCfgRepairDataflow simplifyCfgPhiPreds
  simplifyCfgChainDataflow simplifyCfgBypassDataflow
  venomInst venomWf venomExecProofs cfgTransform list rich_list

Theorem fix_phi_inst_inst_wf:
  inst_wf inst ==> inst_wf (fix_phi_inst actual_preds inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- ( `LENGTH inst.inst_outputs = 1 /\ phi_well_formed inst.inst_operands` by
         fs[inst_wf_def] >>
       `phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)` by
         simp[filter_phi_ops_well_formed] >>
       simp[fix_phi_inst_def] >>
       Cases_on `filter_phi_ops actual_preds inst.inst_operands` >>
       simp[inst_wf_def] >>
       Cases_on `t` >> simp[inst_wf_def] >>
       Cases_on `t'` >> simp[inst_wf_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem fix_all_phis_fn_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (fix_all_phis fn)
Proof
  simp[fn_inst_wf_def, fix_all_phis_def, fix_phis_in_block_def,
       MEM_MAP, MEM_APPEND, MEM_FILTER, PULL_EXISTS] >>
  metis_tac[fix_phi_inst_inst_wf]
QED

Theorem remove_unreachable_blocks_fn_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (remove_unreachable_blocks fn)
Proof
  simp[fn_inst_wf_def, remove_unreachable_blocks_def] >>
  Cases_on `fn_entry_label fn` >> simp[MEM_FILTER] >> metis_tac[]
QED

Theorem repair_reachable_invariants:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn ==>
  wf_function (fix_all_phis (remove_unreachable_blocks fn)) /\
  fn_inst_wf (fix_all_phis (remove_unreachable_blocks fn)) /\
  first_block_no_preds (fix_all_phis (remove_unreachable_blocks fn)) /\
  scfg_phi_safe (fix_all_phis (remove_unreachable_blocks fn)) /\
  fn_defs_reach_uses (fix_all_phis (remove_unreachable_blocks fn)) /\
  scfg_phi_preds (fix_all_phis (remove_unreachable_blocks fn)) /\
  all_reachable (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >>
  `wf_function (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_wf] >>
  `fn_inst_wf (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_fn_inst_wf] >>
  `first_block_no_preds (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_first_block_no_preds] >>
  `scfg_phi_safe (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_phi_safe] >>
  `fn_defs_reach_uses (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_defs_reach_uses] >>
  `all_reachable (remove_unreachable_blocks fn)` by
    simp[remove_unreachable_blocks_reachable] >>
  simp[fix_all_phis_wf, fix_all_phis_fn_inst_wf,
       fix_all_phis_first_block_no_preds, fix_all_phis_phi_safe,
       fix_all_phis_defs_reach_uses, fix_all_phis_phi_preds,
       fix_all_phis_all_reachable]
QED

Theorem phi_pairs_subst_equal_source:
  phi_well_formed ops /\ phi_well_formed ops' /\
  MAP (subst_label_op old new) ops' = MAP (subst_label_op old new) ops /\
  MEM (p,v) (phi_pairs ops') /\ p <> old ==>
  ?q. MEM (q,v) (phi_pairs ops) /\
      p = (if q = old then new else q)
Proof
  strip_tac >>
  `MEM (if p = old then new else p, v)
    (phi_pairs (MAP (subst_label_op old new) ops'))` by
    (simp[phi_pairs_subst_label_ops, MEM_MAP] >>
     qexists `(p,v)` >> simp[]) >>
  `MEM (p,v) (phi_pairs (MAP (subst_label_op old new) ops))` by
    metis_tac[] >>
  qpat_x_assum `MEM _ (phi_pairs (MAP _ ops))` mp_tac >>
  simp[phi_pairs_subst_label_ops, MEM_MAP] >>
  disch_then (qx_choose_then `pair` strip_assume_tac) >>
  PairCases_on `pair` >> gvs[] >> metis_tac[]
QED

Theorem chain_merge_phi_pair_source:
  wf_function fn /\ fn_inst_wf fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  MEM bb' fn'.fn_blocks /\ MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs phi.inst_operands) /\ p <> b.bb_label ==>
  ?bb inst q. MEM bb fn.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    MEM (q,v) (phi_pairs inst.inst_operands) /\
    p = (if q = b.bb_label then a.bb_label else q)
Proof
  strip_tac >>
  `fn_inst_wf fn'` by metis_tac[chain_merge_fn_inst_wf] >>
  `?bb inst. MEM bb fn.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    subst_label_inst b.bb_label a.bb_label phi =
    subst_label_inst b.bb_label a.bb_label inst` by
    (irule chain_merge_phi_source >> gvs[]) >>
  `inst_wf phi /\ inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed phi.inst_operands /\ phi_well_formed inst.inst_operands` by
    (qpat_x_assum `inst_wf phi` mp_tac >>
     qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def]) >>
  `MAP (subst_label_op b.bb_label a.bb_label) phi.inst_operands =
   MAP (subst_label_op b.bb_label a.bb_label) inst.inst_operands` by
    fs[subst_label_inst_def, instruction_component_equality] >>
  drule_all phi_pairs_subst_equal_source >> strip_tac >>
  qexistsl [`bb`, `inst`, `q`] >> simp[]
QED

Theorem chain_merge_phi_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  fn_defs_reach_uses fn /\ scfg_phi_preds fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  MEM bb' fn'.fn_blocks /\ MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs phi.inst_operands) /\
  MEM pred' fn'.fn_blocks /\ pred'.bb_label = p ==>
  def_on_all_paths fn' pred' NONE v
Proof
  strip_tac >>
  `MEM p (fn_labels fn')` by
    (pure_rewrite_tac[fn_labels_def, MEM_MAP] >> qexists `pred'` >> simp[]) >>
  `p <> b.bb_label` by gvs[chain_merge_fn_labels, MEM_FILTER] >>
  drule_all chain_merge_phi_pair_source >> strip_tac >>
  `fn_cfg_edge fn q bb.bb_label` by metis_tac[scfg_phi_preds_edge] >>
  `?pred. MEM pred fn.fn_blocks /\ pred.bb_label = q` by
    (fs[fn_cfg_edge_def] >> metis_tac[]) >>
  `def_on_all_paths fn pred NONE v` by
    (qpat_x_assum `fn_defs_reach_uses fn` mp_tac >>
     simp[fn_defs_reach_uses_def] >>
     disch_then (qspecl_then [`bb`, `inst`] mp_tac) >> simp[] >>
     disch_then (qspec_then `pred` mp_tac) >> simp[]) >>
  irule chain_merge_def_on_all_paths_endpoint >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem chain_merge_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  fn_defs_reach_uses fn /\ scfg_phi_preds fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) ==>
  fn_defs_reach_uses fn'
Proof
  strip_tac >> pure_rewrite_tac[fn_defs_reach_uses_def] >>
  rpt gen_tac >> strip_tac >> IF_CASES_TAC >> rpt strip_tac
  >- (drule_all chain_merge_phi_defs_reach_uses >> simp[]) >>
  drule_all chain_merge_ordinary_defs_reach_uses >> simp[]
QED

Theorem lookup_replace_label_map:
  !bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  (case lookup_block lbl bbs of
     NONE => bbs
   | SOME bb => replace_block lbl (f bb) bbs) =
  MAP (\bb. if bb.bb_label = lbl then f bb else bb) bbs
Proof
  Induct >> simp[lookup_block_def, FIND_thm, replace_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> gvs[]
  >- (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
      `MEM (EL x bbs) bbs` by simp[EL_MEM] >>
      `((EL x bbs).bb_label <> h.bb_label)` by
        (fs[MEM_MAP] >> metis_tac[]) >> simp[]) >>
  Cases_on `FIND (\bb. bb.bb_label = lbl) bbs` >>
  gvs[replace_block_def, lookup_block_def]
QED

Theorem update_succ_phi_labels_exact:
  !succs bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  update_succ_phi_labels old new bbs succs =
  MAP (\bb. if MEM bb.bb_label succs then
    bb with bb_instructions := MAP (\i. if i.inst_opcode <> PHI then i
      else subst_label_inst old new i) bb.bb_instructions
    else bb) bbs
Proof
  pure_rewrite_tac[update_succ_phi_labels_def, LET_THM] >>
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  ` (case lookup_block h bbs of NONE => bbs | SOME bb =>
      replace_block h (bb with bb_instructions :=
        MAP (\i. if i.inst_opcode <> PHI then i else subst_label_inst old new i)
          bb.bb_instructions) bbs) =
    MAP (\bb. if bb.bb_label = h then bb with bb_instructions :=
      MAP (\i. if i.inst_opcode <> PHI then i else subst_label_inst old new i)
        bb.bb_instructions else bb) bbs` by
    (ho_match_mp_tac lookup_replace_label_map >> simp[]) >>
  asm_rewrite_tac[] >>
  first_x_assum (qspec_then `MAP (\bb. if bb.bb_label = h then
    bb with bb_instructions := MAP (\i. if i.inst_opcode <> PHI then i
      else subst_label_inst old new i) bb.bb_instructions else bb) bbs` mp_tac) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  impl_tac
  >- (`MAP (\bb. if bb.bb_label = h then h else bb.bb_label) bbs =
        MAP (\bb. bb.bb_label) bbs` by
        (irule MAP_CONG >> simp[] >> rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
      simp[COND_RAND, COND_RATOR]) >>
  disch_then SUBST1_TAC >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >> rename1 `MEM bb bbs` >>
  Cases_on `bb.bb_label = h` >> gvs[] >>
  Cases_on `MEM bb.bb_label succs` >> gvs[] >>
  simp[basic_block_component_equality, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  rename1 `MEM i bb.bb_instructions` >> Cases_on `i.inst_opcode = PHI` >>
  `(subst_label_inst old new i).inst_opcode = i.inst_opcode` by
    simp[subst_label_inst_def] >>
  simp[subst_label_inst_idempotent]
QED

Theorem chain_merge_base_phi_source:
  MEM a fn.fn_blocks /\ can_merge_blocks fn a b /\
  MEM bb' (replace_block a.bb_label (merge_blocks a b)
    (remove_block b.bb_label fn.fn_blocks)) /\
  MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI ==>
  ?bb. MEM bb fn.fn_blocks /\ bb'.bb_label = bb.bb_label /\
       MEM phi bb.bb_instructions
Proof
  strip_tac >>
  fs[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
  Cases_on `bb.bb_label = a.bb_label` >> gvs[merge_blocks_def, MEM_APPEND]
  >- (qexists `a` >> simp[] >>
      Cases_on `a.bb_instructions` >> fs[] >> drule MEM_FRONT >> simp[])
  >- (fs[can_merge_blocks_def, no_phis_def, EVERY_MEM] >> metis_tac[]) >>
  qexists `bb` >> simp[]
QED

Theorem chain_merge_phi_pair_not_removed:
  wf_function fn /\ fn_inst_wf fn /\ scfg_phi_preds fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  MEM bb' fn'.fn_blocks /\ MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs phi.inst_operands) ==> p <> b.bb_label
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)))` by
    (irule chain_merge_base_labels >> fs[wf_function_def]) >>
  qpat_x_assum `MEM bb' fn'.fn_blocks` mp_tac >>
  asm_rewrite_tac[] >> simp[update_succ_phi_labels_exact, MEM_MAP] >>
  disch_then (qx_choose_then `srcbb` strip_assume_tac) >>
  Cases_on `MEM srcbb.bb_label (bb_succs (merge_blocks a b))` >> gvs[]
  >- suspend "targeted" >>
  suspend "untargeted"
QED

Resume chain_merge_phi_pair_not_removed[targeted]:
  qpat_x_assum `MEM phi (MAP _ _)` mp_tac >> simp[MEM_MAP] >>
  disch_then (qx_choose_then `orig` strip_assume_tac) >>
  Cases_on `orig.inst_opcode = PHI` >> gvs[subst_label_inst_def] >>
  `?bb. MEM bb fn.fn_blocks /\ srcbb.bb_label = bb.bb_label /\
        MEM orig bb.bb_instructions` by
    metis_tac[chain_merge_base_phi_source] >>
  `inst_wf orig` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed orig.inst_operands` by
    (qpat_x_assum `inst_wf orig` mp_tac >> simp[inst_wf_def]) >>
  fs[phi_pairs_subst_label_ops, MEM_MAP] >>
  rename1 `MEM pair (phi_pairs orig.inst_operands)` >>
  Cases_on `FST pair = b.bb_label` >> gvs[can_merge_blocks_def]
QED

Resume chain_merge_phi_pair_not_removed[untargeted]:
  strip_tac >> gvs[] >>
  drule_all chain_merge_base_phi_source >> strip_tac >>
  `fn_cfg_edge fn b.bb_label bb.bb_label` by
    metis_tac[scfg_phi_preds_edge] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `MEM bb.bb_label (bb_succs b)` by
    (fs[fn_cfg_edge_def] >> metis_tac[same_label_same_block]) >>
  `b.bb_instructions <> []` by
    (Cases_on `b.bb_instructions` >> fs[bb_succs_def]) >>
  fs[bb_succs_merge_blocks]
QED

Finalise chain_merge_phi_pair_not_removed
