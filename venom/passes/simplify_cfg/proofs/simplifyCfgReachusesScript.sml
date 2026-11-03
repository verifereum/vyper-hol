Theory simplifyCfgReachuses
Ancestors
  simplifyCfgDefs simplifyCfgStruct simplifyCfgPhiRepair simplifyCfgLabelProps
  simplifyCfgDataflow simplifyCfgRepairDataflow simplifyCfgPhiPreds
  simplifyCfgChainDataflow simplifyCfgBypassDataflow
  unitShapeDefs stackPlanTypes venomInst venomWf venomExecSemantics venomExecProofs cfgTransform cfgTransformProps cfgTransformInstWf list rich_list

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

Theorem chain_merge_phi_preds:
  wf_function fn /\ fn_inst_wf fn /\ scfg_phi_preds fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) ==> scfg_phi_preds fn'
Proof
  strip_tac >> pure_rewrite_tac[scfg_phi_preds_def] >> rpt strip_tac >>
  `p <> b.bb_label` by metis_tac[chain_merge_phi_pair_not_removed] >>
  drule_all chain_merge_phi_pair_source >> strip_tac >>
  `fn_cfg_edge fn q bb.bb_label` by metis_tac[scfg_phi_preds_edge] >>
  `bb.bb_label <> b.bb_label` by
    ( `MEM bb.bb_label (fn_labels fn')` by
        (pure_rewrite_tac[fn_labels_def, MEM_MAP] >> qexists `bb` >> simp[]) >>
      gvs[chain_merge_fn_labels, MEM_FILTER]) >>
  Cases_on `q = b.bb_label`
  >- (gvs[] >> simp[chain_merge_edge]) >>
  `q <> a.bb_label` by
    (strip_tac >> gvs[fn_cfg_edge_def] >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
       fs[wf_function_def, fn_labels_def] >>
     `bb'' = a` by metis_tac[same_label_same_block] >>
     gvs[can_merge_blocks_def]) >>
  gvs[] >> drule_all chain_merge_edge >> simp[]
QED

Theorem do_merge_jump_fn_inst_wf:
  wf_function fn /\ fn_inst_wf fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==> fn_inst_wf fn'
Proof
  strip_tac >> pure_rewrite_tac[fn_inst_wf_def] >> rpt strip_tac >>
  drule_all do_merge_jump_block_map >> strip_tac >>
  qpat_x_assum `MEM inst _` mp_tac >> asm_rewrite_tac[] >>
  simp[MEM_MAP] >> disch_then (qx_choose_then `orig` strip_assume_tac) >>
  `inst_wf orig` by metis_tac[fn_inst_wf_def] >>
  Cases_on `bb'.bb_label = a.bb_label` >>
  Cases_on `target = a.bb_label` >>
  Cases_on `bb'.bb_label = target` >>
  Cases_on `is_terminator orig.inst_opcode` >>
  gvs[inst_wf_update_phi_bypass, inst_wf_canon_jnz_inst, inst_wf_subst_label_inst]
QED

Theorem chain_merge_reachable_input:
  wf_function fn /\ first_block_no_preds fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  MEM z (fn_labels fn) /\
  fn_reachable fn' (if z = b.bb_label then a.bb_label else z) ==>
  fn_reachable fn z
Proof
  strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[chain_merge_entry] >>
  qpat_x_assum `fn_reachable fn' _` mp_tac >>
  pure_rewrite_tac[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM (LAST path) (fn_labels fn')` by
    (gvs[chain_merge_fn_labels, MEM_FILTER] >>
     Cases_on `z = b.bb_label` >> gvs[fn_labels_def, MEM_MAP, can_merge_blocks_def] >>
     metis_tac[]) >>
  drule_all chain_merge_endpoint_path_input >> strip_tac >>
  qexists `entry` >> simp[] >>
  qpat_x_assum `is_fn_path fn' _` kall_tac >>
  `chain_prefix a.bb_label b.bb_label path ++
     (if z = b.bb_label then [a.bb_label;b.bb_label] else [z]) <> []` by
    (Cases_on `z = b.bb_label` >> simp[]) >>
  drule_all is_fn_path_rtc >>
  Cases_on `z = b.bb_label` >> gvs[]
QED

Theorem do_merge_jump_reachable_input:
  wf_function fn /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM z (fn_labels fn') /\ fn_reachable fn' z ==> fn_reachable fn z
Proof
  strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[do_merge_jump_entry] >>
  qpat_x_assum `fn_reachable fn' _` mp_tac >>
  pure_rewrite_tac[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM (LAST path) (fn_labels fn')` by simp[] >>
  drule_all do_merge_jump_path_input >> strip_tac >>
  qexists `entry` >> simp[] >>
  qpat_x_assum `is_fn_path fn' _` kall_tac >>
  drule_all is_fn_path_rtc >> gvs[]
QED

Theorem do_merge_jump_reachable_block_map:
  wf_function fn /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb' fn'.fn_blocks /\ fn_reachable fn' bb'.bb_label ==>
  ?bb target. MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_label <> b.bb_label /\ bb_succs b = [target] /\
    bb'.bb_label = bb.bb_label /\
    bb'.bb_instructions = MAP (\inst.
      if bb.bb_label = a.bb_label then
        (if target = a.bb_label then update_phi_bypass a.bb_label b.bb_label else I)
          (if ~is_terminator inst.inst_opcode then inst
           else canon_jnz_inst (subst_label_inst b.bb_label target inst))
      else if bb.bb_label = target then update_phi_bypass a.bb_label b.bb_label inst
      else inst) bb.bb_instructions
Proof
  strip_tac >>
  `fn_reachable fn bb'.bb_label` by
    (irule do_merge_jump_reachable_input >>
     goal_assum (drule_at Any) >> simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  drule_all do_merge_jump_block_map >> strip_tac >>
  qexistsl [`bb`, `target`] >> gvs[]
QED

Theorem do_merge_jump_reachable_inst_origin:
  wf_function fn /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb' fn'.fn_blocks /\ fn_reachable fn' bb'.bb_label /\
  MEM inst' bb'.bb_instructions ==>
  ?bb inst target. MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_label <> b.bb_label /\ bb_succs b = [target] /\
    bb'.bb_label = bb.bb_label /\ MEM inst bb.bb_instructions /\
    inst'.inst_outputs = inst.inst_outputs /\
    (inst'.inst_opcode = PHI <=> inst.inst_opcode = PHI) /\
    inst' = (if bb.bb_label = a.bb_label then
        (if target = a.bb_label then update_phi_bypass a.bb_label b.bb_label else I)
          (if ~is_terminator inst.inst_opcode then inst
           else canon_jnz_inst (subst_label_inst b.bb_label target inst))
      else if bb.bb_label = target then update_phi_bypass a.bb_label b.bb_label inst
      else inst)
Proof
  strip_tac >> drule_all do_merge_jump_reachable_block_map >>
  disch_then (qx_choose_then `bb` (qx_choose_then `target` strip_assume_tac)) >>
  qpat_x_assum `MEM inst' _` mp_tac >> asm_rewrite_tac[] >>
  simp[MEM_MAP] >> disch_then (qx_choose_then `inst` strip_assume_tac) >>
  qexistsl [`bb`, `inst`] >> simp[] >>
  Cases_on `bb.bb_label = a.bb_label` >>
  Cases_on `target = a.bb_label` >> Cases_on `bb.bb_label = target` >>
  Cases_on `is_terminator inst.inst_opcode` >>
  gvs[update_phi_bypass_shape, canon_jnz_inst_shape, subst_label_inst_shape,
      combinTheory.I_DEF, is_terminator_def]
QED

Theorem chain_merge_base_inst_origin:
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  MEM bb' (replace_block a.bb_label (merge_blocks a b)
    (remove_block b.bb_label fn.fn_blocks)) /\ MEM inst bb'.bb_instructions ==>
  ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    bb'.bb_label = (if bb.bb_label = b.bb_label then a.bb_label else bb.bb_label)
Proof
  strip_tac >>
  fs[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
  Cases_on `bb.bb_label = a.bb_label` >> gvs[merge_blocks_def, MEM_APPEND]
  >- (qexists `a` >> simp[can_merge_blocks_def] >>
      Cases_on `a.bb_instructions` >> fs[] >> drule MEM_FRONT >> simp[])
  >- (qexists `b` >> simp[] >> fs[can_merge_blocks_def]) >>
  qexists `bb` >> simp[]
QED

Theorem chain_merge_reachable_inst_origin:
  wf_function fn /\ first_block_no_preds fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  MEM bb' fn'.fn_blocks /\ fn_reachable fn' bb'.bb_label /\
  MEM inst' bb'.bb_instructions ==>
  ?bb inst. MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    MEM inst bb.bb_instructions /\
    bb'.bb_label = (if bb.bb_label = b.bb_label then a.bb_label else bb.bb_label) /\
    inst'.inst_outputs = inst.inst_outputs /\ inst'.inst_opcode = inst.inst_opcode /\
    inst' = (if MEM bb'.bb_label (bb_succs (merge_blocks a b)) /\ inst.inst_opcode = PHI
             then subst_label_inst b.bb_label a.bb_label inst else inst)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)))` by
    (irule chain_merge_base_labels >> fs[wf_function_def]) >>
  qpat_x_assum `MEM bb' fn'.fn_blocks` mp_tac >>
  asm_rewrite_tac[] >> simp[update_succ_phi_labels_exact, MEM_MAP] >>
  disch_then (qx_choose_then `src` strip_assume_tac) >>
  Cases_on `MEM src.bb_label (bb_succs (merge_blocks a b))` >> gvs[]
  >- suspend "updated"
  >> suspend "unchanged"
QED

Resume chain_merge_reachable_inst_origin[updated]:
  qpat_x_assum `MEM inst' _` mp_tac >> simp[MEM_MAP] >>
  disch_then (qx_choose_then `inst` strip_assume_tac) >>
  drule_all chain_merge_base_inst_origin >> strip_tac >>
  `fn_reachable fn bb.bb_label` by
    (irule chain_merge_reachable_input >> goal_assum (drule_at Any) >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  qexistsl [`bb`, `inst`] >> simp[] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[subst_label_inst_shape]
QED

Resume chain_merge_reachable_inst_origin[unchanged]:
  drule_all chain_merge_base_inst_origin >> strip_tac >>
  `fn_reachable fn bb.bb_label` by
    (irule chain_merge_reachable_input >> goal_assum (drule_at Any) >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  qexists `bb` >> simp[]
QED

Finalise chain_merge_reachable_inst_origin

Theorem do_merge_jump_entry_no_phi:
  wf_function fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  EVERY (\inst. inst.inst_opcode <> PHI) (HD fn'.fn_blocks).bb_instructions
Proof
  strip_tac >>
  `wf_function fn'` by metis_tac[do_merge_jump_wf] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[do_merge_jump_entry] >>
  `fn.fn_blocks <> [] /\ fn'.fn_blocks <> []` by
    fs[wf_function_def, fn_has_entry_def] >>
  `MEM (HD fn'.fn_blocks) fn'.fn_blocks /\
   fn_reachable fn' (HD fn'.fn_blocks).bb_label` by
    (Cases_on `fn'.fn_blocks` >>
     gvs[fn_reachable_def, fn_entry_label_def, entry_block_def]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all do_merge_jump_reachable_inst_origin >> strip_tac >>
  `bb.bb_label = (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `bb = HD fn.fn_blocks` by
    (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  gvs[scfg_phi_safe_def, EVERY_MEM] >> metis_tac[]
QED

Theorem chain_merge_entry_no_phi:
  wf_function fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) ==>
  EVERY (\inst. inst.inst_opcode <> PHI) (HD fn'.fn_blocks).bb_instructions
Proof
  strip_tac >>
  `lookup_block a.bb_label fn.fn_blocks = SOME a /\
   lookup_block b.bb_label fn.fn_blocks = SOME b` by
    (fs[wf_function_def, fn_labels_def] >> metis_tac[MEM_lookup_block]) >>
  `wf_function fn'` by metis_tac[chain_merge_wf] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[chain_merge_entry] >>
  `fn.fn_blocks <> [] /\ fn'.fn_blocks <> []` by
    fs[wf_function_def, fn_has_entry_def] >>
  `MEM (HD fn'.fn_blocks) fn'.fn_blocks /\
   fn_reachable fn' (HD fn'.fn_blocks).bb_label` by
    (Cases_on `fn'.fn_blocks` >>
     gvs[fn_reachable_def, fn_entry_label_def, entry_block_def]) >>
  pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> rpt strip_tac >>
  drule_all chain_merge_reachable_inst_origin >> strip_tac >>
  `bb.bb_label <> b.bb_label` by
    (strip_tac >>
     `bb = b` by
       (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
     gvs[can_merge_blocks_def, no_phis_def, EVERY_MEM]) >>
  `bb.bb_label = (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `bb = HD fn.fn_blocks` by
    (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  gvs[scfg_phi_safe_def, EVERY_MEM] >> metis_tac[]
QED

Theorem chain_merge_phi_output_unique:
  wf_function fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  MEM bb fn'.fn_blocks /\ fn_reachable fn' bb.bb_label /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\ MEM v inst.inst_outputs /\
  MEM bb' fn'.fn_blocks /\ fn_reachable fn' bb'.bb_label /\
  MEM inst' bb'.bb_instructions /\ MEM v inst'.inst_outputs ==> inst' = inst
Proof
  strip_tac >> drule_all chain_merge_reachable_inst_origin >>
  disch_then (qx_choose_then `src` (qx_choose_then `orig` strip_assume_tac)) >>
  qpat_x_assum `MEM inst' bb'.bb_instructions` kall_tac >>
  drule_all chain_merge_reachable_inst_origin >>
  disch_then (qx_choose_then `src2` (qx_choose_then `orig2` strip_assume_tac)) >>
  `orig = orig2` by metis_tac[scfg_phi_safe_unique_output] >>
  `src = src2` by metis_tac[wf_function_instruction_block] >>
  gvs[]
QED

Theorem do_merge_jump_phi_output_unique:
  wf_function fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb fn'.fn_blocks /\ fn_reachable fn' bb.bb_label /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\ MEM v inst.inst_outputs /\
  MEM bb' fn'.fn_blocks /\ fn_reachable fn' bb'.bb_label /\
  MEM inst' bb'.bb_instructions /\ MEM v inst'.inst_outputs ==> inst' = inst
Proof
  strip_tac >> drule_all do_merge_jump_reachable_inst_origin >>
  disch_then (qx_choose_then `src` (qx_choose_then `orig`
    (qx_choose_then `target` strip_assume_tac))) >>
  qpat_x_assum `MEM inst' bb'.bb_instructions` kall_tac >>
  drule_all do_merge_jump_reachable_inst_origin >>
  disch_then (qx_choose_then `src2` (qx_choose_then `orig2`
    (qx_choose_then `target2` strip_assume_tac))) >>
  `orig = orig2` by metis_tac[scfg_phi_safe_unique_output] >>
  `src = src2` by metis_tac[wf_function_instruction_block] >>
  gvs[]
QED

Theorem resolve_phi_subst_exists:
  !ops. phi_well_formed ops /\ resolve_phi p ops = SOME value ==>
  ?op. resolve_phi (if p = old then new else p)
    (MAP (subst_label_op old new) ops) = SOME op
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def, subst_label_op_def] >>
  rpt strip_tac >>
  Cases_on `lbl = p` >> Cases_on `lbl = old` >> Cases_on `p = old` >>
  gvs[resolve_phi_def] >> metis_tac[]
QED

Theorem chain_merge_phi_coverage:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  MEM bb fn'.fn_blocks /\ fn_reachable fn' bb.bb_label /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM pred fn'.fn_blocks /\ fn_reachable fn' pred.bb_label /\
  MEM bb.bb_label (bb_succs pred) ==>
  ?op. resolve_phi pred.bb_label inst.inst_operands = SOME op
Proof
  strip_tac >> drule_all chain_merge_reachable_inst_origin >>
  disch_then (qx_choose_then `src` (qx_choose_then `orig` strip_assume_tac)) >>
  `orig.inst_opcode = PHI` by metis_tac[] >>
  `src.bb_label <> b.bb_label` by
    (strip_tac >>
     `src = b` by
       (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
     gvs[can_merge_blocks_def, no_phis_def, EVERY_MEM]) >>
  `bb.bb_label = src.bb_label` by metis_tac[] >>
  `pred.bb_label <> b.bb_label` by
    (`MEM pred.bb_label (fn_labels fn')` by
       (pure_rewrite_tac[fn_labels_def, MEM_MAP] >> qexists `pred` >> simp[]) >>
     gvs[chain_merge_fn_labels, MEM_FILTER]) >>
  `fn_cfg_edge fn' pred.bb_label bb.bb_label` by
    (pure_rewrite_tac[fn_cfg_edge_def] >> qexists `pred` >> simp[]) >>
  `if pred.bb_label = a.bb_label then fn_cfg_edge fn b.bb_label src.bb_label
   else fn_cfg_edge fn pred.bb_label src.bb_label` by
    metis_tac[chain_merge_edge] >>
  `inst_wf orig` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed orig.inst_operands` by
    (qpat_x_assum `inst_wf orig` mp_tac >> simp[inst_wf_def]) >>
  Cases_on `pred.bb_label = a.bb_label`
  >- suspend "merged_predecessor"
  >> suspend "retained_predecessor"
QED

Resume chain_merge_phi_coverage[merged_predecessor]:
  `b.bb_instructions <> []` by metis_tac[wf_function_def, bb_well_formed_def] >>
  `fn_reachable fn b.bb_label` by
    (irule chain_merge_reachable_input >> goal_assum (drule_at Any) >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM src.bb_label (bb_succs b)` by
    (qpat_x_assum `fn_cfg_edge fn' _ _` kall_tac >>
     gvs[fn_cfg_edge_def] >>
     `bb' = b` by
       (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
     gvs[]) >>
  `?op. resolve_phi b.bb_label orig.inst_operands = SOME op` by
    metis_tac[scfg_phi_safe_coverage] >>
  drule_all resolve_phi_subst_exists >>
  disch_then (qspecl_then [`b.bb_label`, `a.bb_label`] mp_tac) >>
  gvs[bb_succs_merge_blocks, subst_label_inst_def]
QED

Resume chain_merge_phi_coverage[retained_predecessor]:
  `fn_cfg_edge fn pred.bb_label src.bb_label` by metis_tac[] >>
  qpat_x_assum `fn_cfg_edge fn _ _` mp_tac >>
  pure_rewrite_tac[fn_cfg_edge_def] >>
  disch_then (qx_choose_then `psrc` strip_assume_tac) >>
  `fn_reachable fn psrc.bb_label` by
    (irule chain_merge_reachable_input >> goal_assum (drule_at Any) >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `?op. resolve_phi pred.bb_label orig.inst_operands = SOME op` by
    metis_tac[scfg_phi_safe_coverage] >>
  Cases_on `MEM bb.bb_label (bb_succs (merge_blocks a b))`
  >- (drule_all resolve_phi_subst_exists >>
      disch_then (qspecl_then [`b.bb_label`, `a.bb_label`] mp_tac) >>
      gvs[subst_label_inst_def]) >>
  gvs[]
QED

Finalise chain_merge_phi_coverage

Theorem resolve_phi_remove_present:
  !ops. phi_well_formed ops /\ MEM (Label a) ops /\ a <> b ==>
  ?op. resolve_phi a (remove_phi_label b ops) = SOME op
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, remove_phi_label_def, resolve_phi_def] >>
  rpt strip_tac >> Cases_on `lbl = b` >> Cases_on `lbl = a` >>
  fs[] >> simp[Once resolve_phi_def] >> metis_tac[]
QED

Theorem resolve_phi_update_bypass_exists:
  inst.inst_opcode = PHI /\ phi_well_formed inst.inst_operands /\ a <> b /\ p <> b /\
  resolve_phi q inst.inst_operands = SOME value /\
  p = (if q = b then a else q) ==>
  ?op. resolve_phi p (update_phi_bypass a b inst).inst_operands = SOME op
Proof
  strip_tac >> Cases_on `MEM (Label a) inst.inst_operands` >>
  simp[update_phi_bypass_def]
  >- (Cases_on `p = a`
      >- metis_tac[resolve_phi_remove_present] >>
      `q = p` by (Cases_on `q = b` >> gvs[]) >>
      metis_tac[resolve_phi_remove_other]) >>
  `MAP (\op. case op of Label l => if l = b then Label a else Label l | _ => op)
      inst.inst_operands = MAP (subst_label_op b a) inst.inst_operands` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >> rename1 `MEM operand inst.inst_operands` >>
     Cases_on `operand` >> simp[subst_label_op_def]) >>
  asm_rewrite_tac[] >> metis_tac[resolve_phi_subst_exists]
QED

Theorem do_merge_jump_phi_coverage:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb fn'.fn_blocks /\ fn_reachable fn' bb.bb_label /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM pred fn'.fn_blocks /\ fn_reachable fn' pred.bb_label /\
  MEM bb.bb_label (bb_succs pred) ==>
  ?op. resolve_phi pred.bb_label inst.inst_operands = SOME op
Proof
  strip_tac >> drule_all do_merge_jump_reachable_inst_origin >>
  disch_then (qx_choose_then `src` (qx_choose_then `orig`
    (qx_choose_then `target` strip_assume_tac))) >>
  `orig.inst_opcode = PHI` by metis_tac[] >>
  `inst = (if src.bb_label = target then update_phi_bypass a.bb_label b.bb_label orig
           else orig)` by
    (Cases_on `src.bb_label = a.bb_label` >> Cases_on `target = a.bb_label` >>
     Cases_on `src.bb_label = target` >> gvs[is_terminator_def]) >>
  `inst_wf orig` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed orig.inst_operands` by
    (qpat_x_assum `inst_wf orig` mp_tac >> simp[inst_wf_def]) >>
  qpat_x_assum `MEM bb fn'.fn_blocks` kall_tac >>
  drule_all do_merge_jump_reachable_block_map >>
  disch_then (qx_choose_then `psrc` (qx_choose_then `target2` strip_assume_tac)) >>
  `target2 = target` by metis_tac[listTheory.CONS_11] >>
  `fn_cfg_edge fn' pred.bb_label bb.bb_label` by
    (pure_rewrite_tac[fn_cfg_edge_def] >> qexists `pred` >> simp[]) >>
  drule_all do_merge_jump_edge_input >> strip_tac
  >- suspend "old_edge"
  >> suspend "contracted_edge"
QED

Resume do_merge_jump_phi_coverage[old_edge]:
  `MEM src.bb_label (bb_succs psrc)` by
    (qpat_x_assum `fn_cfg_edge fn _ _` mp_tac >>
     pure_rewrite_tac[fn_cfg_edge_def] >> strip_tac >>
     `bb' = psrc` by
       (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
     gvs[]) >>
  `?op. resolve_phi pred.bb_label orig.inst_operands = SOME op` by
    metis_tac[scfg_phi_safe_coverage] >>
  Cases_on `src.bb_label = target`
  >- (`a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_labels_distinct] >>
      `?op. resolve_phi pred.bb_label
         (update_phi_bypass a.bb_label b.bb_label orig).inst_operands = SOME op` by
        (irule resolve_phi_update_bypass_exists >> simp[] >>
         qexistsl [`pred.bb_label`, `op`] >> simp[]) >>
      gvs[]) >>
  gvs[]
QED

Resume do_merge_jump_phi_coverage[contracted_edge]:
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `fn_reachable fn b.bb_label` by
    metis_tac[fn_reachable_step, can_bypass_jump_edge] >>
  `src.bb_label = target /\ MEM src.bb_label (bb_succs b)` by
    (qpat_x_assum `fn_cfg_edge fn _ _` mp_tac >>
     pure_rewrite_tac[fn_cfg_edge_def] >> strip_tac >>
     `bb' = b` by
       (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
     gvs[]) >>
  `?op. resolve_phi b.bb_label orig.inst_operands = SOME op` by
    metis_tac[scfg_phi_safe_coverage] >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_labels_distinct] >>
  `?op. resolve_phi a.bb_label
     (update_phi_bypass a.bb_label b.bb_label orig).inst_operands = SOME op` by
    (irule resolve_phi_update_bypass_exists >> simp[] >>
         qexistsl [`b.bb_label`, `op`] >> simp[]) >>
  gvs[]
QED

Finalise do_merge_jump_phi_coverage

Definition scfg_jnz_inst_ok_def:
  scfg_jnz_inst_ok inst <=>
    !c ops. inst.inst_opcode = JNZ /\ inst.inst_operands = c::ops ==>
      ~is_label_operand c
End

Definition scfg_jnz_condition_ok_def:
  scfg_jnz_condition_ok fn <=>
    !bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
      scfg_jnz_inst_ok inst
End

Theorem fn_shape_ok_jnz_condition_ok:
  fn_shape_ok fn ==> scfg_jnz_condition_ok fn
Proof
  simp[fn_shape_ok_def, scfg_jnz_condition_ok_def, EVERY_MEM] >>
  rpt strip_tac >>
  `inst_shape_ok inst` by
    (fs[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  fs[inst_shape_ok_def, scfg_jnz_inst_ok_def] >> rpt strip_tac >>
  qpat_x_assum `label_positions_ok inst` mp_tac >>
  simp[label_positions_ok_def, AllCaseEqs()] >>
  gvs[is_label_operand_def] >>
  Cases_on `ops` >> simp[] >> Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `h` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Theorem canon_jnz_inst_successors_mem:
  scfg_jnz_inst_ok inst ==>
  (MEM l (get_successors (canon_jnz_inst inst)) <=>
   MEM l (get_successors inst))
Proof
  simp[canon_jnz_inst_def] >> rpt CASE_TAC >>
  gvs[get_successors_mem_label, is_terminator_def, scfg_jnz_inst_ok_def] >>
  Cases_on `h` >> gvs[is_label_operand_def]
QED

Theorem scfg_jnz_inst_ok_subst_label:
  scfg_jnz_inst_ok inst ==> scfg_jnz_inst_ok (subst_label_inst old new inst)
Proof
  simp[scfg_jnz_inst_ok_def, subst_label_inst_def] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `is_label_operand (subst_label_op old new head)` >>
  Cases_on `head` >> gvs[subst_label_op_def, is_label_operand_def]
QED

Theorem scfg_jnz_inst_ok_canon:
  scfg_jnz_inst_ok inst ==> scfg_jnz_inst_ok (canon_jnz_inst inst)
Proof
  simp[canon_jnz_inst_def] >> rpt CASE_TAC >>
  gvs[scfg_jnz_inst_ok_def]
QED

Theorem scfg_jnz_inst_ok_update_phi_bypass:
  scfg_jnz_inst_ok inst ==> scfg_jnz_inst_ok (update_phi_bypass a b inst)
Proof
  Cases_on `inst.inst_opcode = PHI`
  >- simp[scfg_jnz_inst_ok_def, update_phi_bypass_shape] >>
  simp[update_phi_bypass_def]
QED

Theorem scfg_jnz_inst_ok_fix_phi_inst:
  scfg_jnz_inst_ok inst ==> scfg_jnz_inst_ok (fix_phi_inst actual_preds inst)
Proof
  Cases_on `inst.inst_opcode = PHI`
  >- (simp[fix_phi_inst_def] >>
      qabbrev_tac `filtered = filter_phi_ops actual_preds inst.inst_operands` >>
      Cases_on `filtered` >> simp[scfg_jnz_inst_ok_def] >>
      Cases_on `t` >> simp[scfg_jnz_inst_ok_def] >>
      Cases_on `t'` >> simp[scfg_jnz_inst_ok_def]) >>
  simp[fix_phi_inst_def]
QED

Theorem remove_unreachable_blocks_jnz_condition_ok:
  scfg_jnz_condition_ok fn ==> scfg_jnz_condition_ok (remove_unreachable_blocks fn)
Proof
  simp[scfg_jnz_condition_ok_def, remove_unreachable_blocks_def] >>
  Cases_on `fn_entry_label fn` >> simp[MEM_FILTER] >> metis_tac[]
QED

Theorem fix_all_phis_jnz_condition_ok:
  scfg_jnz_condition_ok fn ==> scfg_jnz_condition_ok (fix_all_phis fn)
Proof
  simp[scfg_jnz_condition_ok_def, fix_all_phis_def, fix_phis_in_block_def,
       MEM_MAP, MEM_APPEND, MEM_FILTER, PULL_EXISTS] >>
  metis_tac[scfg_jnz_inst_ok_fix_phi_inst]
QED

Theorem chain_merge_jnz_condition_ok:
  scfg_jnz_condition_ok fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) ==> scfg_jnz_condition_ok fn'
Proof
  strip_tac >>
  `EVERY (\bb. EVERY scfg_jnz_inst_ok bb.bb_instructions) fn.fn_blocks` by
    (fs[scfg_jnz_condition_ok_def, EVERY_MEM] >> metis_tac[]) >>
  drule chain_merge_every_inst >>
  disch_then (qspecl_then [`b`, `a`] mp_tac) >>
  impl_tac >- metis_tac[scfg_jnz_inst_ok_subst_label] >>
  gvs[scfg_jnz_condition_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem do_merge_jump_jnz_condition_ok:
  wf_function fn /\ scfg_jnz_condition_ok fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==> scfg_jnz_condition_ok fn'
Proof
  strip_tac >> pure_rewrite_tac[scfg_jnz_condition_ok_def] >> rpt strip_tac >>
  drule_all do_merge_jump_block_map >> strip_tac >>
  qpat_x_assum `MEM inst _` mp_tac >> asm_rewrite_tac[] >>
  simp[MEM_MAP] >> disch_then (qx_choose_then `orig` strip_assume_tac) >>
  `scfg_jnz_inst_ok orig` by metis_tac[scfg_jnz_condition_ok_def] >>
  Cases_on `bb'.bb_label = a.bb_label` >>
  Cases_on `target = a.bb_label` >> Cases_on `bb'.bb_label = target` >>
  Cases_on `is_terminator orig.inst_opcode` >>
  gvs[combinTheory.I_DEF] >>
  metis_tac[scfg_jnz_inst_ok_subst_label, scfg_jnz_inst_ok_canon,
            scfg_jnz_inst_ok_update_phi_bypass]
QED

Theorem scfg_jnz_inst_ok_subst_block_labels:
  scfg_jnz_inst_ok inst ==> scfg_jnz_inst_ok (subst_block_labels_inst lm inst)
Proof
  Cases_on `is_block_label_opcode inst.inst_opcode` >>
  simp[subst_block_labels_inst_def, subst_label_map_inst_def,
       scfg_jnz_inst_ok_def] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `is_label_operand (subst_label_map_op lm head)` >>
  Cases_on `head` >> gvs[subst_label_map_op_def, is_label_operand_def]
QED

Theorem subst_block_labels_fn_jnz_condition_ok:
  scfg_jnz_condition_ok fn ==> scfg_jnz_condition_ok (subst_block_labels_fn lm fn)
Proof
  simp[scfg_jnz_condition_ok_def, subst_block_labels_fn_def,
       subst_block_labels_block_def, MEM_MAP, PULL_EXISTS] >>
  metis_tac[scfg_jnz_inst_ok_subst_block_labels]
QED

Theorem bypass_source_successor_forward:
  scfg_jnz_inst_ok inst /\ MEM l (get_successors inst) ==>
  MEM (if l = old then new else l) (get_successors
    (if ~is_terminator inst.inst_opcode then inst
     else canon_jnz_inst (subst_label_inst old new inst)))
Proof
  strip_tac >>
  `is_terminator inst.inst_opcode` by fs[get_successors_mem_label] >>
  `scfg_jnz_inst_ok (subst_label_inst old new inst)` by
    simp[scfg_jnz_inst_ok_subst_label] >>
  asm_rewrite_tac[] >>
  ASM_SIMP_TAC std_ss [canon_jnz_inst_successors_mem] >>
  simp[get_successors_mem_label, subst_label_inst_def, MEM_MAP] >>
  qexists `Label l` >>
  fs[get_successors_mem_label, subst_label_op_def] >>
  Cases_on `l = old` >> simp[]
QED

Theorem bb_bypass_source_successor_forward:
  bb_well_formed bb /\ EVERY scfg_jnz_inst_ok bb.bb_instructions /\
  MEM l (bb_succs bb) ==>
  MEM (if l = old then new else l) (bb_succs (bb with bb_instructions :=
    MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                else canon_jnz_inst (subst_label_inst old new inst)) bb.bb_instructions))
Proof
  strip_tac >> `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> gvs[bb_succs_def] >>
  Cases_on `t` >> fs[LAST_MAP, LAST_DEF] >>
  irule bypass_source_successor_forward >> simp[] >>
  fs[EVERY_MEM] >> IF_CASES_TAC >> simp[] >> metis_tac[LAST_MEM]
QED

Theorem do_merge_jump_edge_forward:
  wf_function fn /\ scfg_jnz_condition_ok fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ bb_succs b = [target] /\
  MEM pred fn.fn_blocks /\ pred.bb_label <> b.bb_label /\ MEM l (bb_succs pred) ==>
  fn_cfg_edge fn' pred.bb_label
    (if pred.bb_label = a.bb_label /\ l = b.bb_label then target else l)
Proof
  strip_tac >> drule_all do_merge_jump_output_block >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  drule_all do_merge_jump_block_map >>
  disch_then (qx_choose_then `src` (qx_choose_then `target2` strip_assume_tac)) >>
  `src = pred` by
    (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  `target2 = target` by metis_tac[listTheory.CONS_11] >>
  `bb_well_formed pred` by metis_tac[wf_function_def] >>
  `EVERY scfg_jnz_inst_ok pred.bb_instructions` by
    (fs[EVERY_MEM, scfg_jnz_condition_ok_def] >> metis_tac[]) >>
  pure_rewrite_tac[fn_cfg_edge_def] >> qexists `out` >> simp[] >>
  `out = pred with bb_instructions := out.bb_instructions` by
    simp[basic_block_component_equality] >>
  pop_assum SUBST1_TAC >>
  Cases_on `pred.bb_label = a.bb_label` >>
  Cases_on `target = a.bb_label` >> Cases_on `pred.bb_label = target` >>
  gvs[combinTheory.I_DEF, MAP_MAP_o, combinTheory.o_DEF] >>
  simp[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o,
       bb_succs_update_phi_bypass, bb_succs_bypass_source_phi] >>
  metis_tac[bb_bypass_source_successor_forward]
QED

Theorem update_phi_bypass_pair_not_removed:
  phi_well_formed inst.inst_operands /\ inst.inst_opcode = PHI /\ a <> b /\
  MEM (p,v) (phi_pairs (update_phi_bypass a b inst).inst_operands) ==> p <> b
Proof
  strip_tac >> Cases_on `MEM (Label a) inst.inst_operands`
  >- gvs[update_phi_bypass_def, phi_pairs_remove_phi_label, MEM_FILTER] >>
  drule_all update_phi_bypass_pair_origin >> strip_tac >>
  Cases_on `q = b` >> gvs[]
QED

Theorem do_merge_jump_phi_pair_not_removed:
  wf_function fn /\ fn_inst_wf fn /\ scfg_phi_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ MEM bb fn'.fn_blocks /\
  MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs phi.inst_operands) ==> p <> b.bb_label
Proof
  strip_tac >> drule_all do_merge_jump_block_map >>
  disch_then (qx_choose_then `src` (qx_choose_then `target` strip_assume_tac)) >>
  qpat_x_assum `MEM phi _` mp_tac >> asm_rewrite_tac[] >> simp[MEM_MAP] >>
  disch_then (qx_choose_then `orig` strip_assume_tac) >>
  `orig.inst_opcode = PHI` by
    (Cases_on `src.bb_label = a.bb_label` >> Cases_on `target = a.bb_label` >>
     Cases_on `src.bb_label = target` >> Cases_on `is_terminator orig.inst_opcode` >>
     gvs[update_phi_bypass_shape, canon_jnz_inst_shape, subst_label_inst_shape,
         combinTheory.I_DEF, is_terminator_def]) >>
  `phi = (if src.bb_label = target then update_phi_bypass a.bb_label b.bb_label orig
          else orig)` by
    (Cases_on `src.bb_label = a.bb_label` >> Cases_on `target = a.bb_label` >>
     Cases_on `src.bb_label = target` >> gvs[is_terminator_def]) >>
  Cases_on `src.bb_label = target`
  >- (`inst_wf orig` by metis_tac[fn_inst_wf_def] >>
      `phi_well_formed orig.inst_operands` by
        (qpat_x_assum `inst_wf orig` mp_tac >> simp[inst_wf_def]) >>
      `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_labels_distinct] >>
      metis_tac[update_phi_bypass_pair_not_removed]) >>
  gvs[] >> strip_tac >>
  `fn_cfg_edge fn b.bb_label src.bb_label` by metis_tac[scfg_phi_preds_edge] >>
  `MEM b fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  qpat_x_assum `fn_cfg_edge fn _ _` mp_tac >>
  pure_rewrite_tac[fn_cfg_edge_def] >>
  disch_then (qx_choose_then `edge_src` strip_assume_tac) >>
  `edge_src = b` by
    (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  gvs[]
QED

Theorem do_merge_jump_phi_preds:
  wf_function fn /\ fn_inst_wf fn /\ scfg_jnz_condition_ok fn /\ scfg_phi_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==> scfg_phi_preds fn'
Proof
  strip_tac >> pure_rewrite_tac[scfg_phi_preds_def] >> rpt strip_tac >>
  `p <> b.bb_label` by metis_tac[do_merge_jump_phi_pair_not_removed] >>
  drule_all do_merge_jump_phi_pair_source >>
  disch_then (qx_choose_then `src` (qx_choose_then `orig`
    (qx_choose_then `q` (qx_choose_then `target` strip_assume_tac)))) >>
  `fn_cfg_edge fn q src.bb_label` by metis_tac[scfg_phi_preds_edge] >>
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  qpat_x_assum `fn_cfg_edge fn _ _` mp_tac >>
  pure_rewrite_tac[fn_cfg_edge_def] >>
  disch_then (qx_choose_then `pred` strip_assume_tac) >>
  Cases_on `q = b.bb_label`
  >- suspend "contracted"
  >> suspend "retained"
QED

Resume do_merge_jump_phi_preds[contracted]:
  `pred = b` by
    (irule same_label_same_block >> fs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  `src.bb_label = target` by gvs[] >>
  `MEM b.bb_label (bb_succs a)` by fs[can_bypass_jump_def] >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_labels_distinct] >>
  drule_all do_merge_jump_edge_forward >> gvs[fn_cfg_edge_def]
QED

Resume do_merge_jump_phi_preds[retained]:
  `pred.bb_label <> b.bb_label` by metis_tac[] >>
  `p = pred.bb_label` by gvs[] >>
  drule_all do_merge_jump_edge_forward >>
  Cases_on `pred.bb_label = a.bb_label` >> gvs[fn_cfg_edge_def]
QED

Finalise do_merge_jump_phi_preds

Theorem chain_merge_phi_safe:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) ==> scfg_phi_safe fn'
Proof
  strip_tac >> pure_rewrite_tac[scfg_phi_safe_def] >> conj_tac
  >- metis_tac[chain_merge_entry_no_phi] >> conj_tac
  >- metis_tac[chain_merge_phi_output_unique] >>
  metis_tac[chain_merge_phi_coverage]
QED

Theorem do_merge_jump_phi_safe:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==> scfg_phi_safe fn'
Proof
  strip_tac >> pure_rewrite_tac[scfg_phi_safe_def] >> conj_tac
  >- metis_tac[do_merge_jump_entry_no_phi] >> conj_tac
  >- metis_tac[do_merge_jump_phi_output_unique] >>
  metis_tac[do_merge_jump_phi_coverage]
QED

Definition scfg_reachuses_inv_def:
  scfg_reachuses_inv fn <=>
    wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
    scfg_phi_safe fn /\ fn_defs_reach_uses fn /\ scfg_jnz_condition_ok fn
End

Definition scfg_collapse_inv_def:
  scfg_collapse_inv fn <=> scfg_reachuses_inv fn /\ scfg_phi_preds fn
End

Theorem chain_merge_collapse_inv:
  scfg_collapse_inv fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) ==> scfg_collapse_inv fn'
Proof
  simp[scfg_collapse_inv_def, scfg_reachuses_inv_def] >> strip_tac >>
  `lookup_block a.bb_label fn.fn_blocks = SOME a /\
   lookup_block b.bb_label fn.fn_blocks = SOME b` by
    (fs[wf_function_def, fn_labels_def] >> metis_tac[MEM_lookup_block]) >>
  rpt conj_tac
  >- metis_tac[chain_merge_wf]
  >- metis_tac[chain_merge_fn_inst_wf]
  >- metis_tac[chain_merge_first_block_no_preds]
  >- metis_tac[chain_merge_phi_safe]
  >- metis_tac[chain_merge_defs_reach_uses]
  >- metis_tac[chain_merge_jnz_condition_ok] >>
  metis_tac[chain_merge_phi_preds]
QED

Theorem do_merge_jump_collapse_inv:
  scfg_collapse_inv fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==> scfg_collapse_inv fn'
Proof
  simp[scfg_collapse_inv_def, scfg_reachuses_inv_def] >> strip_tac >>
  rpt conj_tac
  >- metis_tac[do_merge_jump_wf]
  >- metis_tac[do_merge_jump_fn_inst_wf]
  >- metis_tac[do_merge_jump_first_block_no_preds]
  >- metis_tac[do_merge_jump_phi_safe]
  >- metis_tac[do_merge_jump_defs_reach_uses]
  >- metis_tac[do_merge_jump_jnz_condition_ok] >>
  metis_tac[do_merge_jump_phi_preds]
QED

Theorem try_bypass_collapse_inv:
  scfg_collapse_inv fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn',lm',T) ==> scfg_collapse_inv fn'
Proof
  qid_spec_tac `succs` >> Induct >- simp[try_bypass_def] >>
  rpt strip_tac >> gvs[Once try_bypass_def, AllCaseEqs()] >>
  metis_tac[do_merge_jump_collapse_inv, lookup_block_member_label]
QED

Theorem collapse_reachuses_inv_joint:
  (!fn lm visited lbl. scfg_collapse_inv fn ==>
    scfg_collapse_inv (FST (collapse_dfs fn lm visited lbl))) /\
  (!fn lm visited succs. scfg_collapse_inv fn ==>
    scfg_collapse_inv (FST (collapse_dfs_succs fn lm visited succs)))
Proof
  irule (collapse_property_joint |> Q.SPEC `scfg_collapse_inv`) >>
  conj_tac
  >- (rpt strip_tac >> irule chain_merge_collapse_inv >>
      metis_tac[lookup_block_member_label]) >>
  metis_tac[try_bypass_collapse_inv]
QED

Theorem subst_label_map_phi_absent:
  !ops. phi_well_formed ops /\
  (!p v. MEM (p,v) (phi_pairs ops) ==> ~MEM p (MAP FST lm)) ==>
  MAP (subst_label_map_op lm) ops = ops
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, phi_pairs_def] >> rpt strip_tac >>
  `ALOOKUP lm lbl = NONE` by metis_tac[alistTheory.ALOOKUP_NONE] >>
  gvs[subst_label_map_op_def] >> metis_tac[]
QED

Theorem subst_block_labels_inst_inactive:
  wf_function fn /\ fn_inst_wf fn /\ scfg_phi_preds fn /\
  (!l. MEM l (fn_labels fn) ==> ~MEM l (MAP FST lm)) /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
  subst_block_labels_inst lm inst = inst
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (irule subst_block_labels_terminator_absent >> simp[] >>
      `bb_well_formed bb` by metis_tac[wf_function_def] >>
      `inst = LAST bb.bb_instructions` by
        metis_tac[bb_well_formed_terminator_last] >>
      `!l. MEM l (bb_succs bb) ==> ~MEM l (MAP FST lm)` by
        metis_tac[wf_function_def, fn_succs_closed_def] >>
      Cases_on `bb.bb_instructions` >>
      gvs[bb_well_formed_def, bb_succs_def, MEM_nub, MEM_REVERSE]) >>
  Cases_on `inst.inst_opcode = PHI`
  >- (`phi_well_formed inst.inst_operands` by
        (`inst_wf inst` by metis_tac[fn_inst_wf_def] >>
         qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def]) >>
      `!p v. MEM (p,v) (phi_pairs inst.inst_operands) ==>
        ~MEM p (MAP FST lm)` by
        (rpt strip_tac >>
         `fn_cfg_edge fn p bb.bb_label` by metis_tac[scfg_phi_preds_edge] >>
         fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
      drule_all subst_label_map_phi_absent >>
      simp[subst_block_labels_inst_def, is_block_label_opcode_def,
        subst_label_map_inst_def]) >>
  simp[subst_block_labels_inst_def, is_block_label_opcode_def]
QED

Theorem subst_block_labels_fn_inactive:
  wf_function fn /\ fn_inst_wf fn /\ scfg_phi_preds fn /\
  (!l. MEM l (fn_labels fn) ==> ~MEM l (MAP FST lm)) ==>
  subst_block_labels_fn lm fn = fn
Proof
  strip_tac >>
  `MAP (subst_block_labels_block lm) fn.fn_blocks = fn.fn_blocks` by
    (GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
     irule MAP_CONG >> simp[] >> rpt strip_tac >>
     `MAP (subst_block_labels_inst lm) x.bb_instructions = x.bb_instructions` by
       (GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
        irule MAP_CONG >> simp[] >> rpt strip_tac >>
        metis_tac[subst_block_labels_inst_inactive]) >>
     simp[subst_block_labels_block_def]) >>
  simp[subst_block_labels_fn_def]
QED

Theorem collapse_subst_collapse_inv:
  scfg_collapse_inv fn /\ collapse_dfs fn [] visited lbl = (fn',lm,visited') ==>
  scfg_collapse_inv (subst_block_labels_fn lm fn')
Proof
  strip_tac >>
  `scfg_collapse_inv fn'` by metis_tac[cj 1 collapse_reachuses_inv_joint, pairTheory.FST] >>
  `!l. MEM l (fn_labels fn') ==> ~MEM l (MAP FST lm)` by
    (`ALL_DISTINCT (fn_labels fn)` by
       fs[scfg_collapse_inv_def, scfg_reachuses_inv_def, wf_function_def] >>
     metis_tac[collapse_dfs_sources_absent]) >>
  `subst_block_labels_fn lm fn' = fn'` by
    (irule subst_block_labels_fn_inactive >>
     fs[scfg_collapse_inv_def, scfg_reachuses_inv_def]) >> simp[]
QED
