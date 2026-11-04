(* Graph boundaries for the exact chain contraction used by collapse_dfs. *)
Theory simplifyCfgMergeStatic
Ancestors
  simplifyCfgStaticInterface simplifyCfgDefs cfgNormSupplyProofs
  cfgTransform venomInst list rich_list
  simplifyCfgStruct simplifyCfgChainDataflow

Theorem scfg_merge_label:
  (merge_blocks a b).bb_label = a.bb_label
Proof
  simp[merge_blocks_def]
QED

Theorem scfg_lookup_remove:
  !bbs l k. lookup_block l (remove_block k bbs) =
    if l = k then NONE else lookup_block l bbs
Proof
  Induct >> simp[remove_block_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `h.bb_label = k` >>
  Cases_on `h.bb_label = l` >> gvs[lookup_block_def, remove_block_def, FIND_thm]
QED

Theorem scfg_lookup_replace:
  !bbs k bb l. bb.bb_label = k ==>
    lookup_block l (replace_block k bb bbs) =
    if l = k then OPTION_MAP (K bb) (lookup_block l bbs)
    else lookup_block l bbs
Proof
  Induct >> simp[replace_block_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `h.bb_label = bb.bb_label` >>
  Cases_on `h.bb_label = l` >>
  gvs[lookup_block_def, replace_block_def, FIND_thm]
QED

Theorem scfg_chain_body_lookup:
  a.bb_label <> b.bb_label /\ lookup_block a.bb_label fn.fn_blocks = SOME a ==>
  lookup_block l (replace_block a.bb_label (merge_blocks a b)
    (remove_block b.bb_label fn.fn_blocks)) =
    if l = b.bb_label then NONE
    else if l = a.bb_label then SOME (merge_blocks a b)
    else lookup_block l fn.fn_blocks
Proof
  strip_tac >> simp[scfg_lookup_replace, scfg_merge_label, scfg_lookup_remove] >>
  Cases_on `l = b.bb_label` >> Cases_on `l = a.bb_label` >> gvs[]
QED

Theorem scfg_succ_phi_lookup:
  !succs bbs old new l.
  lookup_block l (update_succ_phi_labels old new bbs succs) =
  OPTION_MAP (\bb. if MEM l succs then
    bb with bb_instructions := MAP (\i. if i.inst_opcode <> PHI then i
      else subst_label_inst old new i) bb.bb_instructions else bb)
    (lookup_block l bbs)
Proof
  Induct >- simp[update_succ_phi_labels_def] >> qx_gen_tac `lbl` >> rpt gen_tac >>
  once_rewrite_tac[update_succ_phi_labels_def] >>
  simp[Once FOLDL] >>
  namedCases_on `lookup_block lbl bbs` ["", "blk"]
  >- (fs[update_succ_phi_labels_def] >> Cases_on `l = lbl` >> gvs[]) >>
  fs[update_succ_phi_labels_def] >>
  `blk.bb_label = lbl` by metis_tac[lookup_block_member_label] >>
  simp[scfg_lookup_replace] >>
  Cases_on `l = lbl` >> gvs[] >>
  Cases_on `MEM blk.bb_label succs` >> simp[MAP_MAP_o, combinTheory.o_DEF] >>
  AP_THM_TAC >> ntac 2 AP_TERM_TAC >>
  irule listTheory.MAP_CONG >> simp[] >> qx_gen_tac `i` >> strip_tac >>
  Cases_on `i.inst_opcode = PHI` >>
  simp[subst_label_inst_idempotent]
QED

Theorem scfg_succ_phi_block_succs:
  bb_succs (bb with bb_instructions :=
    MAP (\i. if i.inst_opcode <> PHI then i else subst_label_inst old new i)
      bb.bb_instructions) = bb_succs bb
Proof
  Cases_on `bb.bb_instructions` using SNOC_CASES >>
  simp[bb_succs_def, MAP_SNOC, SNOC_APPEND, LAST_APPEND_CONS] >>
  Cases_on `l` >> simp[LAST_CONS_cond, LAST_APPEND_CONS] >>
  Cases_on `x.inst_opcode = PHI` >>
  simp[get_successors_def, is_terminator_def]
QED

Theorem scfg_chain_lookup:
  a.bb_label <> b.bb_label /\ lookup_block a.bb_label fn.fn_blocks = SOME a ==>
  lookup_block l (update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))) =
  OPTION_MAP (\bb. if MEM l (bb_succs (merge_blocks a b)) then
    bb with bb_instructions := MAP (\i. if i.inst_opcode <> PHI then i
      else subst_label_inst b.bb_label a.bb_label i) bb.bb_instructions else bb)
    (if l = b.bb_label then NONE
     else if l = a.bb_label then SOME (merge_blocks a b)
     else lookup_block l fn.fn_blocks)
Proof
  simp[scfg_succ_phi_lookup, scfg_chain_body_lookup]
QED

Theorem scfg_succ_phi_lookup_succs:
  !succs bbs old new l.
  OPTION_MAP bb_succs (lookup_block l
    (update_succ_phi_labels old new bbs succs)) =
  OPTION_MAP bb_succs (lookup_block l bbs)
Proof
  simp[scfg_succ_phi_lookup] >> rpt gen_tac >>
  Cases_on `lookup_block l bbs` >> simp[] >>
  Cases_on `MEM l succs` >> simp[scfg_succ_phi_block_succs]
QED

Theorem scfg_entry_labels:
  fn_entry_label fn = case fn_labels fn of [] => NONE | l::ls => SOME l
Proof
  Cases_on `fn.fn_blocks` >> simp[fn_entry_label_def, entry_block_def, fn_labels_def]
QED

Theorem scfg_succ_phi_entry:
  fn_entry_label (fn with fn_blocks := update_succ_phi_labels old new bbs succs) =
  fn_entry_label (fn with fn_blocks := bbs)
Proof
  simp[scfg_entry_labels, fn_labels_def, simplifyCfgLabelPropsTheory.fn_labels_update_succ_phi_labels]
QED

Theorem scfg_chain_entry:
  fn_entry_label fn <> SOME b.bb_label ==>
  fn_entry_label (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))) =
  fn_entry_label fn
Proof
  simp[scfg_succ_phi_entry] >>
  Cases_on `fn.fn_blocks` >>
  simp[fn_entry_label_def, entry_block_def, remove_block_def, replace_block_def] >>
  strip_tac >> Cases_on `h.bb_label = a.bb_label` >> simp[scfg_merge_label]
QED

Theorem scfg_merge_not_entry:
  unitShapeDefs$first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\ can_merge_blocks fn a b ==>
  fn_entry_label fn <> SOME b.bb_label
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  Cases_on `fn.fn_blocks` >>
  fs[unitShapeDefsTheory.first_block_no_preds_def, EVERY_MEM,
    fn_entry_label_def, entry_block_def, can_merge_blocks_def] >> metis_tac[MEM]
QED

Theorem scfg_merge_preds:
  lookup_block a.bb_label fn.fn_blocks = SOME a /\ can_merge_blocks fn a b ==>
  block_preds fn b.bb_label = [a]
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `MEM a (block_preds fn b.bb_label)` by
    fs[can_merge_blocks_def, block_preds_def, MEM_FILTER] >>
  `LENGTH (block_preds fn b.bb_label) = 1` by
    fs[can_merge_blocks_def, num_preds_def] >>
  namedCases_on `block_preds fn b.bb_label` ["", "p rest"] >> gvs[] >>
  Cases_on `rest` >> gvs[]
QED

Theorem scfg_merge_incoming:
  lookup_block a.bb_label fn.fn_blocks = SOME a /\ can_merge_blocks fn a b /\
  MEM bb fn.fn_blocks /\ MEM b.bb_label (bb_succs bb) ==> bb = a
Proof
  strip_tac >> drule_all scfg_merge_preds >>
  `MEM bb (block_preds fn b.bb_label)` by simp[block_preds_def, MEM_FILTER] >>
  metis_tac[MEM]
QED

Theorem scfg_chain_distinct:
  ALL_DISTINCT (fn_labels fn) ==>
  ALL_DISTINCT (fn_labels (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))))
Proof
  simp[chain_merge_fn_labels, FILTER_ALL_DISTINCT]
QED

Theorem scfg_chain_lookup_successors:
  a.bb_label <> b.bb_label /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  b.bb_instructions <> [] ==>
  OPTION_MAP bb_succs (lookup_block l
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))) =
  if l = b.bb_label then NONE else if l = a.bb_label then SOME (bb_succs b)
  else OPTION_MAP bb_succs (lookup_block l fn.fn_blocks)
Proof
  strip_tac >> simp[scfg_succ_phi_lookup_succs, scfg_chain_body_lookup] >>
  Cases_on `l = b.bb_label` >> Cases_on `l = a.bb_label` >>
  simp[bb_succs_merge_blocks]
QED

Theorem scfg_succ_lookup[local]:
  fn_succ fn x y <=> ?ls.
    OPTION_MAP bb_succs (lookup_block x fn.fn_blocks) = SOME ls /\ MEM y ls
Proof
  Cases_on `lookup_block x fn.fn_blocks` >> simp[fn_succ_def]
QED

Theorem scfg_chain_edge:
  fn' = fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)) /\
  ALL_DISTINCT (fn_labels fn) /\ can_merge_blocks fn a b /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ b.bb_instructions <> [] ==>
  (venomWf$fn_cfg_edge fn' x y <=> x <> b.bb_label /\
    if x = a.bb_label then venomWf$fn_cfg_edge fn b.bb_label y
    else venomWf$fn_cfg_edge fn x y)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn')` by metis_tac[scfg_chain_distinct] >>
  simp[simplifyCfgLabelPropsTheory.fn_cfg_edge_iff_fn_succ] >>
  `a.bb_label <> b.bb_label` by metis_tac[can_merge_blocks_distinct] >>
  drule_all scfg_chain_lookup_successors >>
  disch_then (qspec_then `x` assume_tac) >>
  pure_rewrite_tac[scfg_succ_lookup] >>
  Cases_on `x = b.bb_label` >> Cases_on `x = a.bb_label` >> gvs[] >>
  qmatch_asmsub_abbrev_tac `lookup_block x bbs` >>
  Cases_on `lookup_block x bbs` >>
  Cases_on `lookup_block x fn.fn_blocks` >> gvs[]
QED
