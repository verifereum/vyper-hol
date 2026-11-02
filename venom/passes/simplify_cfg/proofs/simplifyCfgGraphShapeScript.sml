(* Entry and successor closure at SimplifyCFG's graph-edit boundary. *)
Theory simplifyCfgGraphShape
Ancestors
  simplifyCfgShape simplifyCfgDefs cfgTransformProps cfgTransform venomWf venomInst
  unitShapeDefs list rich_list

Theorem remove_unreachable_blocks_head:
  fn.fn_blocks <> [] ==>
  (remove_unreachable_blocks fn).fn_blocks <> [] /\
  HD (remove_unreachable_blocks fn).fn_blocks = HD fn.fn_blocks
Proof
  Cases_on `fn.fn_blocks` >> simp[] >>
  `fn_entry_label fn = SOME h.bb_label` by
    simp[fn_entry_label_def, entry_block_def] >>
  `reachable fn h.bb_label` by metis_tac[reachable_entry] >>
  simp[remove_unreachable_blocks_def]
QED

Theorem remove_unreachable_blocks_first_no_preds:
  fn.fn_blocks <> [] /\ first_block_no_preds fn ==>
  first_block_no_preds (remove_unreachable_blocks fn)
Proof
  strip_tac >> drule remove_unreachable_blocks_head >> strip_tac >>
  gvs[first_block_no_preds_def] >>
  Cases_on `fn_entry_label fn` >> simp[remove_unreachable_blocks_def] >>
  gvs[EVERY_MEM, MEM_FILTER]
QED

Theorem remove_unreachable_blocks_succs_closed:
  ALL_DISTINCT (fn_labels fn) /\ fn_succs_closed fn ==>
  fn_succs_closed (remove_unreachable_blocks fn)
Proof
  strip_tac >> Cases_on `fn_entry_label fn`
  >- simp[remove_unreachable_blocks_def] >>
  simp[remove_unreachable_blocks_def, fn_succs_closed_def,
       fn_labels_def, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[fn_labels_def]) >>
  `fn_succ fn bb.bb_label succ` by
    (simp[fn_succ_def] >> metis_tac[]) >>
  `reachable fn succ` by metis_tac[reachable_step] >>
  qpat_x_assum `fn_succs_closed fn` mp_tac >>
  simp[fn_succs_closed_def, fn_labels_def, MEM_MAP] >>
  disch_then drule_all >> strip_tac >> metis_tac[]
QED

Theorem num_preds_one_unique:
  num_preds fn lbl = 1 /\ MEM a fn.fn_blocks /\
  MEM lbl (bb_succs a) /\ MEM c fn.fn_blocks /\
  MEM lbl (bb_succs c) ==> c = a
Proof
  simp[num_preds_def, block_preds_def] >> strip_tac >>
  qabbrev_tac `pbs = FILTER (\bb. MEM lbl (bb_succs bb)) fn.fn_blocks` >>
  `MEM a pbs /\ MEM c pbs` by simp[Abbr `pbs`, MEM_FILTER] >>
  Cases_on `pbs` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem incoming_not_entry:
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\
  MEM a fn.fn_blocks /\ MEM lbl (bb_succs a) ==>
  lbl <> (HD fn.fn_blocks).bb_label
Proof
  Cases_on `fn.fn_blocks` >> simp[first_block_no_preds_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem merge_blocks_succs:
  b.bb_instructions <> [] ==>
  bb_succs (merge_blocks a b) = bb_succs b
Proof
  strip_tac >>
  `LAST (FRONT a.bb_instructions ++ b.bb_instructions) =
   LAST b.bb_instructions` by
    (Cases_on `b.bb_instructions` >> gvs[LAST_APPEND]) >>
  `FRONT a.bb_instructions ++ b.bb_instructions <> []` by simp[] >>
  simp[merge_blocks_def, bb_succs_def] >>
  Cases_on `FRONT a.bb_instructions ++ b.bb_instructions` >>
  gvs[] >> Cases_on `b.bb_instructions` >> gvs[]
QED

Theorem can_merge_blocks_not_entry:
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  can_merge_blocks fn a b ==>
  b.bb_label <> (HD fn.fn_blocks).bb_label
Proof
  strip_tac >> irule incoming_not_entry >>
  simp[] >> qexists_tac `a` >>
  gvs[can_merge_blocks_def] >>
  metis_tac[lookup_block_member_label]
QED

Theorem can_bypass_jump_not_entry:
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  can_bypass_jump fn a b ==>
  b.bb_label <> (HD fn.fn_blocks).bb_label
Proof
  strip_tac >> irule incoming_not_entry >>
  simp[] >> qexists_tac `a` >>
  gvs[can_bypass_jump_def] >>
  metis_tac[lookup_block_member_label]
QED

Theorem update_phi_bypass_successors:
  get_successors (update_phi_bypass a b i) = get_successors i
Proof
  Cases_on `i.inst_opcode = PHI` >>
  simp[update_phi_bypass_def, get_successors_def] >>
  simp[is_terminator_def] >>
  Cases_on `MEM (Label a) i.inst_operands` >>
  simp[get_successors_def, is_terminator_def]
QED

Theorem succ_phi_update_successors:
  get_successors
    (if i.inst_opcode <> PHI then i else subst_label_inst old new i) =
  get_successors i
Proof
  Cases_on `i.inst_opcode = PHI` >>
  simp[subst_label_inst_def, get_successors_def, is_terminator_def]
QED

Theorem bb_succs_map_preserve:
  (!i. get_successors (tr i) = get_successors i) ==>
  bb_succs (bb with bb_instructions := MAP tr bb.bb_instructions) =
  bb_succs bb
Proof
  strip_tac >> Cases_on `bb.bb_instructions` >> simp[bb_succs_def] >>
  qspecl_then [`h::t`, `tr`] mp_tac LAST_MAP >>
  (impl_tac >- simp[]) >>
  pure_rewrite_tac[MAP] >> disch_then SUBST1_TAC >> simp[]
QED

Theorem replace_block_graph:
  !bbs old new lbl.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    lookup_block lbl bbs = SOME old /\
    new.bb_label = old.bb_label /\ bb_succs new = bb_succs old ==>
    MAP (\bb. (bb.bb_label, bb_succs bb)) (replace_block lbl new bbs) =
    MAP (\bb. (bb.bb_label, bb_succs bb)) bbs
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `h.bb_label = lbl` >>
  simp[lookup_block_def, FIND_thm, replace_block_def] >> strip_tac >> gvs[]
  >- (simp[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
      rename1 `MEM bb bbs` >>
      `bb.bb_label <> h.bb_label` by metis_tac[MEM_MAP] >> simp[]) >>
  qpat_x_assum `!old' new' lbl'. _` mp_tac >>
  simp[lookup_block_def, replace_block_def] >>
  disch_then irule >> metis_tac[]
QED

Theorem update_succ_phi_labels_graph:
  !succs bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    MAP (\bb. (bb.bb_label, bb_succs bb))
      (update_succ_phi_labels old new bbs succs) =
    MAP (\bb. (bb.bb_label, bb_succs bb)) bbs
Proof
  Induct >> gvs[update_succ_phi_labels_def] >> rpt strip_tac >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  rename1 `lookup_block h bbs = SOME bb` >>
  `bb.bb_label = h` by metis_tac[lookup_block_member_label] >>
  qmatch_goalsub_abbrev_tac `replace_block h changed bbs` >>
  `changed.bb_label = h /\ bb_succs changed = bb_succs bb` by
    (simp[Abbr `changed`] >> irule bb_succs_map_preserve >>
     simp[succ_phi_update_successors]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (replace_block h changed bbs))` by
    metis_tac[fn_labels_replace_block] >>
  `MAP (\bb. (bb.bb_label, bb_succs bb)) (replace_block h changed bbs) =
   MAP (\bb. (bb.bb_label, bb_succs bb)) bbs` by
    (irule replace_block_graph >> metis_tac[]) >>
  first_x_assum drule >> simp[]
QED
