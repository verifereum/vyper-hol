(* Entry and successor closure at SimplifyCFG's graph-edit boundary. *)
Theory simplifyCfgGraphShape
Ancestors
  simplifyCfgShape simplifyCfgDefs simplifyCfgLabelProps simplifyCfgInvariant
  cfgTransformProps cfgTransform venomWf venomInst
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

Theorem chain_merge_blocks_nonempty:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_merge_blocks fn a b /\
  fn' = fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b)) ==>
  fn'.fn_blocks <> []
Proof
  strip_tac >>
  qspecl_then [`fn`, `a`, `b.bb_label`, `b`] mp_tac chain_merge_event_labels >>
  simp[] >> strip_tac >> Cases_on `fn'.fn_blocks` >> gvs[fn_labels_def]
QED

Theorem do_merge_jump_blocks_nonempty:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  fn'.fn_blocks <> []
Proof
  strip_tac >> drule_all do_merge_jump_event_labels >>
  strip_tac >> Cases_on `fn'.fn_blocks` >> gvs[fn_labels_def]
QED

Theorem replace_block_head_label:
  bbs <> [] /\ bb.bb_label = lbl ==>
  replace_block lbl bb bbs <> [] /\
  (HD (replace_block lbl bb bbs)).bb_label = (HD bbs).bb_label
Proof
  Cases_on `bbs` >> simp[replace_block_def] >> strip_tac >>
  Cases_on `h.bb_label = lbl` >> simp[]
QED

Theorem update_succ_phi_labels_head_label:
  !succs bbs. bbs <> [] ==>
  update_succ_phi_labels old new bbs succs <> [] /\
  (HD (update_succ_phi_labels old new bbs succs)).bb_label =
  (HD bbs).bb_label
Proof
  Induct >> gvs[update_succ_phi_labels_def] >> rpt gen_tac >> disch_tac >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  rename1 `lookup_block h bbs = SOME bb` >>
  `bb.bb_label = h` by metis_tac[lookup_block_member_label] >>
  qmatch_goalsub_abbrev_tac `replace_block h changed bbs` >>
  `changed.bb_label = h` by simp[Abbr `changed`] >>
  `replace_block h changed bbs <> [] /\
   (HD (replace_block h changed bbs)).bb_label = (HD bbs).bb_label` by
    (irule replace_block_head_label >> simp[]) >>
  first_x_assum drule >> simp[]
QED

Theorem remove_block_head:
  bbs <> [] /\ lbl <> (HD bbs).bb_label ==>
  remove_block lbl bbs <> [] /\ HD (remove_block lbl bbs) = HD bbs
Proof
  Cases_on `bbs` >> simp[remove_block_def] >> strip_tac >> simp[]
QED

Theorem chain_merge_entry_label:
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  can_merge_blocks fn a b /\
  fn' = fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b)) ==>
  (HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label
Proof
  strip_tac >>
  `b.bb_label <> (HD fn.fn_blocks).bb_label` by
    (irule can_merge_blocks_not_entry >> metis_tac[]) >>
  `remove_block b.bb_label fn.fn_blocks <> [] /\
   HD (remove_block b.bb_label fn.fn_blocks) = HD fn.fn_blocks` by
    (irule remove_block_head >> simp[]) >>
  `replace_block a.bb_label (merge_blocks a b)
     (remove_block b.bb_label fn.fn_blocks) <> [] /\
   (HD (replace_block a.bb_label (merge_blocks a b)
     (remove_block b.bb_label fn.fn_blocks))).bb_label =
   (HD fn.fn_blocks).bb_label` by
    (drule replace_block_head_label >>
     disch_then (qspecl_then [`a.bb_label`, `merge_blocks a b`] mp_tac) >>
     simp[merge_blocks_def]) >>
  drule update_succ_phi_labels_head_label >> simp[] >> metis_tac[]
QED

Theorem do_merge_jump_entry_label:
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  (HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label
Proof
  strip_tac >>
  `b.bb_label <> (HD fn.fn_blocks).bb_label` by
    (irule can_bypass_jump_not_entry >> metis_tac[]) >>
  `remove_block b.bb_label fn.fn_blocks <> [] /\
   HD (remove_block b.bb_label fn.fn_blocks) = HD fn.fn_blocks` by
    (irule remove_block_head >> simp[]) >>
  qpat_x_assum `do_merge_jump _ _ _ _ = _` mp_tac >>
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `lookup_block target_lbl fn.fn_blocks = SOME target` >>
  `target.bb_label = target_lbl` by metis_tac[lookup_block_member_label] >>
  qmatch_goalsub_abbrev_tac `replace_block a.bb_label source
    (replace_block target_lbl dest rest)` >>
  `source.bb_label = a.bb_label /\ dest.bb_label = target_lbl` by
    simp[Abbr `source`, Abbr `dest`] >>
  `rest <> [] /\ (HD rest).bb_label = (HD fn.fn_blocks).bb_label` by
    simp[Abbr `rest`] >>
  `replace_block target_lbl dest rest <> [] /\
   (HD (replace_block target_lbl dest rest)).bb_label = (HD rest).bb_label` by
    (irule replace_block_head_label >> simp[]) >>
  metis_tac[replace_block_head_label]
QED

Theorem block_graph_every:
  MAP (\bb. (bb.bb_label, bb_succs bb)) bs1 =
    MAP (\bb. (bb.bb_label, bb_succs bb)) bs2 /\
  EVERY (\bb. P bb.bb_label (bb_succs bb)) bs2 ==>
  EVERY (\bb. P bb.bb_label (bb_succs bb)) bs1
Proof
  strip_tac >>
  `EVERY (\p. P (FST p) (SND p))
     (MAP (\bb. (bb.bb_label, bb_succs bb)) bs1)` suffices_by
    simp[EVERY_MAP] >>
  asm_rewrite_tac[] >> simp[EVERY_MAP]
QED

Theorem update_succ_phi_labels_graph_every:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  EVERY (\bb. P bb.bb_label (bb_succs bb)) bbs ==>
  EVERY (\bb. P bb.bb_label (bb_succs bb))
    (update_succ_phi_labels old new bbs succs)
Proof
  strip_tac >> irule block_graph_every >> qexists_tac `bbs` >>
  simp[update_succ_phi_labels_graph]
QED

Theorem chain_merge_first_no_preds:
  ALL_DISTINCT (fn_labels fn) /\
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_merge_blocks fn a b /\ b.bb_instructions <> [] /\
  fn' = fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b)) ==>
  first_block_no_preds fn'
Proof
  strip_tac >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (irule chain_merge_entry_label >> metis_tac[]) >>
  rewrite_tac[first_block_no_preds_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `fn' = _` SUBST1_TAC >> simp[] >>
  ho_match_mp_tac update_succ_phi_labels_graph_every >> conj_tac
  >- (simp[fn_labels_replace_block, merge_blocks_def] >>
      irule ALL_DISTINCT_remove_block >> gvs[fn_labels_def]) >>
  irule replace_block_every >> reverse conj_tac
  >- (irule remove_block_every >> gvs[first_block_no_preds_def]) >>
  simp[merge_blocks_succs] >>
  gvs[first_block_no_preds_def, EVERY_MEM] >>
  metis_tac[lookup_block_member_label]
QED

Theorem update_succ_phi_labels_labels:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  MAP (\bb. bb.bb_label) (update_succ_phi_labels old new bbs succs) =
  MAP (\bb. bb.bb_label) bbs
Proof
  strip_tac >>
  `MAP FST (MAP (\bb. (bb.bb_label, bb_succs bb))
      (update_succ_phi_labels old new bbs succs)) =
   MAP FST (MAP (\bb. (bb.bb_label, bb_succs bb)) bbs)` by
    simp[update_succ_phi_labels_graph] >>
  gvs[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem chain_merge_succs_closed:
  ALL_DISTINCT (fn_labels fn) /\
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\ fn_succs_closed fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_merge_blocks fn a b /\ b.bb_instructions <> [] /\
  fn' = fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b)) ==>
  fn_succs_closed fn'
Proof
  strip_tac >>
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)))` by
    (simp[fn_labels_replace_block, merge_blocks_def] >>
     irule ALL_DISTINCT_remove_block >> gvs[fn_labels_def]) >>
  `fn_labels fn' = FILTER (\l. l <> b.bb_label) (fn_labels fn)` by
    (simp[fn_labels_def] >> qpat_x_assum `fn' = _` SUBST1_TAC >>
     simp[update_succ_phi_labels_labels, fn_labels_replace_block,
          merge_blocks_def, fn_labels_remove_block, fn_labels_def]) >>
  rewrite_tac[fn_succs_closed_def] >>
  `EVERY (\bb. EVERY (\l. MEM l (fn_labels fn')) (bb_succs bb))
    fn'.fn_blocks` suffices_by (simp[EVERY_MEM] >> metis_tac[]) >>
  qpat_assum `fn_labels fn' = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `fn' = _` SUBST1_TAC >> simp[] >>
  ho_match_mp_tac update_succ_phi_labels_graph_every >> conj_tac
  >- first_x_assum ACCEPT_TAC >>
  pure_rewrite_tac[replace_block_def, remove_block_def] >>
  pure_rewrite_tac[EVERY_MAP] >> pure_rewrite_tac[EVERY_FILTER] >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  rename1 `MEM bb fn.fn_blocks` >>
  Cases_on `bb.bb_label = a.bb_label` >> simp[merge_blocks_succs,
    EVERY_MEM, MEM_FILTER] >> disch_tac >> gen_tac >> disch_tac >> reverse conj_tac
  >- metis_tac[fn_succs_closed_def] 
  >- (strip_tac >> `b = a` by
        (irule num_preds_one_unique >> gvs[can_merge_blocks_def] >>
         metis_tac[]) >> gvs[can_merge_blocks_def])
  >- metis_tac[fn_succs_closed_def] >>
  strip_tac >> `bb = a` by
    (irule num_preds_one_unique >> gvs[can_merge_blocks_def] >>
     metis_tac[]) >> gvs[]
QED

Theorem canon_jnz_inst_successors_mem:
  MEM lbl (get_successors (canon_jnz_inst i)) ==>
  MEM lbl (get_successors i)
Proof
  simp[canon_jnz_inst_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `i.inst_opcode = JNZ /\ h' = h''` >> simp[] >>
  gvs[get_successors_def, is_terminator_def] >>
  Cases_on `h` >> Cases_on `h'` >> simp[venomStateTheory.get_label_def]
QED

Theorem subst_label_inst_successors_mem:
  MEM lbl (get_successors (subst_label_inst old new i)) <=>
  ?l. MEM l (get_successors i) /\ lbl = (if l = old then new else l)
Proof
  simp[subst_label_inst_def, get_successors_def] >>
  Cases_on `is_terminator i.inst_opcode` >> simp[] >>
  simp[MEM_MAP, MEM_FILTER, MAP_MAP_o, combinTheory.o_DEF] >>
  eq_tac >> rpt strip_tac
  >- (rename1 `MEM op i.inst_operands` >> Cases_on `op` >>
      gvs[subst_label_op_def, venomStateTheory.get_label_def] >>
      qexists_tac `s` >> Cases_on `s = old` >>
      simp[venomStateTheory.get_label_def] >>
      qexists_tac `SOME s` >> simp[] >>
      qexists_tac `Label s` >> simp[venomStateTheory.get_label_def]) >>
  rename1 `MEM op i.inst_operands` >> Cases_on `op` >>
  gvs[subst_label_op_def, venomStateTheory.get_label_def] >>
  qexists_tac `SOME (if l = old then new else l)` >> simp[] >>
  qexists_tac `Label (if l = old then new else l)` >>
  simp[venomStateTheory.get_label_def] >>
  qexists_tac `Label l` >> simp[subst_label_op_def] >>
  Cases_on `l = old` >> simp[]
QED

Theorem bypass_inst_successors_mem:
  MEM lbl (get_successors
    (if ~is_terminator i.inst_opcode then i
     else canon_jnz_inst (subst_label_inst old new i))) ==>
  ?l. MEM l (get_successors i) /\ lbl = (if l = old then new else l)
Proof
  Cases_on `is_terminator i.inst_opcode` >> simp[]
  >- (strip_tac >> drule canon_jnz_inst_successors_mem >>
      simp[subst_label_inst_successors_mem]) >>
  simp[get_successors_def]
QED

Theorem bb_succs_map_mem:
  !tr redirect. (!i l. MEM l (get_successors (tr i)) ==>
         ?k. MEM k (get_successors i) /\ l = redirect k) ==>
  !bb lbl. MEM lbl
    (bb_succs (bb with bb_instructions := MAP tr bb.bb_instructions)) ==>
    ?l. MEM l (bb_succs bb) /\ lbl = redirect l
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> Cases_on `bb.bb_instructions` >>
  simp[bb_succs_def] >>
  qspecl_then [`h::t`, `tr`] mp_tac LAST_MAP >>
  (impl_tac >- simp[]) >>
  pure_rewrite_tac[MAP] >> disch_then SUBST1_TAC >>
  simp[MEM_nub] >> metis_tac[]
QED

Theorem bypass_block_successors_mem:
  MEM lbl (bb_succs
    (bb with bb_instructions := MAP (\i.
      if ~is_terminator i.inst_opcode then i
      else canon_jnz_inst (subst_label_inst old new i)) bb.bb_instructions)) ==>
  ?l. MEM l (bb_succs bb) /\ lbl = (if l = old then new else l)
Proof
  qspecl_then
    [`\i. if ~is_terminator i.inst_opcode then i else
       canon_jnz_inst (subst_label_inst old new i)`,
     `\l. if l = old then new else l`] mp_tac bb_succs_map_mem >>
  simp[bypass_inst_successors_mem]
QED

Theorem bb_succs_update_phi_bypass_map:
  bb_succs (bb with bb_instructions := MAP (update_phi_bypass a b) insts) =
  bb_succs (bb with bb_instructions := insts)
Proof
  Cases_on `insts` >> simp[bb_succs_def] >>
  qspecl_then [`h::t`, `update_phi_bypass a b`] mp_tac LAST_MAP >>
  (impl_tac >- simp[]) >> pure_rewrite_tac[MAP] >>
  disch_then SUBST1_TAC >> simp[update_phi_bypass_successors]
QED

Theorem do_merge_jump_successor_cases:
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb fn'.fn_blocks /\ MEM lbl (bb_succs bb) ==>
  (?old. MEM old fn.fn_blocks /\ old.bb_label <> b.bb_label /\
         old.bb_label <> a.bb_label /\ MEM lbl (bb_succs old)) \/
  (?target l. bb_succs b = [target] /\ MEM l (bb_succs a) /\
              lbl = (if l = b.bb_label then target else l))
Proof
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `lookup_block target_lbl fn.fn_blocks = SOME target` >>
  `MEM target fn.fn_blocks /\ target.bb_label = target_lbl` by
    metis_tac[lookup_block_member_label] >>
  qmatch_asmsub_abbrev_tac `replace_block a.bb_label source
    (replace_block target_lbl dest rest)` >>
  `bb_succs dest = bb_succs target` by
    (simp[Abbr `dest`] >> irule bb_succs_map_preserve >>
     simp[update_phi_bypass_successors]) >>
  `!l. MEM l (bb_succs source) ==>
    ?k. MEM k (bb_succs a) /\
      l = (if k = b.bb_label then target_lbl else k)` by
    (simp[Abbr `source`] >> Cases_on `target_lbl = a.bb_label` >>
     simp[bb_succs_update_phi_bypass_map, bypass_block_successors_mem]) >>
  `dest.bb_label = target_lbl` by simp[Abbr `dest`] >>
  gvs[replace_block_def, MEM_MAP] >>
  rename1 `MEM old rest` >>
  Cases_on `old.bb_label = target.bb_label` >> gvs[] >>
  Cases_on `target.bb_label = a.bb_label` >> gvs[] >>
  Cases_on `old.bb_label = a.bb_label` >>
  gvs[Abbr `rest`, remove_block_def, MEM_FILTER] >> metis_tac[]
QED

Theorem do_merge_jump_first_no_preds:
  ALL_DISTINCT (fn_labels fn) /\
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  first_block_no_preds fn'
Proof
  strip_tac >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (irule do_merge_jump_entry_label >> metis_tac[]) >>
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  simp[first_block_no_preds_def, EVERY_MEM] >> rpt strip_tac >>
  drule_all do_merge_jump_successor_cases >> strip_tac
  >- metis_tac[incoming_not_entry] >>
  Cases_on `l = b.bb_label` >> gvs[] >>
  metis_tac[incoming_not_entry, MEM]
QED

Theorem do_merge_jump_labels:
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  fn_labels fn' = FILTER (\l. l <> b.bb_label) (fn_labels fn)
Proof
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `lookup_block target_lbl fn.fn_blocks = SOME target` >>
  `target.bb_label = target_lbl` by metis_tac[lookup_block_member_label] >>
  simp[fn_labels_def, fn_labels_replace_block, fn_labels_remove_block]
QED

Theorem do_merge_jump_succs_closed:
  ALL_DISTINCT (fn_labels fn) /\
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\ fn_succs_closed fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  fn_succs_closed fn'
Proof
  strip_tac >>
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  drule do_merge_jump_labels >> strip_tac >>
  simp[fn_succs_closed_def] >> rpt gen_tac >> strip_tac >>
  drule_all do_merge_jump_successor_cases >> strip_tac
  >- (simp[MEM_FILTER] >> reverse conj_tac
      >- metis_tac[fn_succs_closed_def] >> strip_tac >>
      `old = a` by (irule num_preds_one_unique >>
        gvs[can_bypass_jump_def] >> metis_tac[]) >> gvs[]) >>
  Cases_on `l = b.bb_label` >> gvs[MEM_FILTER]
  >- (reverse conj_tac
      >- metis_tac[fn_succs_closed_def, MEM] >> strip_tac >>
      `b = a` by (irule num_preds_one_unique >>
        gvs[can_bypass_jump_def] >> metis_tac[]) >>
      gvs[can_bypass_jump_def]) >>
  metis_tac[fn_succs_closed_def]
QED

Theorem try_bypass_result_cases:
  !succs fn lm a fn' lm' changed.
  try_bypass fn lm a succs = (fn',lm',changed) ==>
  (fn' = fn /\ lm' = lm /\ ~changed) \/
  (?b. lookup_block b.bb_label fn.fn_blocks = SOME b /\
       can_bypass_jump fn a b /\
       do_merge_jump fn a b lm = SOME (fn',lm') /\ changed)
Proof
  Induct >> simp[try_bypass_def] >> rpt gen_tac >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block h fn.fn_blocks = SOME b` >>
  `b.bb_label = h` by metis_tac[lookup_block_member_label] >>
  Cases_on `can_bypass_jump fn a b` >> simp[] >>
  Cases_on `lookup_block (HD (bb_succs b)) fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block (HD (bb_succs b)) fn.fn_blocks = SOME target` >>
  Cases_on `phi_values_agree a.bb_label b.bb_label target.bb_instructions` >> simp[] >>
  Cases_on `do_merge_jump fn a b lm` >> simp[] >>
  PairCases_on `x` >> simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem try_bypass_blocks_nonempty:
  ALL_DISTINCT (fn_labels fn) /\
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\ fn_succs_closed fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn',lm',changed) ==>
  fn'.fn_blocks <> []
Proof
  strip_tac >> drule try_bypass_result_cases >> strip_tac >> gvs[] >>
  metis_tac[do_merge_jump_blocks_nonempty]
QED

Theorem try_bypass_entry_label:
  ALL_DISTINCT (fn_labels fn) /\
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\ fn_succs_closed fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn',lm',changed) ==>
  (HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label
Proof
  strip_tac >> drule try_bypass_result_cases >> strip_tac >> gvs[] >>
  metis_tac[do_merge_jump_entry_label]
QED

Theorem try_bypass_first_no_preds:
  ALL_DISTINCT (fn_labels fn) /\
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\ fn_succs_closed fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn',lm',changed) ==>
  first_block_no_preds fn'
Proof
  strip_tac >> drule try_bypass_result_cases >> strip_tac >> gvs[] >>
  metis_tac[do_merge_jump_first_no_preds]
QED

Theorem try_bypass_succs_closed:
  ALL_DISTINCT (fn_labels fn) /\
  fn.fn_blocks <> [] /\ first_block_no_preds fn /\ fn_succs_closed fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn',lm',changed) ==>
  fn_succs_closed fn'
Proof
  strip_tac >> drule try_bypass_result_cases >> strip_tac >> gvs[] >>
  metis_tac[do_merge_jump_succs_closed]
QED
