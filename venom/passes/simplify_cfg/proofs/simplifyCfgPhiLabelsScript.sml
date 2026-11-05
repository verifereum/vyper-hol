Theory simplifyCfgPhiLabels
Ancestors
  simplifyCfgCollapseShape simplifyCfgGraphShape simplifyCfgLocalShape
  simplifyCfgReferences cfgTransformProps
  simplifyCfgInvariant simplifyCfgWfssa
  simplifyCfgPhiRepair simplifyCfgPhiShape simplifyCfgStruct simplifyCfgDefs simplifyCfgLabelProps
  venomWf venomInst venomExecProofs cfgTransform list rich_list

val phi_distinct = ``\f. !i. MEM i (fn_insts f) /\ i.inst_opcode = PHI ==>
  ALL_DISTINCT (MAP FST (phi_pairs i.inst_operands))``;

Theorem removed_label_edges_closed:
  fn_succs_closed f /\
  fn_labels g = FILTER (\l. l <> removed) (fn_labels f) /\
  (!bb. MEM bb f.fn_blocks /\ MEM removed (bb_succs bb) ==> bb = a) /\
  (!out l. MEM out g.fn_blocks /\ MEM l (bb_succs out) ==>
    (?old. MEM old f.fn_blocks /\ old <> a /\ MEM l (bb_succs old)) \/
    (l <> removed /\ ?old. MEM old f.fn_blocks /\ MEM l (bb_succs old))) ==>
  fn_succs_closed g
Proof
  strip_tac >> simp[fn_succs_closed_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[MEM_FILTER] >> metis_tac[fn_succs_closed_def]
QED

Theorem chain_merge_edge_origin:
  ALL_DISTINCT (fn_labels f) /\ can_merge_blocks f a b /\
  b.bb_instructions <> [] /\ MEM b f.fn_blocks /\
  g = f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks))
      (bb_succs (merge_blocks a b)) ==>
  !out l. MEM out g.fn_blocks /\ MEM l (bb_succs out) ==>
    ?old. MEM old f.fn_blocks /\ old <> a /\ MEM l (bb_succs old)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label f.fn_blocks)))` by
    (simp[fn_labels_replace_block, merge_blocks_def] >>
     irule ALL_DISTINCT_remove_block >> gvs[fn_labels_def]) >>
  `EVERY (\out. !l. MEM l (bb_succs out) ==>
    ?old. MEM old f.fn_blocks /\ old <> a /\ MEM l (bb_succs old))
    g.fn_blocks` suffices_by (simp[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `g = _` SUBST1_TAC >> simp[] >>
  irule (BETA_RULE (Q.INST [`P` |-> `\lab succs. !l. MEM l succs ==>
    ?old. MEM old f.fn_blocks /\ old <> a /\ MEM l (bb_succs old)`]
    update_succ_phi_labels_graph_every)) >>
  conj_tac >- first_x_assum ACCEPT_TAC >>
  pure_rewrite_tac[replace_block_def, remove_block_def, EVERY_MAP, EVERY_FILTER] >>
  simp[EVERY_MEM] >> rpt strip_tac >> rename1 `MEM bb f.fn_blocks` >>
  Cases_on `bb.bb_label = a.bb_label` >>
  gvs[merge_blocks_succs] >> metis_tac[can_merge_blocks_def]
QED

Theorem bypass_edge_origin:
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_bypass_jump f a b /\ do_merge_jump f a b lm = SOME (g,lm') ==>
  !out l. MEM out g.fn_blocks /\ MEM l (bb_succs out) ==>
    (?old. MEM old f.fn_blocks /\ old <> a /\ MEM l (bb_succs old)) \/
    (l <> b.bb_label /\ ?old. MEM old f.fn_blocks /\ MEM l (bb_succs old))
Proof
  strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `a.bb_label <> b.bb_label` by
    metis_tac[simplifyCfgShapeTheory.can_bypass_jump_source_distinct] >>
  rpt gen_tac >> strip_tac >>
  drule_all do_merge_jump_successor_cases >> strip_tac
  >- (disj1_tac >> qexists_tac `old` >> metis_tac[]) >>
  Cases_on `l' = b.bb_label` >> gvs[] >> metis_tac[MEM]
QED

Theorem chain_merge_edges_closed:
  ALL_DISTINCT (fn_labels f) /\ fn_succs_closed f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_merge_blocks f a b /\ b.bb_instructions <> [] /\
  g = f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks))
      (bb_succs (merge_blocks a b)) ==> fn_succs_closed g
Proof
  strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `fn_labels g = FILTER (\l. l <> b.bb_label) (fn_labels f)` by
    (gvs[] >> simp[fn_labels_def, fn_labels_update_succ_phi_labels,
      fn_labels_replace_block, merge_blocks_def, fn_labels_remove_block]) >>
  `!bb. MEM bb f.fn_blocks /\ MEM b.bb_label (bb_succs bb) ==> bb = a` by
    (rpt strip_tac >> irule simplifyCfgGraphShapeTheory.num_preds_one_unique >>
     gvs[can_merge_blocks_def] >> metis_tac[MEM]) >>
  irule removed_label_edges_closed >>
  qexistsl_tac [`a`, `f`, `b.bb_label`] >> simp[] >>
  rpt strip_tac >> disj1_tac >> irule chain_merge_edge_origin >>
  simp[] >> qexistsl_tac [`b`, `out`] >> simp[]
QED

Theorem bypass_edges_closed:
  ALL_DISTINCT (fn_labels f) /\ fn_succs_closed f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_bypass_jump f a b /\ do_merge_jump f a b lm = SOME (g,lm') ==>
  fn_succs_closed g
Proof
  strip_tac >>
  `MEM a f.fn_blocks` by metis_tac[lookup_block_member_label] >>
  drule do_merge_jump_labels >> strip_tac >>
  `!bb. MEM bb f.fn_blocks /\ MEM b.bb_label (bb_succs bb) ==> bb = a` by
    (rpt strip_tac >> irule simplifyCfgGraphShapeTheory.num_preds_one_unique >>
     gvs[can_bypass_jump_def] >> metis_tac[]) >>
  irule removed_label_edges_closed >>
  qexistsl_tac [`a`, `f`, `b.bb_label`] >> simp[] >>
  mp_tac bypass_edge_origin >> simp[]
QED

Theorem fix_phi_inst_phi_distinct:
  phi_well_formed i.inst_operands /\
  ALL_DISTINCT (MAP FST (phi_pairs i.inst_operands)) /\
  i.inst_opcode = PHI /\ (fix_phi_inst ps i).inst_opcode = PHI ==>
  ALL_DISTINCT (MAP FST (phi_pairs (fix_phi_inst ps i).inst_operands))
Proof
  strip_tac >> drule_all fix_phi_inst_surviving_pairs >>
  disch_then SUBST1_TAC >>
  `!xs : (string # string) list. ALL_DISTINCT (MAP FST xs) ==>
    ALL_DISTINCT (MAP FST (FILTER (\p. MEM (FST p) ps) xs))` suffices_by metis_tac[] >>
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `MEM (FST h) ps` >> simp[] >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem remove_unreachable_blocks_phi_distinct:
  ^phi_distinct f ==> ^phi_distinct (remove_unreachable_blocks f)
Proof
  BETA_TAC >> strip_tac >> pure_rewrite_tac [GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac (GEN_ALL remove_unreachable_blocks_inst_property) >> simp[]
QED

Theorem fix_all_phis_phi_distinct:
  EVERY inst_wf (fn_insts f) /\ ^phi_distinct f ==>
  ^phi_distinct (fix_all_phis f)
Proof
  BETA_TAC >>
  simp[fn_insts_def, fn_insts_blocks_mem, fix_all_phis_def,
    MEM_MAP, PULL_EXISTS, fix_phis_in_block_member, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >>
  rename1 `(fix_phi_inst ps inst).inst_opcode = PHI` >>
  `inst.inst_opcode = PHI` by
    (spose_not_then assume_tac >> gvs[fix_phi_inst_non_phi]) >>
  `inst_wf inst` by metis_tac[] >>
  `ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))` by metis_tac[] >>
  irule fix_phi_inst_phi_distinct >> gvs[inst_wf_def]
QED

Theorem phi_preds_exclude_single_succ:
  ALL_DISTINCT (fn_labels f) /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label)) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  bb_succs a = [target] /\ MEM bb f.fn_blocks /\
  bb.bb_label <> target /\ MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_well_formed i.inst_operands ==>
  ~MEM a.bb_label (MAP FST (phi_pairs i.inst_operands))
Proof
  strip_tac >> strip_tac >>
  `MEM (Label a.bb_label) i.inst_operands` by
    metis_tac[phi_pair_label_mem] >>
  `MEM a.bb_label (pred_labels f bb.bb_label)` by metis_tac[] >>
  drule_all pred_labels_lookup_edge >> simp[]
QED

Theorem chain_merge_phi_distinct_relaxed:
  ALL_DISTINCT (fn_labels f) /\ EVERY inst_wf (fn_insts f) /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label)) /\ ^phi_distinct f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  ^phi_distinct (f with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks))
    (bb_succs (merge_blocks a b)))
Proof
  BETA_TAC >> strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `no_phis b /\ bb_succs a = [b.bb_label]` by fs[can_merge_blocks_def] >>
  simp[fn_insts_def, fn_insts_blocks_mem] >> rpt strip_tac >>
  rename1 `MEM i bb.bb_instructions` >>
  `bb.bb_label <> b.bb_label` by
    (qmatch_asmsub_abbrev_tac `MEM bb bs` >>
     `MEM bb.bb_label (fn_labels (f with fn_blocks := bs))` by
       (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
     fs[Abbr `bs`, chain_merge_fn_labels, MEM_FILTER]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks)))`
    by simp[chain_merge_base_labels] >>
  drule_all update_succ_phi_labels_phi_source_exact >> strip_tac >>
  drule_all chain_merge_phi_origin >> strip_tac >>
  `inst_wf inst` by (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  `ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))` by
    (fs[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  `~MEM a.bb_label (MAP FST (phi_pairs inst.inst_operands))` by
    (irule phi_preds_exclude_single_succ >> metis_tac[]) >>
  drule_all phi_subst_label_distinct >>
  disch_then (qspec_then `b.bb_label` assume_tac) >>
  Cases_on `MEM bb.bb_label (bb_succs (merge_blocks a b))` >> gvs[]
QED

Theorem do_merge_jump_phi_distinct_relaxed:
  ALL_DISTINCT (fn_labels f) /\ EVERY inst_wf (fn_insts f) /\
  ^phi_distinct f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==> ^phi_distinct g
Proof
  BETA_TAC >> strip_tac >> simp[fn_insts_def, fn_insts_blocks_mem] >>
  rpt strip_tac >> drule_all do_merge_jump_phi_origin >> strip_tac >>
  `inst_wf oi` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  `phi_well_formed oi.inst_operands` by gvs[inst_wf_def] >>
  `ALL_DISTINCT (MAP FST (phi_pairs oi.inst_operands))` by
    (fs[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  Cases_on `MEM orig.bb_label (bb_succs b)` >> gvs[] >>
  irule update_phi_bypass_distinct >> simp[]
QED

val collapse_shape = ``\f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  fn_succs_closed f /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label))``;

Theorem chain_merge_phi_shape:
  ^collapse_shape f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  ^collapse_shape (f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label f.fn_blocks))
      (bb_succs (merge_blocks a b)))
Proof
  BETA_TAC >> strip_tac >>
  `b.bb_instructions <> []` by
    (drule lookup_block_member_label >> strip_tac >>
     gvs[EVERY_MEM, bb_well_formed_def]) >>
  conj_tac >- (irule chain_merge_distinct_labels >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_blocks_nonempty >> metis_tac[]) >>
  conj_tac >- (simp[] >> irule chain_merge_bb_well_formed >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_inst_wf >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_label_positions >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_edges_closed >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> irule chain_merge_phi_preds >> metis_tac[]
QED

Theorem bypass_phi_shape:
  ^collapse_shape f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  do_merge_jump f a b lm = SOME (g,lm') ==> ^collapse_shape g
Proof
  BETA_TAC >> strip_tac >>
  `bb_well_formed a` by metis_tac[lookup_block_member_label, EVERY_MEM] >>
  conj_tac >- (drule do_merge_jump_labels >> simp[FILTER_ALL_DISTINCT]) >>
  conj_tac >- (irule do_merge_jump_blocks_nonempty >> metis_tac[]) >>
  conj_tac >- (irule do_merge_jump_bb_well_formed >> metis_tac[]) >>
  conj_tac >- (irule do_merge_jump_inst_wf >> metis_tac[]) >>
  conj_tac >- (irule do_merge_jump_label_positions >> metis_tac[]) >>
  conj_tac >- (irule bypass_edges_closed >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> irule do_merge_jump_phi_preds >> metis_tac[]
QED

Theorem collapse_dfs_phi_distinct_joint:
  (!f lm vis lbl. ^collapse_shape f /\ ^phi_distinct f ==>
    ^collapse_shape (FST (collapse_dfs f lm vis lbl)) /\
    ^phi_distinct (FST (collapse_dfs f lm vis lbl))) /\
  (!f lm vis succs. ^collapse_shape f /\ ^phi_distinct f ==>
    ^collapse_shape (FST (collapse_dfs_succs f lm vis succs)) /\
    ^phi_distinct (FST (collapse_dfs_succs f lm vis succs)))
Proof
  ho_match_mp_tac collapse_dfs_preserves_predicate_joint >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (irule bypass_phi_shape >> metis_tac[]) >>
      irule do_merge_jump_phi_distinct_relaxed >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`a.bb_label = lbl /\ b.bb_label = next` by
        metis_tac[lookup_block_member_label] >>
      qpat_x_assum `a.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `b.bb_label = next` (SUBST_ALL_TAC o SYM) >>
      BETA_TAC >> irule (BETA_RULE chain_merge_phi_shape) >> fs[] >> metis_tac[]) >>
  `a.bb_label = lbl /\ b.bb_label = next` by
    metis_tac[lookup_block_member_label] >>
  gvs[] >> metis_tac[BETA_RULE chain_merge_phi_distinct_relaxed]
QED

Theorem collapse_phi_empty_log_identity:
  ^collapse_shape f /\ ^phi_distinct f /\
  collapse_dfs f [] vis lbl = (g,lm,vis') ==>
  subst_block_labels_fn lm g = g
Proof
  strip_tac >>
  `^collapse_shape g /\ ^phi_distinct g` by
    (mp_tac (CONJUNCT1 collapse_dfs_phi_distinct_joint) >>
     disch_then drule >>
     disch_then (qspecl_then [`[]`, `vis`, `lbl`] mp_tac) >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels f)` by gvs[] >>
  drule_all collapse_dfs_empty_log_sources_absent >> strip_tac >>
  irule phi_preds_subst_block_labels_identity >> gvs[EVERY_MEM] >>
  metis_tac[pairTheory.FST]
QED

val structural_shape = ``\f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  fn_succs_closed f``;

Theorem remove_unreachable_phi_shape:
  ^structural_shape f /\ ^phi_distinct f ==>
  ^structural_shape (remove_unreachable_blocks f) /\
  ^phi_distinct (remove_unreachable_blocks f)
Proof
  BETA_TAC >> strip_tac >>
  drule simplifyCfgGraphShapeTheory.remove_unreachable_blocks_head >> strip_tac >>
  conj_tac
  >- (conj_tac >- (Cases_on `fn_entry_label f` >>
        gvs[remove_unreachable_blocks_def, fn_labels_def] >>
        `MAP (\bb. bb.bb_label) (FILTER (\bb. reachable f bb.bb_label) f.fn_blocks) =
         FILTER (reachable f) (MAP (\bb. bb.bb_label) f.fn_blocks)` by
          simp[FILTER_MAP, combinTheory.o_DEF] >>
        simp[FILTER_ALL_DISTINCT]) >>
      conj_tac >- simp[] >>
      conj_tac >- (irule remove_unreachable_blocks_bb_well_formed >> simp[]) >>
      conj_tac >- (irule remove_unreachable_blocks_every >> simp[]) >>
      conj_tac >- (irule remove_unreachable_blocks_every >> simp[]) >>
      irule remove_unreachable_blocks_succs_closed >> simp[]) >>
  metis_tac[remove_unreachable_blocks_phi_distinct]
QED

Theorem fix_all_phis_phi_shape:
  ^structural_shape f /\ ^phi_distinct f ==>
  ^collapse_shape (fix_all_phis f) /\ ^phi_distinct (fix_all_phis f)
Proof
  BETA_TAC >> strip_tac >>
  `MAP (\bb. (bb.bb_label, bb_succs bb)) (fix_all_phis f).fn_blocks =
   MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks` by
    (irule fix_all_phis_graph >> gvs[EVERY_MEM]) >>
  `fn_labels (fix_all_phis f) = fn_labels f /\
   (fix_all_phis f).fn_blocks <> []` by
    (Cases_on `f.fn_blocks` >>
     gvs[fix_all_phis_def, fn_labels_def, MAP_MAP_o,
       combinTheory.o_DEF, fix_phis_in_block_def]) >>
  conj_tac
  >- (conj_tac >- simp[] >> conj_tac >- simp[] >>
      conj_tac >- (irule fix_all_phis_bb_well_formed >> simp[]) >>
      conj_tac >- (irule fix_all_phis_inst_wf >> simp[]) >>
      conj_tac >- (irule fix_all_phis_label_positions >> simp[]) >>
      conj_tac
      >- (simp[fn_succs_closed_def] >> rpt gen_tac >> strip_tac >>
          `EVERY (\bb. !s. MEM s (bb_succs bb) ==> MEM s (fn_labels f))
             (fix_all_phis f).fn_blocks` by
            (ho_match_mp_tac (Q.INST [`bs2` |-> `f.fn_blocks`] block_graph_every) >>
             simp[fix_all_phis_graph, EVERY_MEM] >>
             metis_tac[fn_succs_closed_def]) >>
          gvs[EVERY_MEM] >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >> irule fix_all_phis_phi_preds >> gvs[] >>
      metis_tac[]) >>
  metis_tac[BETA_RULE fix_all_phis_phi_distinct]
QED

Theorem simplify_cfg_round_phi_distinct:
  ^structural_shape f /\ ^phi_distinct f ==>
  ^structural_shape (FST (simplify_cfg_round_with_labels f)) /\
  ^phi_distinct (FST (simplify_cfg_round_with_labels f))
Proof
  strip_tac >>
  `^structural_shape (remove_unreachable_blocks f) /\
   ^phi_distinct (remove_unreachable_blocks f)` by
    (irule remove_unreachable_phi_shape >> simp[]) >>
  `^collapse_shape (fix_all_phis (remove_unreachable_blocks f)) /\
   ^phi_distinct (fix_all_phis (remove_unreachable_blocks f))` by
    (irule fix_all_phis_phi_shape >> simp[]) >>
  Cases_on `fn_entry_label f`
  >- (Cases_on `f.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  qabbrev_tac `a = fix_all_phis (remove_unreachable_blocks f)` >>
  Cases_on `collapse_dfs a [] [] x` >> PairCases_on `r` >>
  `^collapse_shape q /\ ^phi_distinct q` by
    (mp_tac (CONJUNCT1 collapse_dfs_phi_distinct_joint) >>
     disch_then drule >>
     disch_then (qspecl_then [`[]`, `[]`, `x`] mp_tac) >> simp[] >> metis_tac[]) >>
  `subst_block_labels_fn r0 q = q` by
    (irule collapse_phi_empty_log_identity >> metis_tac[]) >>
  `^structural_shape q` by gvs[] >>
  `^structural_shape (remove_unreachable_blocks q) /\
   ^phi_distinct (remove_unreachable_blocks q)` by
    (irule remove_unreachable_phi_shape >> simp[]) >>
  `^collapse_shape (fix_all_phis (remove_unreachable_blocks q)) /\
   ^phi_distinct (fix_all_phis (remove_unreachable_blocks q))` by
    (irule fix_all_phis_phi_shape >> simp[]) >>
  simp[simplify_cfg_round_with_labels_def, Abbr `a`] >>
  Cases_on `r0 = []` >> simp[] >> metis_tac[]
QED

Theorem simplify_cfg_iter_phi_distinct:
  !n f. ^structural_shape f /\ ^phi_distinct f ==>
    ^structural_shape (FST (simplify_cfg_iter_with_labels n f)) /\
    ^phi_distinct (FST (simplify_cfg_iter_with_labels n f))
Proof
  Induct_on `n` >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  `^structural_shape (FST (simplify_cfg_round_with_labels f)) /\
   ^phi_distinct (FST (simplify_cfg_round_with_labels f))` by
    (irule simplify_cfg_round_phi_distinct >> simp[]) >>
  Cases_on `simplify_cfg_round_with_labels f` >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >> simp[] >>
  Cases_on `q.fn_blocks = f.fn_blocks` >- gvs[] >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> gvs[] >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED
