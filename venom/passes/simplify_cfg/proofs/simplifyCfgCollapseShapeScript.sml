(* The relaxed structural invariant shared by both DFS traversals. *)
Theory simplifyCfgCollapseShape
Ancestors
  simplifyCfgLocalShape simplifyCfgGraphShape simplifyCfgPhiShape
  simplifyCfgReferences simplifyCfgLabelProps simplifyCfgInvariant
  simplifyCfgDefs simplifyCfgShape venomWf venomInst unitShapeDefs
  cfgTransform cfgTransformProps list rich_list

(* Proof notation only: no new logical definition or invariant constant. *)
val collapse_shape = ``\e f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  first_block_no_preds f /\ fn_succs_closed f /\
  (!bb i l. MEM bb f.fn_blocks /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels f bb.bb_label)) /\
  (HD f.fn_blocks).bb_label = e``;

Theorem chain_merge_distinct_labels:
  ALL_DISTINCT (fn_labels f) /\
  g = f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks))
      (bb_succs (merge_blocks a b)) ==>
  ALL_DISTINCT (fn_labels g)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label f.fn_blocks)))` by
    (simp[fn_labels_replace_block, merge_blocks_def] >>
     irule ALL_DISTINCT_remove_block >> gvs[fn_labels_def]) >>
  gvs[fn_labels_def, update_succ_phi_labels_labels]
QED

Theorem chain_merge_collapse_shape:
  ^collapse_shape e f /\
  lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
  ^collapse_shape e (f with fn_blocks := update_succ_phi_labels next lbl
    (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
    (bb_succs (merge_blocks a b)))
Proof
  BETA_TAC >> strip_tac >>
  `a.bb_label = lbl /\ b.bb_label = next` by
    metis_tac[lookup_block_member_label] >>
  `b.bb_instructions <> []` by
    (drule lookup_block_member_label >> strip_tac >>
     gvs[EVERY_MEM, bb_well_formed_def]) >>
  conj_tac >- (irule chain_merge_distinct_labels >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_blocks_nonempty >> metis_tac[]) >>
  conj_tac >- (simp[] >> irule chain_merge_bb_well_formed >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_inst_wf >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_label_positions >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_first_no_preds >> metis_tac[]) >>
  conj_tac >- (irule chain_merge_succs_closed >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule chain_merge_phi_preds >> metis_tac[]) >>
  `(HD (f with fn_blocks := update_succ_phi_labels next lbl
    (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
    (bb_succs (merge_blocks a b))).fn_blocks).bb_label =
    (HD f.fn_blocks).bb_label` suffices_by simp[] >>
  irule chain_merge_entry_label >> metis_tac[]
QED

Theorem do_merge_jump_collapse_shape:
  ^collapse_shape e f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\ can_bypass_jump f a b /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  ^collapse_shape e g
Proof
  BETA_TAC >> strip_tac >>
  `bb_well_formed a` by
    metis_tac[lookup_block_member_label, EVERY_MEM] >>
  conj_tac >- (drule do_merge_jump_labels >> simp[FILTER_ALL_DISTINCT]) >>
  conj_tac >- (irule do_merge_jump_blocks_nonempty >> metis_tac[]) >>
  conj_tac >- (irule do_merge_jump_bb_well_formed >> metis_tac[]) >>
  conj_tac >- (irule do_merge_jump_inst_wf >> metis_tac[]) >>
  conj_tac >- (irule do_merge_jump_label_positions >> metis_tac[]) >>
  conj_tac >- (irule do_merge_jump_first_no_preds >> metis_tac[]) >>
  conj_tac >- (irule do_merge_jump_succs_closed >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule do_merge_jump_phi_preds >> metis_tac[]) >>
  `(HD g.fn_blocks).bb_label = (HD f.fn_blocks).bb_label` suffices_by simp[] >>
  irule do_merge_jump_entry_label >> metis_tac[]
QED

Theorem collapse_dfs_shape_joint:
  (!f lm vis lbl. ^collapse_shape e f ==>
    ^collapse_shape e (FST (collapse_dfs f lm vis lbl))) /\
  (!f lm vis succs. ^collapse_shape e f ==>
    ^collapse_shape e (FST (collapse_dfs_succs f lm vis succs)))
Proof
  irule collapse_dfs_preserves_predicate_joint >> reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule do_merge_jump_collapse_shape >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule chain_merge_collapse_shape >> metis_tac[]
QED

Theorem collapse_dfs_empty_log_subst_identity:
  ^collapse_shape e f /\
  collapse_dfs f [] vis lbl = (g,lm,vis') ==>
  subst_block_labels_fn lm g = g
Proof
  strip_tac >>
  `^collapse_shape e g` by
    (mp_tac (CONJUNCT1 collapse_dfs_shape_joint) >>
     disch_then drule >>
     disch_then (qspecl_then [`[]`, `vis`, `lbl`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels f)` by gvs[] >>
  drule_all collapse_dfs_empty_log_sources_absent >> strip_tac >>
  irule phi_preds_subst_block_labels_identity >> gvs[EVERY_MEM] >>
  metis_tac[pairTheory.FST]
QED

val structural_shape = ``\e f.
  ALL_DISTINCT (fn_labels f) /\ f.fn_blocks <> [] /\
  EVERY bb_well_formed f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\ EVERY label_positions_ok (fn_insts f) /\
  first_block_no_preds f /\ fn_succs_closed f /\
  (HD f.fn_blocks).bb_label = e``;

Theorem remove_unreachable_blocks_structural_shape:
  ^structural_shape e f ==>
  ^structural_shape e (remove_unreachable_blocks f)
Proof
  BETA_TAC >> strip_tac >>
  drule remove_unreachable_blocks_head >> strip_tac >>
  conj_tac >- (Cases_on `fn_entry_label f` >>
    gvs[remove_unreachable_blocks_def, fn_labels_def] >>
    `MAP (\bb. bb.bb_label) (FILTER (\bb. reachable f bb.bb_label) f.fn_blocks) =
     FILTER (reachable f) (MAP (\bb. bb.bb_label) f.fn_blocks)` by
      (simp[FILTER_MAP, combinTheory.o_DEF]) >>
    simp[FILTER_ALL_DISTINCT]) >>
  conj_tac >- simp[] >>
  conj_tac >- (irule remove_unreachable_blocks_bb_well_formed >> simp[]) >>
  conj_tac >- (irule remove_unreachable_blocks_every >> simp[]) >>
  conj_tac >- (irule remove_unreachable_blocks_every >> simp[]) >>
  conj_tac >- (irule remove_unreachable_blocks_first_no_preds >> simp[]) >>
  conj_tac >- (irule remove_unreachable_blocks_succs_closed >> simp[]) >>
  simp[]
QED

Theorem fix_all_phis_structural_shape:
  ^structural_shape e f ==>
  ^structural_shape e (fix_all_phis f)
Proof
  BETA_TAC >> strip_tac >>
  `MAP (\bb. (bb.bb_label, bb_succs bb)) (fix_all_phis f).fn_blocks =
   MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks` by
    (irule fix_all_phis_graph >> gvs[EVERY_MEM]) >>
  `fn_labels (fix_all_phis f) = fn_labels f /\
   (fix_all_phis f).fn_blocks <> [] /\
   (HD (fix_all_phis f).fn_blocks).bb_label = (HD f.fn_blocks).bb_label` by
    (Cases_on `f.fn_blocks` >>
     gvs[fix_all_phis_def, fn_labels_def, MAP_MAP_o,
       combinTheory.o_DEF, fix_phis_in_block_def]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- (irule fix_all_phis_bb_well_formed >> simp[]) >>
  conj_tac >- (irule fix_all_phis_inst_wf >> simp[]) >>
  conj_tac >- (irule fix_all_phis_label_positions >> simp[]) >>
  conj_tac
  >- (simp[first_block_no_preds_def] >>
      ho_match_mp_tac (Q.INST [`bs2` |-> `f.fn_blocks`] block_graph_every) >> simp[fix_all_phis_graph] >>
      gvs[first_block_no_preds_def]) >>
  conj_tac
  >- (simp[fn_succs_closed_def] >> rpt gen_tac >> strip_tac >>
      `EVERY (\bb. !s. MEM s (bb_succs bb) ==> MEM s (fn_labels f))
         (fix_all_phis f).fn_blocks` by
        (ho_match_mp_tac (Q.INST [`bs2` |-> `f.fn_blocks`] block_graph_every) >>
         simp[fix_all_phis_graph, EVERY_MEM] >>
         metis_tac[fn_succs_closed_def]) >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[]
QED

Theorem fix_all_phis_collapse_shape:
  ^structural_shape e f ==> ^collapse_shape e (fix_all_phis f)
Proof
  strip_tac >> drule fix_all_phis_structural_shape >>
  simp[] >> strip_tac >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> irule fix_all_phis_phi_preds >> gvs[] >>
  metis_tac[]
QED

Theorem fix_all_phis_entry_no_phi:
  f.fn_blocks <> [] /\ first_block_no_preds f /\
  EVERY inst_wf (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> PHI)
    (HD (fix_all_phis f).fn_blocks).bb_instructions
Proof
  strip_tac >>
  `pred_labels f (HD f.fn_blocks).bb_label = []` by
    (gvs[first_block_no_preds_def, pred_labels_def, block_preds_def,
       EVERY_MEM, FILTER_EQ_NIL]) >>
  Cases_on `f.fn_blocks` >> gvs[] >>
  simp[fix_all_phis_def, fix_phis_in_block_def, EVERY_APPEND,
       EVERY_FILTER, EVERY_MAP] >>
  simp[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
  `inst_wf i` by
    (gvs[fn_insts_def, fn_insts_blocks_def, EVERY_MEM] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = PHI`
  >- (drule fix_phi_inst_empty_preds >>
      gvs[inst_wf_def]) >>
  gvs[fix_phi_inst_def]
QED

Theorem simplify_cfg_round_collapse_shape:
  ^structural_shape e f ==>
  ^collapse_shape e (FST (simplify_cfg_round_with_labels f)) /\
  EVERY (\i. i.inst_opcode <> PHI)
    (HD (FST (simplify_cfg_round_with_labels f)).fn_blocks).bb_instructions
Proof
  strip_tac >>
  `^structural_shape e (remove_unreachable_blocks f)` by
    (irule remove_unreachable_blocks_structural_shape >> simp[]) >>
  `^collapse_shape e (fix_all_phis (remove_unreachable_blocks f))` by
    (irule fix_all_phis_collapse_shape >> simp[]) >>
  Cases_on `fn_entry_label f`
  >- (Cases_on `f.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  qabbrev_tac `a = fix_all_phis (remove_unreachable_blocks f)` >>
  Cases_on `collapse_dfs a [] [] x` >>
  PairCases_on `r` >>
  `^collapse_shape e q` by
    (mp_tac (CONJUNCT1 collapse_dfs_shape_joint) >>
     disch_then drule >>
     disch_then (qspecl_then [`[]`, `[]`, `x`] mp_tac) >> simp[] >> metis_tac[]) >>
  `subst_block_labels_fn r0 q = q` by
    (irule collapse_dfs_empty_log_subst_identity >> metis_tac[]) >>
  `^structural_shape e q` by gvs[] >>
  `^structural_shape e (remove_unreachable_blocks q)` by
    (irule remove_unreachable_blocks_structural_shape >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> PHI)
    (HD (fix_all_phis (remove_unreachable_blocks q)).fn_blocks).bb_instructions` by
    (irule fix_all_phis_entry_no_phi >> gvs[]) >>
  drule_all fix_all_phis_collapse_shape >>
  simp[simplify_cfg_round_with_labels_def, Abbr `a`] >>
  Cases_on `r0 = []` >> simp[] >> metis_tac[]
QED


Theorem simplify_cfg_round_label_refs_ok:
  ^structural_shape e f ==>
  fn_label_refs_ok (FST (simplify_cfg_round_with_labels f))
Proof
  strip_tac >> drule simplify_cfg_round_collapse_shape >> strip_tac >>
  irule phi_preds_label_refs_ok >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem simplify_cfg_round_empty:
  f.fn_blocks = [] ==> simplify_cfg_round_with_labels f = (f,[])
Proof
  simp[simplify_cfg_round_with_labels_def, fn_entry_label_def, entry_block_def]
QED

val iteration_shape = ``\e f. ^structural_shape e f /\ fn_label_refs_ok f /\
  EVERY (\i. i.inst_opcode <> PHI) (HD f.fn_blocks).bb_instructions``;

Theorem simplify_cfg_iter_structural_shape:
  !n f. ^iteration_shape e f ==>
    ^iteration_shape e (FST (simplify_cfg_iter_with_labels n f))
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  `^structural_shape e f` by gvs[] >>
  drule simplify_cfg_round_collapse_shape >> strip_tac >>
  drule simplify_cfg_round_label_refs_ok >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels f` >> fs[] >>
  `^iteration_shape e q` by gvs[] >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >> simp[] >>
  Cases_on `q.fn_blocks = f.fn_blocks`
  >- simp[] >>
  first_x_assum drule >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> simp[] >> metis_tac[]
QED

Theorem simplify_cfg_fn_structural_shape:
  ^iteration_shape e f ==>
  ^iteration_shape e (FST (simplify_cfg_fn_with_labels f))
Proof
  rewrite_tac[simplify_cfg_fn_with_labels_def] >>
  strip_tac >> drule simplify_cfg_iter_structural_shape >>
  disch_then (qspec_then `LENGTH f.fn_blocks` mp_tac) >> simp[]
QED
