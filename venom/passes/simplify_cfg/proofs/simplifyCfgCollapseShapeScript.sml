(* The relaxed structural invariant shared by both DFS traversals. *)
Theory simplifyCfgCollapseShape
Ancestors
  simplifyCfgLocalShape simplifyCfgGraphShape simplifyCfgPhiShape
  simplifyCfgReferences simplifyCfgLabelProps simplifyCfgInvariant
  simplifyCfgDefs venomWf venomInst unitShapeDefs cfgTransformProps list rich_list

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
