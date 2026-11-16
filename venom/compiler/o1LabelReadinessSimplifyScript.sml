Theory o1LabelReadinessSimplify
Ancestors
  o1LabelReadinessCfgNorm simplifyCfgInvariant simplifyCfgPhiShape
  simplifyCfgLabelProps o1PassContract venomPassDispatcher
  simplifyCfgDefs cfgTransform unitShapeDefs venomInst list rich_list

Theorem subst_inst_label_absent[local]:
  ~MEM (Label l) i.inst_operands /\ new <> l ==>
  ~MEM (Label l) (subst_label_inst old new i).inst_operands
Proof
  simp[subst_label_inst_label] >> metis_tac[]
QED

Theorem canon_inst_label_absent[local]:
  ~MEM (Label l) i.inst_operands ==>
  ~MEM (Label l) (canon_jnz_inst i).inst_operands
Proof
  Cases_on `canon_jnz_inst i = i` >- simp[] >>
  drule simplifyCfgShapeTheory.canon_jnz_inst_changed >> strip_tac >> simp[]
QED

Theorem fix_inst_label_absent[local]:
  ~MEM (Label l) i.inst_operands ==>
  ~MEM (Label l) (fix_phi_inst ps i).inst_operands
Proof
  rw[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops ps i.inst_operands` >> gvs[] >>
  rename1 `_ = h::rest` >> Cases_on `rest` >> gvs[]
  >- metis_tac[MEM_filter_phi_ops, MEM] >>
  rename1 `_ = h::h'::rest` >> Cases_on `rest` >> gvs[] >>
  metis_tac[MEM_filter_phi_ops, MEM]
QED

Theorem bypass_inst_label_absent[local]:
  ~MEM (Label l) i.inst_operands /\ a <> l ==>
  ~MEM (Label l) (update_phi_bypass a b i).inst_operands
Proof
  rw[update_phi_bypass_def] >> gvs[MEM_MAP, AllCaseEqs()] >>
  metis_tac[simplifyCfgShapeTheory.remove_phi_label_member]
QED

Theorem cfg_absent_lookup[local]:
  cfg_label_absent l f /\ lookup_block k f.fn_blocks = SOME bb ==>
  bb.bb_label <> l /\ EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions
Proof
  strip_tac >> drule lookup_block_member_label >>
  gvs[cfg_label_absent_def, EVERY_MEM] >> metis_tac[]
QED

Theorem cfg_absent_remove[local]:
  cfg_label_absent l f ==> cfg_label_absent l (remove_unreachable_blocks f)
Proof
  Cases_on `fn_entry_label f` >>
  simp[remove_unreachable_blocks_def, cfg_label_absent_def, EVERY_MEM, MEM_FILTER] >>
  metis_tac[]
QED

Theorem cfg_absent_fix[local]:
  cfg_label_absent l f ==> cfg_label_absent l (fix_all_phis f)
Proof
  simp[cfg_label_absent_def, fix_all_phis_def, EVERY_MEM, MEM_MAP,
       fix_phis_in_block_def, MEM_FILTER, PULL_EXISTS] >>
  metis_tac[fix_inst_label_absent]
QED

Theorem cfg_absent_merge[local]:
  a.bb_label <> l /\ EVERY (\i. ~MEM (Label l) i.inst_operands) a.bb_instructions /\
  EVERY (\i. ~MEM (Label l) i.inst_operands) b.bb_instructions ==>
  (merge_blocks a b).bb_label <> l /\
  EVERY (\i. ~MEM (Label l) i.inst_operands) (merge_blocks a b).bb_instructions
Proof
  strip_tac >> conj_tac >- simp[merge_blocks_def] >>
  irule merge_blocks_every >> simp[]
QED

Theorem cfg_absent_succ_update[local]:
  !succs bbs. new <> l /\
  EVERY (\bb. bb.bb_label <> l /\ EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
  EVERY (\bb. bb.bb_label <> l /\ EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (update_succ_phi_labels old new bbs succs)
Proof
  Induct >> simp[update_succ_phi_labels_def] >> rpt strip_tac >>
  qpat_x_assum `!bbs. _` (mp_tac o SRULE [update_succ_phi_labels_def, LET_THM]) >>
  disch_then irule >> simp[] >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  irule replace_block_every >> simp[] >>
  drule lookup_block_member_label >> strip_tac >>
  fs[EVERY_MEM] >> simp[MEM_MAP, PULL_EXISTS] >>
  rpt strip_tac >> Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  metis_tac[subst_inst_label_absent]
QED

Theorem cfg_absent_chain[local]:
  cfg_label_absent l f /\ lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b ==>
  cfg_label_absent l (f with fn_blocks := update_succ_phi_labels next lbl
    (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
    (bb_succs (merge_blocks a b)))
Proof
  strip_tac >>
  `a.bb_label <> l /\ EVERY (\i. ~MEM (Label l) i.inst_operands) a.bb_instructions` by
    metis_tac[cfg_absent_lookup] >>
  `b.bb_label <> l /\ EVERY (\i. ~MEM (Label l) i.inst_operands) b.bb_instructions` by
    metis_tac[cfg_absent_lookup] >>
  `lbl = a.bb_label` by metis_tac[lookup_block_member_label] >>
  simp[cfg_label_absent_def] >> irule cfg_absent_succ_update >> simp[] >>
  irule replace_block_every >> conj_tac
  >- (simp[] >> metis_tac[cfg_absent_merge]) >>
  irule remove_block_every >> fs[cfg_label_absent_def]
QED

Theorem cfg_absent_bypass[local]:
  cfg_label_absent l f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  do_merge_jump f a b lm = SOME (g,lm') ==> cfg_label_absent l g
Proof
  strip_tac >>
  `a.bb_label <> l /\ EVERY (\i. ~MEM (Label l) i.inst_operands) a.bb_instructions` by
    metis_tac[cfg_absent_lookup] >>
  gvs[do_merge_jump_def, AllCaseEqs()] >>
  rename1 `lookup_block target_lbl f.fn_blocks = SOME target` >>
  `target.bb_label <> l /\ EVERY (\i. ~MEM (Label l) i.inst_operands) target.bb_instructions` by
    metis_tac[cfg_absent_lookup] >>
  `target_lbl = target.bb_label` by metis_tac[lookup_block_member_label] >>
  simp[cfg_label_absent_def] >> irule replace_block_every >> conj_tac
  >- (simp[EVERY_MAP] >> Cases_on `target.bb_label = a.bb_label` >>
      simp[EVERY_MAP] >> fs[EVERY_MEM] >> rpt strip_tac >>
      Cases_on `is_terminator i.inst_opcode` >> simp[] >>
      metis_tac[bypass_inst_label_absent, canon_inst_label_absent, subst_inst_label_absent]) >>
  irule replace_block_every >> conj_tac
  >- (simp[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[bypass_inst_label_absent]) >>
  irule remove_block_every >> fs[cfg_label_absent_def]
QED

Theorem cfg_absent_collapse[local]:
  !f lm vis lbl. cfg_label_absent l f ==> cfg_label_absent l (FST (collapse_dfs f lm vis lbl))
Proof
  ho_match_mp_tac collapse_dfs_preserves_predicate >>
  metis_tac[cfg_absent_bypass, cfg_absent_chain]
QED

Theorem map_inst_label_absent[local]:
  EVERY (\p. SND p <> l) lm /\ ~MEM (Label l) i.inst_operands ==>
  ~MEM (Label l) (subst_block_labels_inst lm i).inst_operands
Proof
  strip_tac >> Cases_on `is_block_label_opcode i.inst_opcode` >>
  simp[subst_block_labels_inst_def, subst_label_map_inst_def, MEM_MAP] >>
  rpt strip_tac >> rename1 `MEM op i.inst_operands` >> Cases_on `op` >>
  gvs[subst_label_map_op_def, AllCaseEqs()] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >> fs[EVERY_MEM] >> metis_tac[pairTheory.SND]
QED

Theorem cfg_absent_map[local]:
  EVERY (\p. SND p <> l) lm /\ cfg_label_absent l f ==>
  cfg_label_absent l (subst_block_labels_fn lm f)
Proof
  simp[cfg_label_absent_def, subst_block_labels_fn_def,
       subst_block_labels_block_def, EVERY_MEM, MEM_MAP, PULL_EXISTS] >>
  strip_tac >> gen_tac >> disch_tac >> gen_tac >> disch_tac >>
  irule map_inst_label_absent >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem cfg_absent_collapse_map[local]:
  cfg_label_absent l f /\ ALL_DISTINCT (fn_labels f) /\
  collapse_dfs f [] vis lbl = (g,lm,vis') ==>
  EVERY (\p. SND p <> l) lm
Proof
  strip_tac >>
  mp_tac (cj 1 collapse_events_joint) >>
  disch_then (qspecl_then [`f`, `[]`, `vis`, `lbl`] mp_tac) >>
  simp[collapse_dfs_result_def, collapse_result_events_def,
       fn_result_events_def] >> strip_tac >>
  drule label_event_trace_endpoints >>
  gvs[cfg_label_absent_def, fn_labels_def, EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem cfg_absent_round[local]:
  cfg_label_absent l f /\ ALL_DISTINCT (fn_labels f) ==>
  cfg_label_absent l (FST (simplify_cfg_round_with_labels f))
Proof
  strip_tac >> Cases_on `fn_entry_label f`
  >- simp[simplify_cfg_round_with_labels_def] >>
  rename1 `fn_entry_label f = SOME entry` >>
  `cfg_label_absent l (fix_all_phis (remove_unreachable_blocks f))` by
    metis_tac[cfg_absent_fix, cfg_absent_remove] >>
  `ALL_DISTINCT (fn_labels (fix_all_phis (remove_unreachable_blocks f)))` by
    (simp[fn_labels_fix_all_phis] >>
     irule fn_labels_remove_unreachable_all_distinct >> simp[]) >>
  Cases_on `collapse_dfs (fix_all_phis (remove_unreachable_blocks f)) [] [] entry` >>
  PairCases_on `r` >>
  `cfg_label_absent l q` by metis_tac[cfg_absent_collapse, pairTheory.FST] >>
  `EVERY (\p. SND p <> l) r0` by metis_tac[cfg_absent_collapse_map] >>
  simp[simplify_cfg_round_with_labels_def] >>
  Cases_on `r0 = []` >> simp[] >>
  metis_tac[cfg_absent_fix, cfg_absent_remove, cfg_absent_map]
QED

Theorem cfg_absent_iter:
  !n f. cfg_label_absent l f /\ ALL_DISTINCT (fn_labels f) ==>
  cfg_label_absent l (FST (simplify_cfg_iter_with_labels n f))
Proof
  Induct >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  `cfg_label_absent l (FST (simplify_cfg_round_with_labels f))` by
    metis_tac[cfg_absent_round] >>
  `ALL_DISTINCT (fn_labels (FST (simplify_cfg_round_with_labels f)))` by
    (drule simplify_cfg_round_with_labels_transition >>
     simp[label_map_transition_def]) >>
  Cases_on `simplify_cfg_round_with_labels f` >> fs[] >>
  simp[simplify_cfg_iter_with_labels_def] >>
  Cases_on `q.fn_blocks = f.fn_blocks` >> simp[] >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> simp[] >> metis_tac[pairTheory.FST]
QED

Theorem simplify_pass_no_runtime_begin:
 !rpolicy observed s fn out.
 fn_pass_step rpolicy (CFP_Simple VP_SimplifyCFG) observed s fn out /\
 o1_fn_shape observed.cu_context fn /\
 (!i. MEM i (fn_insts fn) ==> ~MEM (Label "runtime_begin") i.inst_operands) ==>
 !i. MEM i (fn_insts out.fpo_function) ==> ~MEM (Label "runtime_begin") i.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  `cfg_label_absent "runtime_begin" fn /\ ALL_DISTINCT (fn_labels fn)` by
    (gvs[cfg_label_absent_def, o1_fn_shape_def, fn_shape_ok_def,
         venomWfTheory.wf_function_def, EVERY_MEM, reserved_label_def] >>
     rpt strip_tac >>
     `MEM i (fn_insts fn)` by
       (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
     metis_tac[]) >>
  `cfg_label_absent "runtime_begin" (FST (simplify_cfg_fn_with_labels fn))` by
    (simp[simplify_cfg_fn_with_labels_def] >> irule cfg_absent_iter >> simp[]) >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_def, AllCaseEqs()] >>
  fs[cfg_label_absent_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >>
  metis_tac[]
QED
