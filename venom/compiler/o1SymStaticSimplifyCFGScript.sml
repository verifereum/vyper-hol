Theory o1SymStaticSimplifyCFG
Ancestors
  o1ContractSimplifyCfgStep simplifyCfgInvariant simplifyCfgLabelProps
  simplifyCfgReferences cfgTransformProps simplifyCfgDefs cfgTransform
  venomInst list o1PassContract unitShapeDefs

Theorem fix_phi_inst_label_subset:
  MEM (Label l) (fix_phi_inst ps i).inst_operands ==>
  MEM (Label l) i.inst_operands
Proof
  Cases_on `i.inst_opcode = PHI` >> simp[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops ps i.inst_operands` >> simp[] >>
  rename1 `h::t` >> Cases_on `t`
  >- (simp[] >> metis_tac[MEM_filter_phi_ops, MEM]) >>
  rename1 `h::k::rest` >> Cases_on `rest` >> simp[] >>
  metis_tac[MEM_filter_phi_ops, MEM]
QED

Theorem canon_jnz_inst_label_subset:
  MEM (Label l) (canon_jnz_inst i).inst_operands ==>
  MEM (Label l) i.inst_operands
Proof
  simp[canon_jnz_inst_def] >> rpt CASE_TAC >> gvs[] >> metis_tac[]
QED

Theorem subst_label_inst_label_absent:
  b <> l /\ ~MEM (Label l) i.inst_operands ==>
  ~MEM (Label l) (subst_label_inst a b i).inst_operands
Proof
  simp[subst_label_inst_def, MEM_MAP] >> rpt strip_tac >>
  rename1 `MEM operand i.inst_operands` >>
  Cases_on `operand` >> gvs[subst_label_op_def] >>
  Cases_on `s = a` >> gvs[]
QED

Theorem update_phi_bypass_label_absent:
  a <> l /\ ~MEM (Label l) i.inst_operands ==>
  ~MEM (Label l) (update_phi_bypass a b i).inst_operands
Proof
  rpt strip_tac >>
  Cases_on `i.inst_opcode = PHI` >> gvs[update_phi_bypass_def] >>
  Cases_on `MEM (Label a) i.inst_operands` >> gvs[]
  >- metis_tac[simplifyCfgShapeTheory.remove_phi_label_member] >>
  gvs[MEM_MAP] >>
  Cases_on `op` >> gvs[] >>
  Cases_on `s = b` >> gvs[]
QED

Theorem update_succ_phi_labels_label_absent:
  !succs bbs. new <> l /\
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) bbs ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (update_succ_phi_labels old new bbs succs)
Proof
  Induct_on `succs` >>
  gvs[update_succ_phi_labels_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  Cases_on `lookup_block h bbs` >> simp[] >>
  rename1 `lookup_block h bbs = SOME bb` >>
  drule lookup_block_member_label >> strip_tac >>
  irule replace_block_every >> simp[] >>
  `bb.bb_label <> l /\
   EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions`
    by (gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[EVERY_MEM] >>
  `~MEM (Label l) inst.inst_operands` by metis_tac[] >>
  metis_tac[subst_label_inst_label_absent]
QED

Theorem chain_merge_label_absent:
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) f.fn_blocks /\
  lookup_block lbl f.fn_blocks = SOME a /\
  lookup_block next f.fn_blocks = SOME b ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))
Proof
  strip_tac >>
  `MEM a f.fn_blocks /\ a.bb_label = lbl /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `a.bb_label <> l /\ b.bb_label <> l /\
   EVERY (\i. ~MEM (Label l) i.inst_operands) a.bb_instructions /\
   EVERY (\i. ~MEM (Label l) i.inst_operands) b.bb_instructions`
    by (gvs[EVERY_MEM] >> metis_tac[]) >>
  irule update_succ_phi_labels_label_absent >> conj_tac
  >- metis_tac[] >>
  irule replace_block_every >> reverse conj_tac
  >- (irule remove_block_every >> simp[]) >>
  BETA_TAC >> conj_tac
  >- (simp[merge_blocks_def] >> metis_tac[]) >>
  irule merge_blocks_every >> simp[]
QED

Theorem do_merge_jump_label_absent:
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) f.fn_blocks /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) g.fn_blocks
Proof
  strip_tac >>
  qpat_x_assum `do_merge_jump _ _ _ _ = _` mp_tac >>
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `MEM a f.fn_blocks /\ MEM target f.fn_blocks /\ target.bb_label = target_lbl`
    by metis_tac[lookup_block_member_label] >>
  `a.bb_label <> l /\ target_lbl <> l /\
   EVERY (\i. ~MEM (Label l) i.inst_operands) a.bb_instructions /\
   EVERY (\i. ~MEM (Label l) i.inst_operands) target.bb_instructions`
    by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. ~MEM (Label l) i.inst_operands)
     (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
       else canon_jnz_inst (subst_label_inst b.bb_label target_lbl inst))
       a.bb_instructions)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     `~MEM (Label l) inst.inst_operands` by
       (gvs[EVERY_MEM] >> metis_tac[]) >>
     Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
     drule canon_jnz_inst_label_subset >>
     metis_tac[subst_label_inst_label_absent]) >>
  irule replace_block_every >> reverse conj_tac
  >- (irule replace_block_every >> reverse conj_tac
      >- (irule remove_block_every >> simp[]) >>
      simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[] >>
      `~MEM (Label l) y.inst_operands` by
        (gvs[EVERY_MEM] >> metis_tac[]) >>
      metis_tac[update_phi_bypass_label_absent]) >>
  simp[] >> Cases_on `target_lbl = a.bb_label` >>
  gvs[EVERY_MEM, MEM_MAP] >> metis_tac[update_phi_bypass_label_absent]
QED

Theorem collapse_dfs_label_absent:
  !f lm vis lbl.
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) f.fn_blocks ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
      (FST (collapse_dfs f lm vis lbl)).fn_blocks
Proof
  ho_match_mp_tac collapse_dfs_preserves_predicate >> BETA_TAC >>
  conj_tac
  >- metis_tac[do_merge_jump_label_absent] >>
  simp[] >> metis_tac[chain_merge_label_absent]
QED

Theorem remove_unreachable_blocks_label_absent:
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) f.fn_blocks ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (remove_unreachable_blocks f).fn_blocks
Proof
  Cases_on `fn_entry_label f` >>
  simp[remove_unreachable_blocks_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem fix_all_phis_label_absent:
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) f.fn_blocks ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (fix_all_phis f).fn_blocks
Proof
  simp[fix_all_phis_def, fix_phis_in_block_def,
    EVERY_MEM, MEM_MAP, MEM_FILTER] >> rpt strip_tac >>
  gvs[MEM_FILTER, MEM_MAP] >> metis_tac[fix_phi_inst_label_subset]
QED

Theorem subst_label_map_op_label_absent:
  EVERY (\p. SND p <> l) lm /\ op <> Label l ==>
  subst_label_map_op lm op <> Label l
Proof
  Cases_on `op` >> simp[subst_label_map_op_def] >> strip_tac >>
  Cases_on `ALOOKUP lm s` >> simp[] >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  qpat_x_assum `EVERY _ lm` mp_tac >> simp[EVERY_MEM] >>
  disch_then (qspec_then `(s,x)` mp_tac) >> simp[]
QED

Theorem subst_block_labels_fn_label_absent:
  EVERY (\p. SND p <> l) lm /\
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) f.fn_blocks ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (subst_block_labels_fn lm f).fn_blocks
Proof
  simp[subst_block_labels_fn_def, subst_block_labels_block_def,
    EVERY_MEM, MEM_MAP] >> rpt strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM inst bb.bb_instructions` >>
  `~MEM (Label l) inst.inst_operands` by metis_tac[] >>
  Cases_on `is_block_label_opcode inst.inst_opcode` >>
  fs[subst_block_labels_inst_def, subst_label_map_inst_def, MEM_MAP] >>
  `EVERY (\p. SND p <> l) lm` by simp[EVERY_MEM] >>
  `y <> Label l` by metis_tac[] >>
  drule_all subst_label_map_op_label_absent >> simp[]
QED

Theorem simplify_cfg_round_label_absent:
  ALL_DISTINCT (fn_labels f) /\
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) f.fn_blocks ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (FST (simplify_cfg_round_with_labels f)).fn_blocks
Proof
  strip_tac >>
  `EVERY (\p. SND p <> l) (SND (simplify_cfg_round_with_labels f))` by
    (drule simplify_cfg_round_with_labels_transition >>
     simp[label_map_transition_def, EVERY_MEM, fn_labels_def, MEM_MAP] >>
     strip_tac >> gen_tac >> strip_tac >>
     first_x_assum drule >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
      (fix_all_phis (remove_unreachable_blocks f)).fn_blocks` by
    (irule fix_all_phis_label_absent >>
     irule remove_unreachable_blocks_label_absent >> simp[]) >>
  Cases_on `fn_entry_label f`
  >- simp[simplify_cfg_round_with_labels_def] >>
  rename1 `fn_entry_label f = SOME entry` >>
  qspecl_then [`fix_all_phis (remove_unreachable_blocks f)`, `[]`, `[]`, `entry`]
    mp_tac collapse_dfs_label_absent >>
  impl_tac >- simp[] >>
  Cases_on `collapse_dfs (fix_all_phis (remove_unreachable_blocks f)) [] [] entry` >>
  PairCases_on `r` >> simp[] >> strip_tac >>
  `EVERY (\p. SND p <> l) r0` by
    (qpat_x_assum `EVERY _ (SND _)` mp_tac >>
     simp[simplify_cfg_round_with_labels_def, EVERY_MEM, MEM_REVERSE]) >>
  simp[simplify_cfg_round_with_labels_def] >>
  irule fix_all_phis_label_absent >>
  irule remove_unreachable_blocks_label_absent >>
  Cases_on `r0 = []` >> simp[] >>
  irule subst_block_labels_fn_label_absent >> simp[EVERY_MEM]
QED

Theorem simplify_cfg_iter_label_absent:
  !n f. ALL_DISTINCT (fn_labels f) /\
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions) f.fn_blocks ==>
  EVERY (\bb. bb.bb_label <> l /\
    EVERY (\i. ~MEM (Label l) i.inst_operands) bb.bb_instructions)
    (FST (simplify_cfg_iter_with_labels n f)).fn_blocks
Proof
  Induct_on `n` >> simp[simplify_cfg_iter_with_labels_def] >>
  rpt strip_tac >>
  drule_all simplify_cfg_round_label_absent >>
  drule simplify_cfg_round_with_labels_transition >>
  Cases_on `simplify_cfg_round_with_labels f` >> simp[] >>
  simp[label_map_transition_def] >> rpt strip_tac >>
  Cases_on `q.fn_blocks = f.fn_blocks` >> simp[] >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> simp[] >>
  first_x_assum drule >> simp[]
QED

Theorem simplify_cfg_runtime_reflect:
  o1_fn_shape C f ==>
  ((?i. MEM i (fn_insts (FST (simplify_cfg_fn_with_labels f))) /\
        MEM (Label "runtime_begin") i.inst_operands) ==>
   (?i. MEM i (fn_insts f) /\
        MEM (Label "runtime_begin") i.inst_operands))
Proof
  strip_tac >>
  CCONTR_TAC >> fs[] >>
  `ALL_DISTINCT (fn_labels f)` by
    gvs[o1_fn_shape_def, venomWfTheory.wf_function_def] >>
  `EVERY (\bb. bb.bb_label <> "runtime_begin" /\
    EVERY (\i. ~MEM (Label "runtime_begin") i.inst_operands) bb.bb_instructions)
      f.fn_blocks` by
    (fs[o1_fn_shape_def, fn_shape_ok_def, reserved_label_def,
        EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  drule_all simplify_cfg_iter_label_absent >>
  disch_then (qspec_then `LENGTH f.fn_blocks` assume_tac) >>
  fs[simplify_cfg_fn_with_labels_def, EVERY_MEM, fn_insts_def,
     MEM_fn_insts_blocks_iff] >> metis_tac[]
QED
