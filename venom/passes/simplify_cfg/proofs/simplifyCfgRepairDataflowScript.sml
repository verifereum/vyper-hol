Theory simplifyCfgRepairDataflow
Ancestors
  simplifyCfgPhiRepair simplifyCfgDataflow simplifyCfgStruct simplifyCfgDefs
  venomWf venomInst venomExecProofs cfgTransform cfgWf list rich_list

Theorem fix_all_phis_block_member:
  MEM bb fn.fn_blocks ==>
  MEM (fix_phis_in_block (pred_labels fn bb.bb_label) bb) (fix_all_phis fn).fn_blocks
Proof
  simp[fix_all_phis_def, MEM_MAP] >> metis_tac[]
QED

Theorem fix_all_phis_def_available_endpoint:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  def_available_at fn bb NONE v ==>
  def_available_at (fix_all_phis fn)
    (fix_phis_in_block (pred_labels fn bb.bb_label) bb) NONE v
Proof
  strip_tac >> fs[def_available_at_def] >>
  qexistsl [`fix_phis_in_block (pred_labels fn def_bb.bb_label) def_bb`,
    `fix_phi_inst (pred_labels fn def_bb.bb_label) def_inst`] >>
  simp[fix_all_phis_dominates, simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block] >>
  conj_tac >- simp[fix_all_phis_block_member] >>
  conj_tac >- (simp[fix_phis_in_block_member] >> metis_tac[]) >>
  drule_all fix_phi_inst_reachable_outputs >> simp[]
QED

Theorem fix_phis_in_block_eq_member:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  fix_phis_in_block (pred_labels fn a.bb_label) a =
  fix_phis_in_block (pred_labels fn b.bb_label) b ==>
  a = b
Proof
  strip_tac >> irule same_label_same_block >> conj_tac
  >- (qpat_x_assum `fix_phis_in_block _ _ = _`
        (mp_tac o Q.AP_TERM `\bb. bb.bb_label`) >>
      simp[simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block]) >>
  qexists `fn` >> simp[]
QED

Theorem fix_all_phis_def_available_point:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  MEM bb fn.fn_blocks /\ MEM use_inst bb.bb_instructions /\ use_inst.inst_opcode <> PHI /\
  def_available_at fn bb (SOME use_inst) v ==>
  def_available_at (fix_all_phis fn)
    (fix_phis_in_block (pred_labels fn bb.bb_label) bb) (SOME use_inst) v
Proof
  strip_tac >> fs[def_available_at_def] >>
  qexistsl [`fix_phis_in_block (pred_labels fn def_bb.bb_label) def_bb`,
    `fix_phi_inst (pred_labels fn def_bb.bb_label) def_inst`] >>
  simp[fix_all_phis_dominates, simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block] >>
  conj_tac >- simp[fix_all_phis_block_member] >>
  conj_tac >- (simp[fix_phis_in_block_member] >> metis_tac[]) >>
  conj_tac >- (drule_all fix_phi_inst_reachable_outputs >> simp[]) >>
  strip_tac >>
  `def_bb = bb` by (irule fix_phis_in_block_eq_member >> metis_tac[]) >>
  gvs[] >> drule_all fix_phis_in_block_strict_order >> simp[]
QED

Theorem fix_all_phis_def_on_all_paths_endpoint:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  MEM bb fn.fn_blocks /\ def_on_all_paths fn bb NONE v ==>
  def_on_all_paths (fix_all_phis fn)
    (fix_phis_in_block (pred_labels fn bb.bb_label) bb) NONE v
Proof
  strip_tac >> simp[def_on_all_paths_def, fix_all_phis_path_iff,
    fix_all_phis_entry, simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block] >>
  rpt strip_tac >>
  qpat_x_assum `def_on_all_paths fn bb NONE v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> qexistsl [`k`,
        `fix_phis_in_block (pred_labels fn def_bb.bb_label) def_bb`,
        `fix_phi_inst (pred_labels fn def_bb.bb_label) def_inst`] >>
      simp[fix_all_phis_block_member,
        simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block] >>
      conj_tac >- (simp[fix_phis_in_block_member] >> metis_tac[]) >>
      drule_all fix_phi_inst_reachable_outputs >> simp[]) >>
  disj2_tac >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  `MEM (fix_phi_inst (pred_labels fn bb.bb_label) (EL i bb.bb_instructions))
     (fix_phis_in_block (pred_labels fn bb.bb_label) bb).bb_instructions` by
    (simp[fix_phis_in_block_member] >> metis_tac[]) >>
  pop_assum mp_tac >> simp[MEM_EL] >> strip_tac >> qexists `n` >>
  simp[] >> drule_all fix_phi_inst_reachable_outputs >> simp[] >>
  metis_tac[MEM_EL]
QED

Theorem fix_all_phis_def_on_all_paths_point:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  MEM bb fn.fn_blocks /\ MEM use_inst bb.bb_instructions /\ use_inst.inst_opcode <> PHI /\
  def_on_all_paths fn bb (SOME use_inst) v ==>
  def_on_all_paths (fix_all_phis fn)
    (fix_phis_in_block (pred_labels fn bb.bb_label) bb) (SOME use_inst) v
Proof
  strip_tac >> simp[def_on_all_paths_def, fix_all_phis_path_iff,
    fix_all_phis_entry, simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block] >>
  rpt strip_tac >>
  qpat_x_assum `def_on_all_paths fn bb (SOME use_inst) v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> qexistsl [`k`,
        `fix_phis_in_block (pred_labels fn def_bb.bb_label) def_bb`,
        `fix_phi_inst (pred_labels fn def_bb.bb_label) def_inst`] >>
      simp[fix_all_phis_block_member,
        simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block] >>
      conj_tac >- (simp[fix_phis_in_block_member] >> metis_tac[]) >>
      drule_all fix_phi_inst_reachable_outputs >> simp[]) >>
  disj2_tac >>
  `(EL j bb.bb_instructions).inst_opcode <> PHI` by simp[] >>
  drule_all fix_phis_in_block_strict_order >>
  disch_then (qspec_then `pred_labels fn bb.bb_label` mp_tac) >>
  simp[] >> strip_tac >> qexists `i'` >> simp[] >> conj_tac
  >- (`MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
      drule_all fix_phi_inst_reachable_outputs >> simp[]) >>
  qexists `j'` >> simp[]
QED
