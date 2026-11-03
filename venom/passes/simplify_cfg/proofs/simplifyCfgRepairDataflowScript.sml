Theory simplifyCfgRepairDataflow
Ancestors
  simplifyCfgPhiRepair simplifyCfgDataflow simplifyCfgStruct simplifyCfgDefs
  venomWf venomInst venomExecSemantics venomExecProofs cfgTransform cfgWf list rich_list

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

Theorem resolve_phi_filter_phi_ops:
  !ops. phi_well_formed ops /\ MEM p actual_preds ==>
  resolve_phi p (filter_phi_ops actual_preds ops) = resolve_phi p ops
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, filter_phi_ops_def, resolve_phi_def] >>
  rpt strip_tac >> Cases_on `MEM lbl actual_preds` >>
  simp[resolve_phi_def] >> Cases_on `lbl = p` >> gvs[]
QED

Theorem single_pair_phi_predecessors:
  fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  filter_phi_ops (pred_labels fn bb.bb_label) inst.inst_operands = [Label p; Var v] ==>
  !q. fn_cfg_edge fn q bb.bb_label <=> q = p
Proof
  strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  `fn_reachable fn bb.bb_label` by fs[all_reachable_def] >>
  gen_tac >> eq_tac
  >- (strip_tac >>
      `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = q /\ MEM bb.bb_label (bb_succs pb)` by
        (fs[fn_cfg_edge_def] >> metis_tac[]) >>
      `fn_reachable fn pb.bb_label` by fs[all_reachable_def] >>
      drule_all scfg_phi_safe_coverage >> strip_tac >>
      `MEM q (pred_labels fn bb.bb_label)` by metis_tac[pred_labels_edge] >>
      drule_all resolve_phi_filter_phi_ops >>
      simp[resolve_phi_def] >> Cases_on `p = q` >> gvs[]) >>
  strip_tac >> gvs[] >>
  drule_all filter_phi_ops_single_pair_source >>
  simp[pred_labels_edge]
QED

Theorem fix_phi_inst_surviving_phi:
  (fix_phi_inst actual_preds inst).inst_opcode = PHI ==>
  inst.inst_opcode = PHI /\
  fix_phi_inst actual_preds inst = inst with inst_operands := filter_phi_ops actual_preds inst.inst_operands
Proof
  Cases_on `inst.inst_opcode = PHI`
  >- (simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> simp[] >>
      Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
      Cases_on `h` >> simp[]) >>
  simp[fix_phi_inst_non_phi]
QED

Theorem fix_all_phis_entry_no_phi:
  fn.fn_blocks <> [] /\ scfg_phi_safe fn ==>
  EVERY (\inst. inst.inst_opcode <> PHI)
    (HD (fix_all_phis fn).fn_blocks).bb_instructions
Proof
  strip_tac >> drule scfg_phi_safe_entry >>
  Cases_on `fn.fn_blocks` >> gvs[fix_all_phis_def] >>
  simp[EVERY_MEM, fix_phis_in_block_member] >> rpt strip_tac >>
  gvs[] >> drule fix_phi_inst_surviving_phi >> strip_tac >> metis_tac[]
QED

Theorem fix_all_phis_phi_coverage:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  MEM rb (fix_all_phis fn).fn_blocks /\
  MEM ri rb.bb_instructions /\ ri.inst_opcode = PHI /\
  MEM pb (fix_all_phis fn).fn_blocks /\
  MEM rb.bb_label (bb_succs pb) ==>
  ?op. resolve_phi pb.bb_label ri.inst_operands = SOME op
Proof
  simp[fix_all_phis_def, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  gvs[simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block, fix_phis_in_block_member] >>
  drule fix_phi_inst_surviving_phi >> strip_tac >>
  `fn_reachable fn bb.bb_label` by fs[all_reachable_def] >>
  `bb_well_formed bb'` by (fs[wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM bb.bb_label (bb_succs bb')` by fs[fix_phis_in_block_succs] >>
  `fn_reachable fn bb'.bb_label` by fs[all_reachable_def] >>
  drule_all scfg_phi_safe_coverage >> strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  `MEM bb'.bb_label (pred_labels fn bb.bb_label)` by
    (simp[pred_labels_edge, fn_cfg_edge_def] >> metis_tac[]) >>
  drule_all resolve_phi_filter_phi_ops >> simp[]
QED

Theorem fix_all_phis_phi_output_unique:
  wf_function fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  MEM rb (fix_all_phis fn).fn_blocks /\ MEM ri rb.bb_instructions /\
  ri.inst_opcode = PHI /\ MEM v ri.inst_outputs /\
  MEM rb' (fix_all_phis fn).fn_blocks /\ MEM ri' rb'.bb_instructions /\
  MEM v ri'.inst_outputs ==> ri' = ri
Proof
  simp[fix_all_phis_def, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  gvs[fix_phis_in_block_member] >>
  drule fix_phi_inst_surviving_phi >> strip_tac >>
  `MEM v inst.inst_outputs` by gvs[] >>
  `MEM v inst'.inst_outputs` by metis_tac[fix_phi_inst_outputs, MEM] >>
  `inst' = inst` by
    (irule scfg_phi_safe_unique_output >>
     fs[all_reachable_def] >> metis_tac[]) >>
  `bb' = bb` by (irule wf_function_instruction_block >> metis_tac[]) >> simp[]
QED

Theorem fix_all_phis_phi_safe:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn ==>
  scfg_phi_safe (fix_all_phis fn)
Proof
  strip_tac >> simp[scfg_phi_safe_def] >> conj_tac
  >- (irule fix_all_phis_entry_no_phi >> fs[wf_function_def, fn_has_entry_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule fix_all_phis_phi_output_unique >> metis_tac[]) >>
  rpt strip_tac >> irule fix_all_phis_phi_coverage >> metis_tac[]
QED
