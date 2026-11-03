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

Theorem filter_phi_ops_all_preds:
  !ops. phi_well_formed ops /\
  (!p v. MEM (p,v) (phi_pairs ops) ==> MEM p actual_preds) ==>
  filter_phi_ops actual_preds ops = ops
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, phi_pairs_def, filter_phi_ops_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fix_phi_inst_edge_wf_survivor:
  phi_edge_uses_wf fn bb inst /\
  (fix_phi_inst (pred_labels fn bb.bb_label) inst).inst_opcode = PHI ==>
  fix_phi_inst (pred_labels fn bb.bb_label) inst = inst
Proof
  strip_tac >> drule fix_phi_inst_surviving_phi >> strip_tac >>
  `filter_phi_ops (pred_labels fn bb.bb_label) inst.inst_operands = inst.inst_operands` by
    (irule filter_phi_ops_all_preds >> fs[phi_edge_uses_wf_def, pred_labels_edge] >>
     metis_tac[pairTheory.FST]) >> simp[]
QED

Theorem fix_all_phis_phi_edge_uses:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  phi_edge_uses_wf fn bb inst /\
  (fix_phi_inst (pred_labels fn bb.bb_label) inst).inst_opcode = PHI ==>
  phi_edge_uses_wf (fix_all_phis fn)
    (fix_phis_in_block (pred_labels fn bb.bb_label) bb)
    (fix_phi_inst (pred_labels fn bb.bb_label) inst)
Proof
  strip_tac >> drule_all fix_phi_inst_edge_wf_survivor >> strip_tac >>
  `!b. MEM b fn.fn_blocks ==> bb_well_formed b` by fs[wf_function_def] >>
  simp[phi_edge_uses_wf_def, simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block,
       fix_all_phis_edge] >>
  conj_tac >- fs[phi_edge_uses_wf_def] >>
  conj_tac >- fs[phi_edge_uses_wf_def] >>
  conj_tac >- fs[phi_edge_uses_wf_def] >>
  rpt strip_tac >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
        fn_cfg_edge fn pred bb.bb_label /\ def_available_at fn pb NONE v` by
    (fs[phi_edge_uses_wf_def] >> metis_tac[]) >>
  qexists `fix_phis_in_block (pred_labels fn pb.bb_label) pb` >>
  simp[fix_all_phis_block_member, simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block] >>
  gvs[] >> irule fix_all_phis_def_available_endpoint >> simp[]
QED

Theorem fix_all_phis_phi_paths_use:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  fn_defs_reach_uses fn /\ MEM bb fn.fn_blocks /\
  MEM repaired (fix_phis_in_block (pred_labels fn bb.bb_label) bb).bb_instructions /\
  repaired.inst_opcode = PHI /\ MEM (p,v) (phi_pairs repaired.inst_operands) /\
  MEM pb (fix_all_phis fn).fn_blocks /\ pb.bb_label = p ==>
  def_on_all_paths (fix_all_phis fn) pb NONE v
Proof
  strip_tac >> drule_all fix_phis_in_block_phi_pair >> strip_tac >>
  `?orig_pb. MEM orig_pb fn.fn_blocks /\
     pb = fix_phis_in_block (pred_labels fn orig_pb.bb_label) orig_pb` by
    (fs[fix_all_phis_def, MEM_MAP] >> metis_tac[]) >>
  `orig_pb.bb_label = p` by fs[simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block] >>
  `def_on_all_paths fn orig_pb NONE v` by
    (fs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  gvs[] >> irule fix_all_phis_def_on_all_paths_endpoint >> simp[]
QED

Theorem unique_predecessor_path_split:
  (!q. fn_cfg_edge fn q b ==> q = p) ==>
  !path. is_fn_path fn path /\ 2 <= LENGTH path /\ LAST path = b ==>
  ?pre. path = pre ++ [b] /\ pre <> [] /\ is_fn_path fn pre /\
        HD pre = HD path /\ LAST pre = p
Proof
  strip_tac >> Induct >> simp[] >> qx_gen_tac `x` >>
  Cases_on `path` >> simp[is_fn_path_def] >> rpt strip_tac >>
  rename1 `fn_cfg_edge fn x y` >>
  Cases_on `t = []`
  >- gvs[is_fn_path_def] >>
  `2 <= LENGTH (y::t)` by (Cases_on `t` >> gvs[]) >>
  qpat_x_assum `_ ==> ?pre. _` mp_tac >> simp[] >>
  disch_then (qx_choose_then `pre` strip_assume_tac) >>
  qexists `x::pre` >> simp[is_fn_path_prepend] >>
  Cases_on `pre` >> gvs[]
QED

Theorem unique_predecessor_paths_before_point:
  fn_entry_label fn = SOME entry /\ bb.bb_label <> entry /\
  (!q. fn_cfg_edge fn q bb.bb_label ==> q = pb.bb_label) /\
  MEM pb fn.fn_blocks /\ def_on_all_paths fn pb NONE v ==>
  def_on_all_paths fn bb (SOME use_inst) v
Proof
  strip_tac >> simp[def_on_all_paths_def] >> rpt strip_tac >>
  `2 <= LENGTH path` by
    (Cases_on `path` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  drule unique_predecessor_path_split >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `pre` strip_assume_tac) >>
  qpat_x_assum `def_on_all_paths fn pb NONE v` mp_tac >>
  simp[def_on_all_paths_def] >> disch_then (qspec_then `pre` mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> qexistsl [`k`, `def_bb`, `def_inst`] >>
      simp[] >> gvs[EL_APPEND1]) >>
  `LENGTH pre - 1 < LENGTH pre` by (Cases_on `pre` >> gvs[]) >>
  disj1_tac >> qexistsl [`LENGTH pre - 1`, `pb`, `EL i pb.bb_instructions`] >>
  simp[] >> conj_tac
  >- gvs[EL_APPEND1, LAST_EL, arithmeticTheory.PRE_SUB1] >>
  simp[MEM_EL] >> qexists `i` >> simp[]
QED

Theorem scfg_phi_safe_nonentry:
  wf_function fn /\ scfg_phi_safe fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  fn_entry_label fn = SOME entry ==> bb.bb_label <> entry
Proof
  strip_tac >> drule scfg_phi_safe_entry >> strip_tac >>
  Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def, EVERY_MEM] >>
  strip_tac >>
  `bb = h` by
    (irule same_label_same_block >> simp[] >> qexists `fn` >> simp[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem fix_all_phis_converted_paths_use:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  fn_defs_reach_uses fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  inst.inst_opcode = PHI /\
  filter_phi_ops (pred_labels fn bb.bb_label) inst.inst_operands = [Label p; Var v] ==>
  def_on_all_paths (fix_all_phis fn)
    (fix_phis_in_block (pred_labels fn bb.bb_label) bb)
    (SOME (fix_phi_inst (pred_labels fn bb.bb_label) inst)) v
Proof
  strip_tac >> drule_all single_pair_phi_predecessors >> strip_tac >>
  `fn_cfg_edge fn p bb.bb_label` by metis_tac[] >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = p` by
    (fs[fn_cfg_edge_def] >> metis_tac[]) >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  drule_all filter_phi_ops_single_pair_source >> strip_tac >>
  `def_on_all_paths fn pb NONE v` by
    (fs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  `?entry. fn_entry_label fn = SOME entry` by
    (Cases_on `fn.fn_blocks` >>
     gvs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
  `bb.bb_label <> entry` by (irule scfg_phi_safe_nonentry >> metis_tac[]) >>
  irule unique_predecessor_paths_before_point >>
  conj_tac
  >- (qexists `entry` >>
      simp[fix_all_phis_entry, simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block]) >>
  qexists `fix_phis_in_block (pred_labels fn pb.bb_label) pb` >>
  simp[fix_all_phis_entry, simplifyCfgLabelPropsTheory.bb_label_fix_phis_in_block,
       fix_all_phis_block_member] >>
  conj_tac
  >- (`!b. MEM b fn.fn_blocks ==> bb_well_formed b` by fs[wf_function_def] >>
      simp[fix_all_phis_edge] >> metis_tac[]) >>
  gvs[] >> irule fix_all_phis_def_on_all_paths_endpoint >> simp[]
QED

Theorem fix_all_phis_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  fn_defs_reach_uses fn ==> fn_defs_reach_uses (fix_all_phis fn)
Proof
  strip_tac >> simp[fn_defs_reach_uses_def] >> rpt gen_tac >> strip_tac >>
  `?orig_bb. MEM orig_bb fn.fn_blocks /\
    bb = fix_phis_in_block (pred_labels fn orig_bb.bb_label) orig_bb` by
    (fs[fix_all_phis_def, MEM_MAP] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (rpt strip_tac >> irule fix_all_phis_phi_paths_use >> metis_tac[]) >>
  rpt strip_tac >>
  `?orig_inst. MEM orig_inst orig_bb.bb_instructions /\
    inst = fix_phi_inst (pred_labels fn orig_bb.bb_label) orig_inst /\
    ((orig_inst.inst_opcode <> PHI /\ MEM (Var v) orig_inst.inst_operands) \/
     (orig_inst.inst_opcode = PHI /\ ?p.
      filter_phi_ops (pred_labels fn orig_bb.bb_label) orig_inst.inst_operands =
      [Label p; Var v]))` by
    (irule fix_phis_in_block_ordinary_use >> metis_tac[]) >>
  gvs[]
  >- (`def_on_all_paths fn orig_bb (SOME orig_inst) v` by
        (fs[fn_defs_reach_uses_def] >> metis_tac[]) >>
      gvs[fix_phi_inst_non_phi] >>
      irule fix_all_phis_def_on_all_paths_point >> simp[]) >>
  irule fix_all_phis_converted_paths_use >> metis_tac[]
QED
