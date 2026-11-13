Theory simplifyCfgPhiConsumer
Ancestors
  simplifyCfgPhiBlockSemantics simplifyCfgAvailability
  simplifyCfgPhiSemantics simplifyCfgDefs venomExecSemantics venomWf venomInst
  venomExecProofs venomWfProps cfgTransform analysisSimProofsBase list

Theorem scfg_resolve_phi_var:
  !ops p op. phi_well_formed ops /\ resolve_phi p ops = SOME op ==>
    ?v. op = Var v
Proof
  Induct_on `ops` using phi_well_formed_ind >>
  rw[phi_well_formed_def, resolve_phi_def] >> gvs[] >> metis_tac[]
QED

Theorem scfg_phi_edge_evaluable:
  wf_function fn /\ fn_defs_reach_uses fn /\ fn_inst_wf fn /\
  scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s /\
  MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  MEM pb fn.fn_blocks /\ fn_cfg_edge fn pb.bb_label bb.bb_label /\
  s.vs_prev_bb = SOME pb.bb_label /\
  (?op. resolve_phi pb.bb_label i.inst_operands = SOME op) ==>
  ?kv. eval_one_phi s i = SOME kv
Proof
  strip_tac >>
  `inst_wf i` by metis_tac[fn_inst_wf_def, EVERY_MEM] >>
  `phi_well_formed i.inst_operands /\ LENGTH i.inst_outputs = 1` by
    gvs[inst_wf_def] >>
  `?v. op = Var v` by metis_tac[scfg_resolve_phi_var] >> gvs[] >>
  `MEM (pb.bb_label,v) (phi_pairs i.inst_operands)` by
    metis_tac[resolve_phi_pair] >>
  `IS_SOME (lookup_var v s)` by (irule scfg_phi_edge_defined >> metis_tac[]) >>
  Cases_on `i.inst_outputs` >> gvs[LENGTH_EQ_NUM_compute] >>
  simp[eval_one_phi_def, venomStateTheory.eval_operand_def] >>
  Cases_on `lookup_var v s` >> gvs[]
QED

Theorem scfg_phi_snapshot_outputs:
  !ps. EVERY (\i. eval_one_phi s i = SOME (snap i)) ps ==>
    MAP (FST o snap) ps = FLAT (MAP (\i. i.inst_outputs) ps)
Proof
  Induct >- simp[] >> gen_tac >> simp[EVERY_DEF] >> strip_tac >>
  `h.inst_outputs = [FST (snap h)]` by
    (Cases_on `snap h` >> metis_tac[eval_one_phi_imp_inst_outputs, pairTheory.FST]) >> simp[]
QED

Theorem scfg_phi_edge_snapshot:
  wf_function fn /\ fn_defs_reach_uses fn /\ fn_inst_wf fn /\
  scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s /\
  MEM bb fn.fn_blocks /\ MEM pb fn.fn_blocks /\
  fn_cfg_edge fn pb.bb_label bb.bb_label /\ s.vs_prev_bb = SOME pb.bb_label /\
  EVERY (\i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
    ?op. resolve_phi pb.bb_label i.inst_operands = SOME op) ps ==>
  ?snap. EVERY (\i. eval_one_phi s i = SOME (snap i)) ps
Proof
  strip_tac >> simp[EVERY_MEM] >>
  simp[GSYM SKOLEM_THM] >> qx_gen_tac `i` >>
  Cases_on `MEM i ps` >> simp[] >>
  irule scfg_phi_edge_evaluable >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem scfg_fn_phi_snapshot_conditions:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  MEM p (pred_labels fn bb.bb_label) /\ s.vs_prev_bb = SOME p /\
  EVERY (\i. eval_one_phi s i = SOME (snap i)) ps /\
  (!pb. MEM pb fn.fn_blocks /\ MEM bb.bb_label (bb_succs pb) ==>
    fn_reachable fn pb.bb_label) ==>
  ALL_DISTINCT (MAP (FST o snap) ps) /\
  EVERY (\i. i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
    eval_one_phi s i = SOME (snap i) /\
    EVERY (\q. ?op. resolve_phi q i.inst_operands = SOME op)
      (pred_labels fn bb.bb_label)) ps /\
  (!i v. MEM i ps /\
    (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = ASSIGN /\
    resolve_phi p i.inst_operands = SOME (Var v) ==>
    ~MEM v (MAP (FST o snap) ps))
Proof
  strip_tac >>
  `EVERY (\i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI) ps` by
    (mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi) >>
     simp[EVERY_MEM] >> rpt strip_tac >> gvs[] >>
     metis_tac[TAKE_DROP, MEM_APPEND]) >>
  `MAP (FST o snap) ps = FLAT (MAP (\i. i.inst_outputs) ps)` by
    metis_tac[scfg_phi_snapshot_outputs] >>
  conj_tac >- metis_tac[scfg_phi_prefix_outputs_distinct] >>
  conj_tac
  >- (simp[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >> fs[EVERY_MEM] >>
      `MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\ inst_wf i` by
        metis_tac[fn_inst_wf_def, EVERY_MEM] >>
      simp[] >> conj_tac >- gvs[inst_wf_def] >>
      drule_all scfg_reachable_pred_coverage >> simp[EVERY_MEM]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MAP (FST o snap) ps = _` (fn th => rewrite_tac[th]) >>
  strip_tac >> fs[MEM_FLAT, MEM_MAP] >>
  qpat_x_assum `l = _` SUBST_ALL_TAC >>
  rename1 `MEM v j.inst_outputs` >>
  `MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
   MEM j bb.bb_instructions /\ j.inst_opcode = PHI` by fs[EVERY_MEM] >>
  `EVERY (\q. ?op. resolve_phi q i.inst_operands = SOME op)
    (pred_labels fn bb.bb_label)` by
    (irule scfg_reachable_pred_coverage >> metis_tac[]) >>
  drule_all scfg_covered_conversion_source_separate >> simp[]
QED

Theorem scfg_fn_fix_phis_block:
  wf_function fn /\ fn_inst_wf fn /\ simplify_cfg_fn_ok fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  ps = TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  bb.bb_instructions = ps ++ tail /\ EVERY (\i. i.inst_opcode <> PHI) tail /\
  rs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode = PHI) ps /\
  cs = FILTER (\i. (fix_phi_inst (pred_labels fn bb.bb_label) i).inst_opcode <> PHI) ps /\
  MEM pb fn.fn_blocks /\ fn_cfg_edge fn pb.bb_label bb.bb_label /\
  s.vs_prev_bb = SOME pb.bb_label /\
  scfg_path_defined fn path pb (LENGTH pb.bb_instructions) s /\
  (!qb. MEM qb fn.fn_blocks /\ MEM bb.bb_label (bb_succs qb) ==>
    fn_reachable fn qb.bb_label) ==>
  ?snap.
    EVERY (\i. eval_one_phi s i = SOME (snap i)) ps /\
    eval_phis s ps = OK (FOLDL (\t (x,w). update_var x w t) s (MAP snap ps)) /\
    eval_phis s (MAP (fix_phi_inst (pred_labels fn bb.bb_label)) rs) =
      OK (FOLDL (\t (x,w). update_var x w t) s (MAP snap rs)) /\
    scfg_iprefix C (fix_phis_in_block (pred_labels fn bb.bb_label) bb)
      ((FOLDL (\t (x,w). update_var x w t) s (MAP snap rs))
        with vs_inst_idx := LENGTH rs)
      ((FOLDL (\t (x,w). update_var x w t) s (MAP snap ps))
        with vs_inst_idx := LENGTH rs + LENGTH cs)
Proof
  strip_tac >>
  `MEM pb.bb_label (pred_labels fn bb.bb_label)` by
    (fs[fn_cfg_edge_def, pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER] >>
     metis_tac[]) >>
  `EVERY (\i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI) ps` by
    (mp_tac (Q.SPEC `bb.bb_instructions` phi_prefix_all_phi) >>
     fs[EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
  `EVERY (\i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
     ?op. resolve_phi pb.bb_label i.inst_operands = SOME op) ps` by
    (qpat_x_assum `bb.bb_instructions = ps ++ tail` kall_tac >>
     simp[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
     `MEM i bb.bb_instructions /\ i.inst_opcode = PHI` by fs[EVERY_MEM] >>
     drule_all scfg_reachable_pred_coverage >> simp[EVERY_MEM] >> metis_tac[]) >>
  `fn_defs_reach_uses fn` by fs[simplify_cfg_fn_ok_def] >>
  drule_all scfg_phi_edge_snapshot >> strip_tac >>
  drule_all scfg_fn_phi_snapshot_conditions >> strip_tac >>
  qexists_tac `snap` >> conj_tac >- simp[] >>
  irule scfg_fix_phis_block_snapshot >> metis_tac[]
QED
