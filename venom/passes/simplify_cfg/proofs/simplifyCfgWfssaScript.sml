Theory simplifyCfgWfssa
Ancestors
  simplifyCfgPhiRepair simplifyCfgDataflow simplifyCfgStruct simplifyCfgDefs
  simplifyCfgRepairDataflow simplifyCfgChainDataflow simplifyCfgBypassDataflow
  cfgTransform simplifyCfgPhiPreds
  venomWf venomInst venomExecProofs cfgWf unitShapeDefs simplifyCfgLabelProps
  list rich_list relation

Theorem is_fn_path_first_arrival:
  !path. path <> [] /\ is_fn_path fn path /\ LAST path = b ==>
  ?pre. is_fn_path fn (pre ++ [b]) /\ HD (pre ++ [b]) = HD path /\
        ~MEM b pre
Proof
  Induct >> simp[] >> qx_gen_tac `a` >> strip_tac >>
  Cases_on `a = b`
  >- (qexists `[]` >> simp[is_fn_path_def]) >>
  Cases_on `path` >- gvs[] >>
  fs[is_fn_path_def] >>
  qexists `a::pre` >> simp[is_fn_path_prepend] >>
  Cases_on `pre` >> gvs[]
QED

Theorem def_on_all_paths_first_witness:
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  def_on_all_paths fn bb use_opt v ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\
    (db = bb ==> case use_opt of NONE => T | SOME use =>
      ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
            EL i bb.bb_instructions = di /\ EL j bb.bb_instructions = use)
Proof
  strip_tac >> fs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `?pre. is_fn_path fn (pre ++ [bb.bb_label]) /\
     HD (pre ++ [bb.bb_label]) = entry /\ ~MEM bb.bb_label pre` by
    metis_tac[is_fn_path_first_arrival] >>
  qpat_x_assum `def_on_all_paths fn bb use_opt v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  simp[] >> strip_tac
  >- (qexistsl [`def_bb`, `def_inst`] >> simp[] >>
      `MEM def_bb.bb_label pre` by
        (simp[MEM_EL] >> qexists `k` >> fs[EL_APPEND1]) >>
      `def_bb <> bb` by metis_tac[] >> simp[]) >>
  qexistsl [`bb`, `EL i bb.bb_instructions`] >> simp[EL_MEM] >>
  Cases_on `use_opt` >> gvs[] >> metis_tac[]
QED

Theorem def_on_all_paths_dominating_witness:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\ def_on_all_paths fn bb use_opt v /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs ==>
  fn_dominates fn db.bb_label bb.bb_label
Proof
  strip_tac >> simp[fn_dominates_def] >> rpt strip_tac >>
  qpat_x_assum `def_on_all_paths fn bb use_opt v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (`def_inst = di` by metis_tac[ssa_form_output_unique] >>
      `def_bb = db` by metis_tac[wf_function_instruction_block] >>
      gvs[] >> simp[MEM_EL] >> qexists `k` >> simp[]) >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  `EL i bb.bb_instructions = di` by metis_tac[ssa_form_output_unique] >>
  `bb = db` by metis_tac[wf_function_instruction_block] >>
  metis_tac[LAST_MEM]
QED

Theorem def_on_all_paths_available:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\ def_on_all_paths fn bb use_opt v ==>
  def_available_at fn bb use_opt v
Proof
  strip_tac >> drule_all def_on_all_paths_first_witness >> strip_tac >>
  simp[def_available_at_def] >> qexistsl [`db`, `di`] >> simp[] >>
  irule def_on_all_paths_dominating_witness >> metis_tac[]
QED

Theorem reachable_defs_reach_uses_wf_ssa:
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  fn_defs_reach_uses fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     phi_well_formed inst.inst_operands /\
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     (!pred. fn_cfg_edge fn pred bb.bb_label <=>
       ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred)) ==>
  wf_ssa fn
Proof
  strip_tac >> simp[wf_ssa_def, def_dominates_uses_def] >>
  qx_gen_tac `bb` >> qx_gen_tac `inst` >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (`phi_well_formed inst.inst_operands /\
       ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
       (!pred. fn_cfg_edge fn pred bb.bb_label <=>
         ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred)` by
        metis_tac[] >>
      simp[phi_edge_uses_wf_def] >> rpt strip_tac >>
      `fn_cfg_edge fn pred bb.bb_label` by metis_tac[pairTheory.FST] >>
      `?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred` by
        (fs[fn_cfg_edge_def] >> metis_tac[]) >>
      qexists `pred_bb` >> simp[] >>
      conj_tac >- metis_tac[pairTheory.FST] >>
      irule def_on_all_paths_available >>
      fs[all_reachable_def, fn_defs_reach_uses_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> irule def_on_all_paths_available >>
  fs[all_reachable_def, fn_defs_reach_uses_def] >> metis_tac[]
QED

Theorem inst_wf_fix_phi_inst:
  inst_wf inst ==> inst_wf (fix_phi_inst actual_preds inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (`phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)` by
        (irule filter_phi_ops_well_formed >> fs[inst_wf_def]) >>
      fs[inst_wf_def] >> simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> simp[inst_wf_def] >>
      Cases_on `t` >> gvs[phi_well_formed_def] >>
      Cases_on `t'` >> gvs[inst_wf_def]) >>
  simp[fix_phi_inst_non_phi]
QED

Theorem label_positions_ok_fix_phi_inst:
  inst_wf inst /\ label_positions_ok inst ==>
  label_positions_ok (fix_phi_inst actual_preds inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (`phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)` by
        (irule filter_phi_ops_well_formed >> fs[inst_wf_def]) >>
      simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops actual_preds inst.inst_operands` >>
      simp[label_positions_ok_def] >>
      Cases_on `t` >> gvs[phi_well_formed_def] >>
      Cases_on `t'` >> gvs[label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def] >>
      Cases_on `h` >> Cases_on `h'` >>
      gvs[phi_well_formed_def, label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def]) >>
  simp[fix_phi_inst_non_phi]
QED

Theorem fix_all_phis_fn_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (fix_all_phis fn)
Proof
  simp[fn_inst_wf_def, fix_all_phis_def, MEM_MAP, PULL_EXISTS,
       fix_phis_in_block_mem] >> rpt strip_tac >> gvs[] >>
  irule inst_wf_fix_phi_inst >> metis_tac[]
QED

Theorem fix_all_phis_label_positions_ok:
  fn_inst_wf fn /\ EVERY label_positions_ok (fn_insts fn) ==>
  EVERY label_positions_ok (fn_insts (fix_all_phis fn))
Proof
  simp[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem, fix_all_phis_def,
       MEM_MAP, PULL_EXISTS, fix_phis_in_block_mem] >> rpt strip_tac >> gvs[] >>
  irule label_positions_ok_fix_phi_inst >>
  fs[fn_inst_wf_def] >> metis_tac[]
QED

Theorem remove_unreachable_blocks_fn_inst_wf:
  fn_inst_wf fn ==> fn_inst_wf (remove_unreachable_blocks fn)
Proof
  simp[fn_inst_wf_def] >> strip_tac >>
  Cases_on `fn_entry_label fn` >>
  simp[remove_unreachable_blocks_def, MEM_FILTER] >> metis_tac[]
QED

Theorem remove_unreachable_blocks_label_positions_ok:
  EVERY label_positions_ok (fn_insts fn) ==>
  EVERY label_positions_ok (fn_insts (remove_unreachable_blocks fn))
Proof
  simp[EVERY_MEM] >> strip_tac >>
  ho_match_mp_tac (GEN_ALL remove_unreachable_blocks_inst_property) >> simp[]
QED

Theorem remove_unreachable_blocks_ssa_invariant:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  first_block_no_preds fn /\ scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) ==>
  wf_ssa (remove_unreachable_blocks fn) /\
  wf_function (remove_unreachable_blocks fn) /\
  fn_inst_wf (remove_unreachable_blocks fn) /\
  first_block_no_preds (remove_unreachable_blocks fn) /\
  scfg_phi_safe (remove_unreachable_blocks fn) /\
  fn_defs_reach_uses (remove_unreachable_blocks fn) /\
  EVERY label_positions_ok (fn_insts (remove_unreachable_blocks fn)) /\
  all_reachable (remove_unreachable_blocks fn)
Proof
  strip_tac >> rpt conj_tac
  >- (fs[wf_ssa_def] >>
      metis_tac[remove_unreachable_blocks_ssa,
                remove_unreachable_blocks_def_dominates_uses])
  >- metis_tac[remove_unreachable_blocks_wf]
  >- metis_tac[remove_unreachable_blocks_fn_inst_wf]
  >- metis_tac[remove_unreachable_blocks_first_block_no_preds]
  >- metis_tac[remove_unreachable_blocks_phi_safe]
  >- metis_tac[remove_unreachable_blocks_defs_reach_uses]
  >- metis_tac[remove_unreachable_blocks_label_positions_ok] >>
  metis_tac[remove_unreachable_blocks_reachable]
QED

Theorem fix_all_phis_ssa_invariant:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  first_block_no_preds fn /\ scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) /\ all_reachable fn ==>
  wf_ssa (fix_all_phis fn) /\ wf_function (fix_all_phis fn) /\
  fn_inst_wf (fix_all_phis fn) /\ first_block_no_preds (fix_all_phis fn) /\
  scfg_phi_safe (fix_all_phis fn) /\ fn_defs_reach_uses (fix_all_phis fn) /\
  EVERY label_positions_ok (fn_insts (fix_all_phis fn)) /\
  all_reachable (fix_all_phis fn)
Proof
  strip_tac >> rpt conj_tac
  >- (fs[wf_ssa_def] >>
      metis_tac[fix_all_phis_ssa, fix_all_phis_def_dominates_uses])
  >- metis_tac[fix_all_phis_wf]
  >- metis_tac[fix_all_phis_fn_inst_wf]
  >- metis_tac[fix_all_phis_first_block_no_preds]
  >- metis_tac[fix_all_phis_phi_safe]
  >- metis_tac[fix_all_phis_defs_reach_uses]
  >- metis_tac[fix_all_phis_label_positions_ok] >>
  metis_tac[fix_all_phis_all_reachable]
QED

Theorem simplify_cfg_round_entry_ssa_invariant:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  first_block_no_preds fn /\ scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) ==>
  wf_ssa (fix_all_phis (remove_unreachable_blocks fn)) /\
  wf_function (fix_all_phis (remove_unreachable_blocks fn)) /\
  fn_inst_wf (fix_all_phis (remove_unreachable_blocks fn)) /\
  first_block_no_preds (fix_all_phis (remove_unreachable_blocks fn)) /\
  scfg_phi_safe (fix_all_phis (remove_unreachable_blocks fn)) /\
  fn_defs_reach_uses (fix_all_phis (remove_unreachable_blocks fn)) /\
  EVERY label_positions_ok
    (fn_insts (fix_all_phis (remove_unreachable_blocks fn))) /\
  all_reachable (fix_all_phis (remove_unreachable_blocks fn))
Proof
  strip_tac >> drule_all remove_unreachable_blocks_ssa_invariant >>
  strip_tac >> irule fix_all_phis_ssa_invariant >> simp[]
QED

Theorem subst_phi_pair_origin:
  phi_well_formed inst.inst_operands /\
  phi_well_formed inst'.inst_operands /\ p <> old /\
  subst_label_inst old new inst' = subst_label_inst old new inst /\
  MEM (p,v) (phi_pairs inst'.inst_operands) ==>
  ?q. MEM (q,v) (phi_pairs inst.inst_operands) /\
      p = (if q = old then new else q)
Proof
  strip_tac >>
  `MEM (p,v) (phi_pairs (subst_label_inst old new inst').inst_operands)` by
    (qpat_x_assum `subst_label_inst _ _ _ = _` kall_tac >>
     simp[subst_label_inst_def, phi_pairs_subst_label_ops, MEM_MAP] >>
     qexists `(p,v)` >> simp[]) >>
  `MEM (p,v) (phi_pairs (subst_label_inst old new inst).inst_operands)` by
    metis_tac[] >>
  qpat_x_assum `subst_label_inst _ _ _ = _` kall_tac >>
  qpat_x_assum `MEM _ (phi_pairs (subst_label_inst _ _ inst').inst_operands)` kall_tac >>
  gvs[subst_label_inst_def, phi_pairs_subst_label_ops, MEM_MAP] >>
  rename1 `MEM pair (phi_pairs inst.inst_operands)` >>
  qexists `FST pair` >> simp[]
QED

Theorem chain_merge_phi_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_preds fn /\ fn_defs_reach_uses fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))) /\
  MEM bb' fn'.fn_blocks /\ MEM inst' bb'.bb_instructions /\ inst'.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs inst'.inst_operands) /\
  MEM pb' fn'.fn_blocks /\ pb'.bb_label = p ==>
  def_on_all_paths fn' pb' NONE v
Proof
  strip_tac >>
  `fn_inst_wf fn'` by
    (gvs[] >> irule chain_merge_fn_inst_wf >> simp[]) >>
  `inst_wf inst'` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed inst'.inst_operands` by gvs[inst_wf_def] >>
  `MEM p (fn_labels fn')` by
    (simp[NoAsms, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `fn_labels fn' = FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn)` by
    gvs[chain_merge_fn_labels] >>
  `p <> b.bb_label` by fs[MEM_FILTER] >>
  `?bb inst. MEM bb fn.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    subst_label_inst b.bb_label a.bb_label inst' =
      subst_label_inst b.bb_label a.bb_label inst` by
    (irule chain_merge_phi_source >> gvs[]) >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  drule_all subst_phi_pair_origin >> strip_tac >>
  `fn_cfg_edge fn q bb.bb_label` by
    (fs[simplifyCfgPhiPredsTheory.scfg_phi_preds_def] >> metis_tac[]) >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = q` by
    (fs[fn_cfg_edge_def] >> metis_tac[]) >>
  `def_on_all_paths fn pb NONE v` by
    (fs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  `pb'.bb_label = (if pb.bb_label = b.bb_label then a.bb_label else pb.bb_label)` by
    metis_tac[] >>
  drule_all chain_merge_def_on_all_paths_endpoint >> simp[]
QED

Theorem chain_merge_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_preds fn /\ fn_defs_reach_uses fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b))) ==>
  fn_defs_reach_uses fn'
Proof
  strip_tac >> simp[NoAsms, fn_defs_reach_uses_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> simp[IgnAsm `fn' = _`]
  >- (rpt strip_tac >> irule chain_merge_phi_defs_reach_uses >> metis_tac[]) >>
  rpt strip_tac >> irule chain_merge_ordinary_defs_reach_uses >> metis_tac[]
QED
