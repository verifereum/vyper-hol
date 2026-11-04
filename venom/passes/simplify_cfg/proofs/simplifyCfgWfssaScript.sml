Theory simplifyCfgWfssa
Ancestors
  simplifyCfgPhiRepair simplifyCfgDataflow simplifyCfgStruct simplifyCfgDefs
  simplifyCfgRepairDataflow simplifyCfgChainDataflow simplifyCfgBypassDataflow
  cfgTransform simplifyCfgPhiPreds simplifyCfgShape
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

Theorem do_merge_jump_fn_inst_wf:
  fn_inst_wf fn /\ MEM a fn.fn_blocks /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==> fn_inst_wf fn'
Proof
  strip_tac >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn.fn_blocks` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions) fn'.fn_blocks` by
    (irule do_merge_jump_every_inst >> qexistsl [`a`, `b`, `fn`, `lm`, `lm'`] >>
     simp[inst_wf_update_phi_bypass] >> rpt strip_tac >>
     IF_CASES_TAC >> simp[] >> irule inst_wf_canon_jnz_inst >>
     qpat_x_assum `EVERY _ _` kall_tac >>
     qpat_x_assum `fn_inst_wf _` kall_tac >>
     qpat_x_assum `do_merge_jump _ _ _ _ = _` kall_tac >>
     Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
     gvs[subst_label_inst_def, inst_wf_def, EVERY_MAP, subst_label_op_def]
     >- (rpt IF_CASES_TAC >> simp[])
     >- (rpt IF_CASES_TAC >> simp[])
     >- (fs[EVERY_MEM] >> rpt strip_tac >>
         first_x_assum drule >> Cases_on `x` >>
         simp[venomStateTheory.get_label_def, subst_label_op_def] >>
         rpt IF_CASES_TAC >> simp[venomStateTheory.get_label_def]) >>
     Cases_on `inst.inst_operands` >>
     gvs[dretShapeDefsTheory.parse_dret_shape_def] >>
     rename1 `inst.inst_operands = op::ops` >> Cases_on `op` >>
     gvs[dretShapeDefsTheory.parse_dret_shape_def, subst_label_op_def]) >>
  fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED

Theorem update_phi_bypass_pairs:
  phi_well_formed inst.inst_operands /\ inst.inst_opcode = PHI ==>
  phi_pairs (update_phi_bypass a b inst).inst_operands =
    if MEM (Label a) inst.inst_operands then
      FILTER (\p. FST p <> b) (phi_pairs inst.inst_operands)
    else MAP (\p. (if FST p = b then a else FST p, SND p))
           (phi_pairs inst.inst_operands)
Proof
  strip_tac >> Cases_on `MEM (Label a) inst.inst_operands`
  >- simp[update_phi_bypass_def, phi_pairs_remove_phi_label] >>
  ` (\op. case op of Label l => if l = b then Label a else Label l | _ => op) =
     subst_label_op b a` by
    (simp[FUN_EQ_THM] >> Cases >> simp[subst_label_op_def]) >>
  simp[update_phi_bypass_def, phi_pairs_subst_label_ops]
QED

Theorem phi_pair_label_mem:
  !ops. phi_well_formed ops ==>
    (MEM (Label lbl) ops <=> MEM lbl (MAP FST (phi_pairs ops)))
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, phi_pairs_def] >> metis_tac[]
QED

Theorem update_phi_bypass_distinct:
  phi_well_formed inst.inst_operands /\ inst.inst_opcode = PHI /\
  ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) ==>
  ALL_DISTINCT (MAP FST (phi_pairs (update_phi_bypass a b inst).inst_operands))
Proof
  strip_tac >> simp[update_phi_bypass_pairs] >>
  Cases_on `MEM (Label a) inst.inst_operands` >> simp[]
  >- (`!ps:(string # string) list. MAP FST (FILTER (\p. FST p <> b) ps) =
             FILTER (\p. p <> b) (MAP FST ps)` by
        (Induct >> simp[] >> gen_tac >> IF_CASES_TAC >> simp[]) >>
      asm_rewrite_tac[] >> irule FILTER_ALL_DISTINCT >> simp[]) >>
  `~MEM a (MAP FST (phi_pairs inst.inst_operands))` by
    metis_tac[phi_pair_label_mem] >>
  `MAP FST (MAP (\p. (if FST p = b then a else FST p, SND p))
      (phi_pairs inst.inst_operands)) =
   MAP (\p. if p = b then a else p) (MAP FST (phi_pairs inst.inst_operands))` by
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
  asm_rewrite_tac[] >> irule ALL_DISTINCT_MAP_INJ >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `x = b` >> Cases_on `y = b` >> gvs[]
QED

Theorem replace_block_lookup_map:
  !bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    lookup_block lbl bbs = SOME bb ==>
    replace_block lbl (f bb) bbs =
      MAP (\b. if b.bb_label = lbl then f b else b) bbs
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> gen_tac >>
  Cases_on `h.bb_label = lbl` >>
  simp[lookup_block_def, FIND_thm, replace_block_def] >> strip_tac
  >- (gvs[] >> irule MAP_CONG >>
      simp[] >> fs[MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `_ ==> _` mp_tac >>
  simp[lookup_block_def, replace_block_def]
QED

Theorem update_succ_phi_labels_nil:
  update_succ_phi_labels old new bbs [] = bbs
Proof
  simp[update_succ_phi_labels_def]
QED

Theorem update_succ_phi_labels_cons:
  update_succ_phi_labels old new bbs (h::ss) =
  update_succ_phi_labels old new
    (case lookup_block h bbs of NONE => bbs | SOME bb =>
      replace_block h (bb with bb_instructions :=
        MAP (\i. if i.inst_opcode = PHI then subst_label_inst old new i else i)
          bb.bb_instructions) bbs) ss
Proof
  `(\i. if i.inst_opcode <> PHI then i else subst_label_inst old new i) =
   (\i. if i.inst_opcode = PHI then subst_label_inst old new i else i)` by
    (simp[FUN_EQ_THM] >> gen_tac >> Cases_on `i.inst_opcode = PHI` >> simp[]) >>
  simp[update_succ_phi_labels_def]
QED

Theorem update_succ_phi_labels_singleton:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  update_succ_phi_labels old new bbs [h] =
    MAP (\bb. if bb.bb_label = h then bb with bb_instructions :=
      MAP (\i. if i.inst_opcode = PHI then subst_label_inst old new i else i)
        bb.bb_instructions else bb) bbs
Proof
  strip_tac >> rewrite_tac[update_succ_phi_labels_cons, update_succ_phi_labels_nil] >>
  Cases_on `lookup_block h bbs` >> simp[]
  >- (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
      `MEM (EL x bbs) bbs` by simp[EL_MEM] >>
      `!bb. MEM bb bbs ==> bb.bb_label <> h` by
        (rpt strip_tac >>
         `lookup_block bb.bb_label bbs = SOME bb` by
           (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >> gvs[]) >>
      simp[]) >>
  drule_all replace_block_lookup_map >>
  disch_then (qspec_then
    `\bb. bb with bb_instructions := MAP
      (\i. if i.inst_opcode = PHI then subst_label_inst old new i else i)
      bb.bb_instructions` mp_tac) >> simp[]
QED

Theorem update_succ_phi_labels_exact:
  !succs bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  update_succ_phi_labels old new bbs succs =
    MAP (\bb. if MEM bb.bb_label succs then bb with bb_instructions :=
      MAP (\i. if i.inst_opcode = PHI then subst_label_inst old new i else i)
        bb.bb_instructions else bb) bbs
Proof
  Induct >- simp[update_succ_phi_labels_nil] >> rpt strip_tac >>
  `update_succ_phi_labels old new bbs (h::succs) =
   update_succ_phi_labels old new
     (update_succ_phi_labels old new bbs [h]) succs` by
    simp[update_succ_phi_labels_cons, update_succ_phi_labels_nil] >>
  asm_rewrite_tac[] >>
  asm_simp_tac (srw_ss()) [update_succ_phi_labels_singleton] >>
  qmatch_goalsub_abbrev_tac `update_succ_phi_labels old new bs succs` >>
  `MAP (\b. b.bb_label) bs = MAP (\b. b.bb_label) bbs` by
    (simp[Abbr `bs`, MAP_MAP_o, combinTheory.o_DEF] >>
     irule MAP_CONG >> simp[] >> rpt strip_tac >> IF_CASES_TAC >> simp[]) >>
  first_x_assum (qspec_then `bs` mp_tac) >> asm_rewrite_tac[] >>
  disch_then SUBST1_TAC >>
  simp[Abbr `bs`, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  Cases_on `x.bb_label = h` >> Cases_on `MEM x.bb_label succs` >> gvs[] >>
  `MAP (\i. if i.inst_opcode = PHI then subst_label_inst old new i else i)
    (MAP (\i. if i.inst_opcode = PHI then subst_label_inst old new i else i)
      x.bb_instructions) =
   MAP (\i. if i.inst_opcode = PHI then subst_label_inst old new i else i)
      x.bb_instructions` by
    (simp[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >> simp[] >>
     rpt strip_tac >> rename1 `MEM i x.bb_instructions` >>
     ` (subst_label_inst old new i).inst_opcode = i.inst_opcode` by
       simp[subst_label_inst_def] >>
     Cases_on `i.inst_opcode = PHI` >> simp[subst_label_inst_idempotent]) >> simp[]
QED

Theorem update_succ_phi_labels_phi_source_exact:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  MEM bb' (update_succ_phi_labels old new bbs succs) /\
  MEM inst' bb'.bb_instructions /\ inst'.inst_opcode = PHI ==>
  ?bb inst. MEM bb bbs /\ bb'.bb_label = bb.bb_label /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    inst' = (if MEM bb'.bb_label succs then subst_label_inst old new inst else inst)
Proof
  strip_tac >>
  gvs[update_succ_phi_labels_exact, MEM_MAP] >>
  rename1 `MEM bb bbs` >> Cases_on `MEM bb.bb_label succs` >> gvs[]
  >- (gvs[MEM_MAP] >> qexistsl [`bb`, `i`] >>
      Cases_on `i.inst_opcode = PHI` >> gvs[subst_label_inst_def]) >>
  qexists `bb` >> simp[]
QED

Theorem chain_merge_phi_source_exact:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\
  MEM bb' (update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) /\
  MEM inst' bb'.bb_instructions /\ inst'.inst_opcode = PHI ==>
  ?bb inst. MEM bb fn.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    inst' = (if MEM bb'.bb_label (bb_succs (merge_blocks a b))
             then subst_label_inst b.bb_label a.bb_label inst else inst)
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label /\ no_phis b` by fs[can_merge_blocks_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks)))` by
    (irule chain_merge_base_labels >> fs[wf_function_def]) >>
  drule_all update_succ_phi_labels_phi_source_exact >> strip_tac >>
  gvs[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
  Cases_on `bb''.bb_label = a.bb_label` >> gvs[merge_blocks_def, MEM_APPEND]
  >- (qexistsl [`a`, `inst`] >> simp[] >>
      Cases_on `a.bb_instructions` >> fs[] >> drule MEM_FRONT >> simp[])
  >- (fs[no_phis_def, EVERY_MEM] >> metis_tac[]) >>
  qexistsl [`bb''`, `inst`] >> simp[]
QED

Theorem chain_phi_no_old_a:
  wf_ssa fn /\ wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\ MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
  ~MEM a.bb_label (MAP FST (phi_pairs inst.inst_operands))
Proof
  strip_tac >>
  `phi_edge_uses_wf fn bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `!pred. fn_cfg_edge fn pred bb.bb_label <=>
    ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred` by
    fs[phi_edge_uses_wf_def] >>
  strip_tac >> `fn_cfg_edge fn a.bb_label bb.bb_label` by
    (fs[MEM_MAP] >> metis_tac[]) >>
  `bb_succs a = [b.bb_label]` by fs[can_merge_blocks_def] >>
  fs[fn_cfg_edge_def] >>
  `bb' = a` by metis_tac[same_label_same_block] >> gvs[]
QED

Theorem phi_subst_label_distinct:
  phi_well_formed inst.inst_operands /\
  ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
  ~MEM new (MAP FST (phi_pairs inst.inst_operands)) ==>
  ALL_DISTINCT (MAP FST (phi_pairs (subst_label_inst old new inst).inst_operands))
Proof
  strip_tac >> simp[subst_label_inst_def, phi_pairs_subst_label_ops,
    MAP_MAP_o, combinTheory.o_DEF] >>
  `MAP (\p. if FST p = old then new else FST p) (phi_pairs inst.inst_operands) =
   MAP (\p. if p = old then new else p) (MAP FST (phi_pairs inst.inst_operands))` by
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
  asm_rewrite_tac[] >> irule ALL_DISTINCT_MAP_INJ >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `x = old` >> Cases_on `y = old` >> gvs[]
QED

Theorem chain_merge_phi_distinct:
  wf_ssa fn /\ wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\
  MEM bb' (update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) /\
  MEM inst' bb'.bb_instructions /\ inst'.inst_opcode = PHI ==>
  ALL_DISTINCT (MAP FST (phi_pairs inst'.inst_operands))
Proof
  strip_tac >>
  `bb'.bb_label <> b.bb_label` by
    (qmatch_asmsub_abbrev_tac `MEM bb' bs` >>
     `MEM bb'.bb_label (fn_labels (fn with fn_blocks := bs))` by
       (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
     fs[Abbr `bs`, chain_merge_fn_labels, MEM_FILTER]) >>
  drule_all chain_merge_phi_source_exact >> strip_tac >>
  `phi_edge_uses_wf fn bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `~MEM a.bb_label (MAP FST (phi_pairs inst.inst_operands))` by
    (irule chain_phi_no_old_a >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands /\
   ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))` by
    fs[phi_edge_uses_wf_def] >>
  drule_all phi_subst_label_distinct >>
  disch_then (qspec_then `b.bb_label` assume_tac) >>
  Cases_on `MEM bb'.bb_label (bb_succs (merge_blocks a b))` >> gvs[]
QED

Theorem chain_merge_edge_sources:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\ dst <> b.bb_label /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) ==>
  (fn_cfg_edge fn' pred dst <=>
   ?q. fn_cfg_edge fn q dst /\ pred = (if q = b.bb_label then a.bb_label else q))
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label /\ bb_succs a = [b.bb_label]` by
    fs[can_merge_blocks_def] >>
  `~fn_cfg_edge fn a.bb_label dst` by
    (strip_tac >> fs[fn_cfg_edge_def] >>
     `bb = a` by metis_tac[same_label_same_block] >> gvs[]) >>
  `~fn_cfg_edge fn' b.bb_label dst` by
    (strip_tac >>
     `MEM b.bb_label (fn_labels fn')` by
       (gvs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
     gvs[chain_merge_fn_labels, MEM_FILTER]) >>
  Cases_on `pred = b.bb_label` >- (gvs[] >> metis_tac[]) >>
  `fn_cfg_edge fn' pred dst <=>
    if pred = a.bb_label then fn_cfg_edge fn b.bb_label dst
    else fn_cfg_edge fn pred dst` by
    (gvs[] >> irule chain_merge_edge >> simp[]) >>
  asm_rewrite_tac[] >> Cases_on `pred = a.bb_label` >> gvs[] >> metis_tac[]
QED

Theorem phi_subst_label_pred:
  phi_well_formed inst.inst_operands ==>
  ((?p. MEM p (phi_pairs (subst_label_inst old new inst).inst_operands) /\
        FST p = pred) <=>
   ?q. (?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = q) /\
       pred = (if q = old then new else q))
Proof
  strip_tac >> simp[subst_label_inst_def, phi_pairs_subst_label_ops, MEM_MAP] >>
  eq_tac >> rpt strip_tac >> gvs[]
  >- (rename1 `MEM pair (phi_pairs inst.inst_operands)` >>
      qexists `FST pair` >> metis_tac[]) >>
  rename1 `MEM pair (phi_pairs inst.inst_operands)` >>
  qexists `(if FST pair = old then new else FST pair, SND pair)` >>
  simp[] >> qexists `pair` >> simp[]
QED

Theorem chain_merge_phi_coverage:
  wf_ssa fn /\ wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) /\
  MEM bb' fn'.fn_blocks /\ MEM inst' bb'.bb_instructions /\ inst'.inst_opcode = PHI ==>
  (fn_cfg_edge fn' pred bb'.bb_label <=>
   ?p. MEM p (phi_pairs inst'.inst_operands) /\ FST p = pred)
Proof
  strip_tac >>
  `bb'.bb_label <> b.bb_label` by
    (`MEM bb'.bb_label (fn_labels fn')` by
       (simp[NoAsms, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
     gvs[chain_merge_fn_labels, MEM_FILTER]) >>
  `?bb inst. MEM bb fn.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    inst' = (if MEM bb'.bb_label (bb_succs (merge_blocks a b))
             then subst_label_inst b.bb_label a.bb_label inst else inst)` by
    (irule chain_merge_phi_source_exact >> gvs[]) >>
  `phi_edge_uses_wf fn bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands /\
    (!p. fn_cfg_edge fn p bb'.bb_label <=>
      ?pair. MEM pair (phi_pairs inst.inst_operands) /\ FST pair = p)` by
    gvs[phi_edge_uses_wf_def] >>
  `fn_cfg_edge fn' pred bb'.bb_label <=>
    ?q. fn_cfg_edge fn q bb'.bb_label /\
        pred = (if q = b.bb_label then a.bb_label else q)` by
    (irule chain_merge_edge_sources >> simp[]) >>
  asm_rewrite_tac[] >>
  Cases_on `MEM bb'.bb_label (bb_succs (merge_blocks a b))`
  >- (gvs[] >> simp[phi_subst_label_pred] >> metis_tac[]) >>
  `b.bb_instructions <> []` by
    metis_tac[wf_function_bb_well_formed, bb_well_formed_def] >>
  `~fn_cfg_edge fn b.bb_label bb'.bb_label` by
    (strip_tac >> fs[fn_cfg_edge_def] >>
     `bb'' = b` by metis_tac[same_label_same_block] >>
     gvs[bb_succs_merge_blocks]) >>
  gvs[] >> metis_tac[]
QED

Theorem chain_merge_phi_shape:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) ==>
  !bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands /\
    ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
    (!pred. fn_cfg_edge fn' pred bb.bb_label <=>
      ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred)
Proof
  strip_tac >>
  `fn_inst_wf fn'` by
    (gvs[] >> irule chain_merge_fn_inst_wf >> simp[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`inst_wf inst` by metis_tac[fn_inst_wf_def] >> gvs[inst_wf_def]) >>
  conj_tac
  >- (gvs[] >> drule_all chain_merge_phi_distinct >> simp[]) >>
  gen_tac >> irule chain_merge_phi_coverage >> metis_tac[]
QED

Theorem chain_merge_edge_simulation:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) /\ fn_cfg_edge fn src dst ==>
  (if src = b.bb_label then a.bb_label else src) =
    (if dst = b.bb_label then a.bb_label else dst) \/
  fn_cfg_edge fn' (if src = b.bb_label then a.bb_label else src)
    (if dst = b.bb_label then a.bb_label else dst)
Proof
  strip_tac >> Cases_on `dst = b.bb_label`
  >- (`src = a.bb_label` by
        (fs[fn_cfg_edge_def] >>
         `bb = a` by metis_tac[can_merge_blocks_unique_pred] >> gvs[]) >>
      fs[can_merge_blocks_def]) >>
  disj2_tac >> simp[] >>
  drule_all chain_merge_edge_sources >>
  disch_then (qspec_then `if src = b.bb_label then a.bb_label else src` mp_tac) >>
  simp[] >> strip_tac >> qexists `src` >> simp[]
QED

Theorem rtc_map_simulation:
  (!x y. r x y ==> f x = f y \/ s (f x) (f y)) ==>
  !x y. RTC r x y ==> RTC s (f x) (f y)
Proof
  strip_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >>
  rpt strip_tac >>
  `f x = f x' \/ s (f x) (f x')` by metis_tac[]
  >- gvs[] >> metis_tac[relationTheory.RTC_RULES]
QED

Theorem chain_merge_all_reachable:
  wf_function fn /\ first_block_no_preds fn /\ all_reachable fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) ==> all_reachable fn'
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn') /\ fn_has_entry fn'` by
    (gvs[] >> irule chain_merge_labels_entry >> qexistsl [`a`, `b`, `fn`] >>
     simp[] >> fs[wf_function_def] >> conj_tac >>
     irule venomExecPropsTheory.MEM_lookup_block >> simp[GSYM fn_labels_def]) >>
  `fn.fn_blocks <> [] /\ fn'.fn_blocks <> []` by
    fs[wf_function_def, fn_has_entry_def] >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (gvs[] >> irule chain_merge_entry_label >> simp[]) >>
  `(HD fn.fn_blocks).bb_label <> b.bb_label` by
    (fs[first_block_no_preds_def, EVERY_MEM, can_merge_blocks_def] >>
     qpat_x_assum `!bb. _` (qspec_then `a` mp_tac) >> simp[]) >>
  `!x y. RTC (fn_cfg_edge fn) x y ==>
    RTC (fn_cfg_edge fn') (if x = b.bb_label then a.bb_label else x)
      (if y = b.bb_label then a.bb_label else y)` by
    (ho_match_mp_tac rtc_map_simulation >> rpt strip_tac >>
     irule chain_merge_edge_simulation >> metis_tac[]) >>
  simp[all_reachable_def] >> qx_gen_tac `bb` >> strip_tac >>
  `MEM bb.bb_label (fn_labels fn')` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM bb.bb_label (fn_labels fn) /\ bb.bb_label <> b.bb_label` by
    gvs[chain_merge_fn_labels, MEM_FILTER] >>
  `fn_reachable fn bb.bb_label` by
    (fs[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `fn_entry_label fn' = fn_entry_label fn` by
    (Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  gvs[fn_reachable_def] >>
  `entry = (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  first_x_assum (qspecl_then [`entry`, `bb.bb_label`] mp_tac) >> simp[]
QED

Theorem chain_merge_label_positions_ok:
  EVERY label_positions_ok (fn_insts fn) /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) ==>
  EVERY label_positions_ok (fn_insts fn')
Proof
  strip_tac >>
  `EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn.fn_blocks` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  `EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn'.fn_blocks` by
    (gvs[] >> irule chain_merge_every_inst >> simp[] >> rpt strip_tac >>
     gvs[subst_label_inst_def, label_positions_ok_def]) >>
  fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]
QED

Theorem chain_merge_entry_no_phis:
  wf_function fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) ==>
  EVERY (\inst. inst.inst_opcode <> PHI) (HD fn'.fn_blocks).bb_instructions
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn') /\ fn_has_entry fn'` by
    (gvs[] >> irule chain_merge_labels_entry >> qexistsl [`a`, `b`, `fn`] >>
     simp[] >> fs[wf_function_def] >> conj_tac >>
     irule venomExecPropsTheory.MEM_lookup_block >> simp[GSYM fn_labels_def]) >>
  `fn.fn_blocks <> [] /\ fn'.fn_blocks <> []` by
    fs[wf_function_def, fn_has_entry_def] >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (gvs[] >> irule chain_merge_entry_label >> simp[]) >>
  simp[EVERY_MEM] >> qx_gen_tac `inst'` >> strip_tac >> strip_tac >>
  `?bb inst. MEM bb fn.fn_blocks /\ (HD fn'.fn_blocks).bb_label = bb.bb_label /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    inst' = (if MEM (HD fn'.fn_blocks).bb_label (bb_succs (merge_blocks a b))
             then subst_label_inst b.bb_label a.bb_label inst else inst)` by
    (`MEM (HD fn'.fn_blocks) fn'.fn_blocks` by
       (Cases_on `fn'.fn_blocks` >> gvs[]) >>
     irule chain_merge_phi_source_exact >> gvs[]) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `bb = HD fn.fn_blocks` by metis_tac[same_label_same_block] >>
  drule scfg_phi_safe_entry >> disch_then assume_tac >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem wf_ssa_phi_preds:
  wf_ssa fn ==> scfg_phi_preds fn
Proof
  simp[scfg_phi_preds_def] >> rpt strip_tac >>
  `phi_edge_uses_wf fn bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  fs[phi_edge_uses_wf_def] >> metis_tac[pairTheory.FST]
QED

Theorem chain_merge_ssa_invariant:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) /\ all_reachable fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks := update_succ_phi_labels b.bb_label a.bb_label
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
    (bb_succs (merge_blocks a b))) ==>
  wf_ssa fn' /\ wf_function fn' /\ fn_inst_wf fn' /\ first_block_no_preds fn' /\
  scfg_phi_safe fn' /\ fn_defs_reach_uses fn' /\
  EVERY label_positions_ok (fn_insts fn') /\ all_reachable fn'
Proof
  strip_tac >>
  `lookup_block a.bb_label fn.fn_blocks = SOME a /\
   lookup_block b.bb_label fn.fn_blocks = SOME b` by
    (conj_tac >> irule venomExecPropsTheory.MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def]) >>
  `wf_function fn'` by (gvs[] >> irule chain_merge_wf >> simp[]) >>
  `fn_inst_wf fn'` by (gvs[] >> irule chain_merge_fn_inst_wf >> simp[]) >>
  `first_block_no_preds fn'` by
    (gvs[] >> irule chain_merge_first_block_no_preds >> simp[]) >>
  `all_reachable fn'` by (irule chain_merge_all_reachable >> metis_tac[]) >>
  `ssa_form fn'` by
    (gvs[] >> irule chain_merge_ssa >> fs[wf_ssa_def]) >>
  `scfg_phi_preds fn` by metis_tac[wf_ssa_phi_preds] >>
  `fn_defs_reach_uses fn'` by (irule chain_merge_defs_reach_uses >> metis_tac[]) >>
  `wf_ssa fn'` by
    (irule reachable_defs_reach_uses_wf_ssa >> simp[] >>
     rpt gen_tac >> strip_tac >> irule chain_merge_phi_shape >> simp[] >>
     qexistsl [`a`, `b`, `fn`] >> simp[]) >>
  `scfg_phi_safe fn'` by
    (irule wf_ssa_phi_safe >> conj_tac >- asm_rewrite_tac[] >>
     irule chain_merge_entry_no_phis >> metis_tac[]) >>
  `EVERY label_positions_ok (fn_insts fn')` by
    (irule chain_merge_label_positions_ok >> metis_tac[]) >> simp[]
QED

Theorem canon_jnz_inst_successors_exact:
  label_positions_ok inst ==>
  (MEM lbl (get_successors (canon_jnz_inst inst)) <=>
   MEM lbl (get_successors inst))
Proof
  simp[canon_jnz_inst_def] >> rpt CASE_TAC >> gvs[] >>
  gvs[label_positions_ok_def, get_successors_mem_label, is_terminator_def] >>
  rpt CASE_TAC >>
  Cases_on `h` >> gvs[stackPlanTypesTheory.is_label_operand_def]
QED


Theorem subst_label_op_is_label:
  is_label_operand (subst_label_op old new op) = is_label_operand op
Proof
  Cases_on `op` >> simp[subst_label_op_def,
    stackPlanTypesTheory.is_label_operand_def] >> IF_CASES_TAC >>
  simp[stackPlanTypesTheory.is_label_operand_def]
QED

Theorem bypass_source_label_positions_ok:
  label_positions_ok inst ==>
  label_positions_ok (if ~is_terminator inst.inst_opcode then inst
    else canon_jnz_inst (subst_label_inst old new inst))
Proof
  strip_tac >> IF_CASES_TAC >- simp[] >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (Cases_on `inst.inst_operands` >>
      gvs[subst_label_inst_def, canon_jnz_inst_def, label_positions_ok_def,
          EVERY_MAP, subst_label_op_is_label] >>
      Cases_on `t` >>
      gvs[subst_label_inst_def, canon_jnz_inst_def, label_positions_ok_def,
          EVERY_MAP, subst_label_op_is_label] >>
      Cases_on `t'`
      >- (Cases_on `h'` >>
          gvs[subst_label_inst_def, canon_jnz_inst_def, label_positions_ok_def,
              EVERY_MAP, subst_label_op_is_label, subst_label_op_def,
              stackPlanTypesTheory.is_label_operand_def]) >>
      gvs[subst_label_inst_def, canon_jnz_inst_def, label_positions_ok_def,
          EVERY_MAP, subst_label_op_is_label] >>
      Cases_on `t` >>
      gvs[subst_label_inst_def, canon_jnz_inst_def, label_positions_ok_def,
          EVERY_MAP, subst_label_op_is_label] >>
      Cases_on `h'` >> Cases_on `h''` >>
      gvs[label_positions_ok_def, subst_label_op_def, subst_label_op_is_label,
          EVERY_MAP, stackPlanTypesTheory.is_label_operand_def] >>
      rpt IF_CASES_TAC >>
      gvs[label_positions_ok_def, subst_label_op_is_label,
          stackPlanTypesTheory.is_label_operand_def]) >>
  `canon_jnz_inst (subst_label_inst old new inst) =
   subst_label_inst old new inst` by
    (spose_not_then (mp_tac o MATCH_MP canon_jnz_inst_changed) >>
     simp[subst_label_inst_def]) >>
  simp[] >> Cases_on `inst.inst_opcode = JMP`
  >- (Cases_on `inst.inst_operands` >>
      gvs[subst_label_inst_def, label_positions_ok_def,
          EVERY_MAP, subst_label_op_is_label] >>
      Cases_on `h` >> Cases_on `t` >>
      gvs[subst_label_inst_def, label_positions_ok_def,
          subst_label_op_def, EVERY_MAP, subst_label_op_is_label,
          stackPlanTypesTheory.is_label_operand_def] >>
      rpt IF_CASES_TAC >> simp[]) >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, subst_label_inst_def,
      label_positions_ok_def, EVERY_MAP, subst_label_op_is_label]
QED

Theorem bypass_source_successors_exact:
  label_positions_ok inst ==>
  (MEM lbl (get_successors
    (if ~is_terminator inst.inst_opcode then inst
     else canon_jnz_inst (subst_label_inst old new inst))) <=>
   ?src. MEM src (get_successors inst) /\
         lbl = (if src = old then new else src))
Proof
  strip_tac >> IF_CASES_TAC
  >- simp[get_successors_mem_label] >>
  Cases_on `canon_jnz_inst (subst_label_inst old new inst) =
            subst_label_inst old new inst`
  >- (simp[get_successors_mem_label, subst_label_inst_def, MEM_MAP] >>
      eq_tac >> rpt strip_tac >> gvs[]
      >- (rename1 `MEM op inst.inst_operands` >> Cases_on `op` >>
          gvs[subst_label_op_def] >> qexists `s` >>
          Cases_on `s = old` >> gvs[]) >>
      qexists `Label src` >> simp[subst_label_op_def] >>
      Cases_on `src = old` >> gvs[]) >>
  drule canon_jnz_inst_changed >>
  simp[subst_label_inst_def] >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  rename1 `inst.inst_operands = [cond; yes; no]` >>
  Cases_on `yes` >> Cases_on `no` >>
  gvs[label_positions_ok_def, subst_label_op_def,
      stackPlanTypesTheory.is_label_operand_def] >>
  rpt IF_CASES_TAC >>
  gvs[get_successors_mem_label, subst_label_op_is_label] >>
  Cases_on `cond` >>
  gvs[subst_label_op_def, stackPlanTypesTheory.is_label_operand_def,
      is_terminator_def, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  rpt IF_CASES_TAC >> gvs[]

QED

Theorem bb_bypass_source_successors_exact:
  bb_well_formed bb /\ EVERY label_positions_ok bb.bb_instructions ==>
  (MEM lbl (bb_succs (bb with bb_instructions :=
    MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                else canon_jnz_inst (subst_label_inst old new inst))
        bb.bb_instructions)) <=>
   ?src. MEM src (bb_succs bb) /\ lbl = (if src = old then new else src))
Proof
  strip_tac >> `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `label_positions_ok (LAST bb.bb_instructions)` by
    (fs[EVERY_MEM] >> first_x_assum irule >> simp[LAST_MEM]) >>
  Cases_on `bb.bb_instructions` >> gvs[bb_succs_def] >>
  Cases_on `t` >> simp[LAST_MAP, LAST_DEF, bypass_source_successors_exact] >>
  irule bypass_source_successors_exact >> fs[LAST_DEF]
QED

Theorem do_merge_jump_surviving_block:
  do_merge_jump fn a b lm = SOME (fn',lm') /\ MEM bb fn.fn_blocks /\
  bb.bb_label <> b.bb_label ==>
  ?bb'. MEM bb' fn'.fn_blocks /\ bb'.bb_label = bb.bb_label
Proof
  strip_tac >> drule do_merge_jump_fn_labels >>
  rewrite_tac[fn_labels_def] >>
  disch_then (mp_tac o Q.AP_TERM `\ls. MEM bb.bb_label ls`) >>
  simp[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem do_merge_jump_successors_exact:
  wf_function fn /\ EVERY label_positions_ok (fn_insts fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb fn.fn_blocks /\ MEM bb' fn'.fn_blocks /\
  bb'.bb_label = bb.bb_label /\ bb_succs b = [target] ==>
  (MEM lbl (bb_succs bb') <=>
   if bb.bb_label = a.bb_label then
     ?src. MEM src (bb_succs bb) /\
           lbl = (if src = b.bb_label then target else src)
   else MEM lbl (bb_succs bb))
Proof
  strip_tac >> drule_all do_merge_jump_block_map >> strip_tac >>
  rename1 `MEM srcbb fn.fn_blocks` >>
  `srcbb = bb` by metis_tac[same_label_same_block] >> gvs[] >>
  `bb_well_formed bb /\ EVERY label_positions_ok bb.bb_instructions` by
    (fs[wf_function_def, fn_insts_def, EVERY_MEM, fn_insts_blocks_mem] >>
     metis_tac[]) >>
  `bb' = bb with bb_instructions := bb'.bb_instructions` by
    simp[venomInstTheory.basic_block_component_equality] >>
  qpat_x_assum `bb' = bb with bb_instructions := _` SUBST1_TAC >>
  Cases_on `bb.bb_label = a.bb_label`
  >- (Cases_on `target = a.bb_label` >>
      simp[]
      >- (`MAP (\inst. update_phi_bypass a.bb_label b.bb_label
                   (if ~is_terminator inst.inst_opcode then inst
                    else canon_jnz_inst (subst_label_inst b.bb_label a.bb_label inst)))
                  bb.bb_instructions =
           MAP (update_phi_bypass a.bb_label b.bb_label)
             (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                   else canon_jnz_inst (subst_label_inst b.bb_label a.bb_label inst))
                  bb.bb_instructions)` by simp[MAP_MAP_o, combinTheory.o_DEF] >>
          asm_rewrite_tac[] >>
          simp[bb_succs_bypass_source_phi, bb_bypass_source_successors_exact]) >>
      simp[bb_bypass_source_successors_exact]) >>
  Cases_on `bb.bb_label = target` >>
  simp[SF ETA_ss, bb_succs_update_phi_bypass]
QED

Theorem do_merge_jump_phi_source_exact:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ MEM bb' fn'.fn_blocks /\
  MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI ==>
  ?bb inst target. MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
    bb'.bb_label = bb.bb_label /\ bb_succs b = [target] /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    phi = (if bb.bb_label = target then update_phi_bypass a.bb_label b.bb_label inst
           else inst)
Proof
  strip_tac >> drule_all do_merge_jump_block_map >> strip_tac >>
  qpat_x_assum `MEM phi _` mp_tac >> simp[MEM_MAP] >>
  disch_then (qx_choose_then `inst` strip_assume_tac) >>
  `inst.inst_opcode = PHI` by
    (Cases_on `bb.bb_label = a.bb_label` >>
     Cases_on `bb.bb_label = target` >>
     Cases_on `target = a.bb_label` >>
     Cases_on `is_terminator inst.inst_opcode` >>
     gvs[update_phi_bypass_shape, canon_jnz_inst_shape, subst_label_inst_shape,
       combinTheory.I_DEF, is_terminator_def]) >>
  qexistsl [`bb`, `inst`] >> simp[] >>
  Cases_on `bb.bb_label = target` >>
  Cases_on `bb.bb_label = a.bb_label` >> gvs[is_terminator_def]
QED

Theorem do_merge_jump_edge_sources:
  wf_function fn /\ EVERY label_positions_ok (fn_insts fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ bb_succs b = [target] ==>
  (fn_cfg_edge fn' pred lbl <=>
   pred <> b.bb_label /\
   if pred = a.bb_label then
     ?src. fn_cfg_edge fn pred src /\ lbl = (if src = b.bb_label then target else src)
   else fn_cfg_edge fn pred lbl)
Proof
  strip_tac >> eq_tac
  >- (simp[fn_cfg_edge_def] >> strip_tac >>
      rename1 `MEM out fn'.fn_blocks` >>
      drule_all do_merge_jump_block_map >>
      disch_then (qx_choose_then `srcbb` (qx_choose_then `target0` strip_assume_tac)) >>
      `MEM lbl (bb_succs out) <=>
        if srcbb.bb_label = a.bb_label then
          ?src. MEM src (bb_succs srcbb) /\ lbl = (if src = b.bb_label then target else src)
        else MEM lbl (bb_succs srcbb)` by
        (irule do_merge_jump_successors_exact >> metis_tac[]) >>
      gvs[] >> Cases_on `srcbb.bb_label = a.bb_label` >>
      fs[fn_cfg_edge_def] >> metis_tac[]) >>
  strip_tac >> Cases_on `pred = a.bb_label` >> gvs[fn_cfg_edge_def] >>
  `?bb'. MEM bb' fn'.fn_blocks /\ bb'.bb_label = bb.bb_label` by
    (irule do_merge_jump_surviving_block >> metis_tac[]) >>
  `!dest. MEM dest (bb_succs bb') <=>
    if bb.bb_label = a.bb_label then
      ?src. MEM src (bb_succs bb) /\ dest = (if src = b.bb_label then target else src)
    else MEM dest (bb_succs bb)` by
    (gen_tac >> irule do_merge_jump_successors_exact >> metis_tac[]) >>
  qexists `bb'` >> gvs[] >> metis_tac[]
QED

Theorem do_merge_jump_phi_distinct:
  wf_ssa fn /\ wf_function fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ MEM bb' fn'.fn_blocks /\
  MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI ==>
  ALL_DISTINCT (MAP FST (phi_pairs phi.inst_operands))
Proof
  strip_tac >> drule_all do_merge_jump_phi_source_exact >> strip_tac >>
  `phi_edge_uses_wf fn bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands /\
   ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))` by
    fs[phi_edge_uses_wf_def] >>
  Cases_on `bb.bb_label = target` >> gvs[] >>
  irule update_phi_bypass_distinct >> simp[]
QED

Theorem update_phi_bypass_pred:
  phi_well_formed inst.inst_operands /\ inst.inst_opcode = PHI /\ a <> b ==>
  ((?p. MEM p (phi_pairs (update_phi_bypass a b inst).inst_operands) /\ FST p = pred) <=>
   (pred <> b /\ ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred) \/
   (pred = a /\ ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = b))
Proof
  strip_tac >> simp[update_phi_bypass_pairs] >>
  Cases_on `MEM (Label a) inst.inst_operands` >> simp[MEM_FILTER, MEM_MAP]
  >- (`?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = a` by
        (drule phi_pair_label_mem >> simp[MEM_MAP] >> metis_tac[]) >>
      metis_tac[]) >>
  `~(?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = a)` by
    (drule phi_pair_label_mem >> simp[MEM_MAP] >> metis_tac[]) >>
  eq_tac
  >- (rpt strip_tac >> gvs[] >> Cases_on `FST p' = b` >> gvs[]
      >- (disj2_tac >> qexists `p'` >> simp[]) >>
      disj1_tac >> qexists `p'` >> simp[]) >>
  rpt strip_tac >>
  qexists `(if FST p = b then a else FST p, SND p)` >>
  (conj_tac >- (qexists `p` >> simp[]) >> simp[])
QED

Theorem do_merge_jump_surviving_edge:
  wf_function fn /\ EVERY label_positions_ok (fn_insts fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ bb_succs b = [target] /\
  lbl <> b.bb_label ==>
  (fn_cfg_edge fn' pred lbl <=>
    (pred <> b.bb_label /\ fn_cfg_edge fn pred lbl) \/
    (pred = a.bb_label /\ lbl = target))
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_labels_distinct] >>
  `fn_cfg_edge fn a.bb_label b.bb_label` by metis_tac[can_bypass_jump_edge] >>
  `fn_cfg_edge fn' pred lbl <=> pred <> b.bb_label /\
   if pred = a.bb_label then
     ?src. fn_cfg_edge fn pred src /\ lbl = (if src = b.bb_label then target else src)
   else fn_cfg_edge fn pred lbl` by
    (irule do_merge_jump_edge_sources >> metis_tac[]) >>
  asm_rewrite_tac[] >> Cases_on `pred = a.bb_label` >> simp[] >>
  eq_tac
  >- (strip_tac >> Cases_on `src = b.bb_label` >> gvs[]) >>
  strip_tac >- (qexists `lbl` >> simp[]) >>
  qexists `b.bb_label` >> simp[]
QED

Theorem do_merge_jump_phi_coverage:
  wf_ssa fn /\ wf_function fn /\ EVERY label_positions_ok (fn_insts fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ MEM bb' fn'.fn_blocks /\
  MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI ==>
  (fn_cfg_edge fn' pred bb'.bb_label <=>
   ?p. MEM p (phi_pairs phi.inst_operands) /\ FST p = pred)
Proof
  strip_tac >> drule_all do_merge_jump_phi_source_exact >> strip_tac >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_labels_distinct] >>
  `MEM b fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `phi_edge_uses_wf fn bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands /\
   (!p. fn_cfg_edge fn p bb.bb_label <=>
     ?pair. MEM pair (phi_pairs inst.inst_operands) /\ FST pair = p)` by
    fs[phi_edge_uses_wf_def] >>
  `fn_cfg_edge fn b.bb_label bb.bb_label <=> bb.bb_label = target` by
    (simp[NoAsms, fn_cfg_edge_def] >> eq_tac
     >- (strip_tac >>
         `bb'' = b` by metis_tac[same_label_same_block] >> gvs[]) >>
     strip_tac >> qexists `b` >> simp[]) >>
  `fn_cfg_edge fn' pred bb.bb_label <=>
     (pred <> b.bb_label /\ fn_cfg_edge fn pred bb.bb_label) \/
     (pred = a.bb_label /\ bb.bb_label = target)` by
    (irule do_merge_jump_surviving_edge >> metis_tac[]) >>
  Cases_on `bb.bb_label = target`
  >- (gvs[] >> simp[update_phi_bypass_pred] >> metis_tac[]) >>
  gvs[] >> metis_tac[]
QED

Theorem do_merge_jump_phi_shape:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  !bb inst. MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands /\
    ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
    (!pred. fn_cfg_edge fn' pred bb.bb_label <=>
      ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred)
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `fn_inst_wf fn'` by (irule do_merge_jump_fn_inst_wf >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (`inst_wf inst` by metis_tac[fn_inst_wf_def] >> gvs[inst_wf_def]) >>
  conj_tac
  >- (irule do_merge_jump_phi_distinct >> metis_tac[]) >>
  gen_tac >> irule do_merge_jump_phi_coverage >> metis_tac[]
QED

Theorem do_merge_jump_edge_simulation:
  wf_function fn /\ EVERY label_positions_ok (fn_insts fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ bb_succs b = [target] /\
  fn_cfg_edge fn src dst ==>
  (if src = b.bb_label then a.bb_label else src) =
    (if dst = b.bb_label then a.bb_label else dst) \/
  fn_cfg_edge fn' (if src = b.bb_label then a.bb_label else src)
    (if dst = b.bb_label then a.bb_label else dst)
Proof
  strip_tac >>
  `MEM a fn.fn_blocks /\ MEM b fn.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `a.bb_label <> b.bb_label` by metis_tac[can_bypass_jump_labels_distinct] >>
  `b.bb_label <> target` by
    (irule can_bypass_jump_target_distinct >> metis_tac[wf_function_def]) >>
  Cases_on `dst = b.bb_label`
  >- (`src = a.bb_label` by
        (fs[fn_cfg_edge_def] >>
         `bb = a` by metis_tac[can_bypass_jump_unique_pred] >> gvs[]) >> simp[]) >>
  disj2_tac >> simp[] >>
  Cases_on `src = b.bb_label`
  >- (`dst = target` by
        (fs[fn_cfg_edge_def] >>
         `bb = b` by metis_tac[same_label_same_block] >> gvs[]) >>
      simp[] >> irule (iffRL do_merge_jump_surviving_edge) >> metis_tac[]) >>
  simp[] >> irule (iffRL do_merge_jump_surviving_edge) >> metis_tac[]
QED

Theorem do_merge_jump_all_reachable:
  wf_function fn /\ first_block_no_preds fn /\ all_reachable fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==> all_reachable fn'
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `?target. bb_succs b = [target]` by
    (fs[can_bypass_jump_def, num_succs_def] >>
     Cases_on `bb_succs b` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `ALL_DISTINCT (fn_labels fn') /\ fn_has_entry fn'` by
    (irule do_merge_jump_labels_entry >> metis_tac[]) >>
  `fn.fn_blocks <> [] /\ fn'.fn_blocks <> []` by
    fs[wf_function_def, fn_has_entry_def] >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (irule do_merge_jump_entry_label >> metis_tac[]) >>
  `(HD fn.fn_blocks).bb_label <> b.bb_label` by
    (fs[first_block_no_preds_def, EVERY_MEM, can_bypass_jump_def] >>
     qpat_x_assum `!bb. _` (qspec_then `a` mp_tac) >> simp[] >> metis_tac[]) >>
  `!x y. RTC (fn_cfg_edge fn) x y ==>
    RTC (fn_cfg_edge fn') (if x = b.bb_label then a.bb_label else x)
      (if y = b.bb_label then a.bb_label else y)` by
    (ho_match_mp_tac rtc_map_simulation >> rpt strip_tac >>
     irule do_merge_jump_edge_simulation >> metis_tac[]) >>
  simp[all_reachable_def] >> qx_gen_tac `bb` >> strip_tac >>
  `MEM bb.bb_label (fn_labels fn')` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM bb.bb_label (fn_labels fn) /\ bb.bb_label <> b.bb_label` by
    (drule do_merge_jump_fn_labels >> strip_tac >> fs[MEM_FILTER]) >>
  `fn_reachable fn bb.bb_label` by
    (fs[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `fn_entry_label fn' = fn_entry_label fn` by
    (Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def]) >>
  gvs[fn_reachable_def] >>
  `entry = (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
  first_x_assum (qspecl_then [`entry`, `bb.bb_label`] mp_tac) >> simp[]
QED

Theorem update_phi_bypass_label_positions_ok:
  label_positions_ok inst ==> label_positions_ok (update_phi_bypass a b inst)
Proof
  Cases_on `inst.inst_opcode = PHI` >> simp[update_phi_bypass_def] >>
  Cases_on `MEM (Label a) inst.inst_operands` >> simp[label_positions_ok_def]
QED

Theorem canon_jnz_inst_label_positions_ok:
  label_positions_ok inst ==> label_positions_ok (canon_jnz_inst inst)
Proof
  Cases_on `inst.inst_opcode = JNZ`
  >- (Cases_on `inst.inst_operands` >> simp[canon_jnz_inst_def] >>
      Cases_on `t` >> simp[canon_jnz_inst_def] >>
      Cases_on `t'` >> simp[canon_jnz_inst_def] >>
      Cases_on `t` >> simp[canon_jnz_inst_def] >>
      IF_CASES_TAC >> simp[] >> gvs[] >>
      Cases_on `h'` >>
      gvs[label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def]) >>
  simp[canon_jnz_inst_def] >> rpt strip_tac >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem do_merge_jump_label_positions_ok:
  EVERY label_positions_ok (fn_insts fn) /\ MEM a fn.fn_blocks /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  EVERY label_positions_ok (fn_insts fn')
Proof
  strip_tac >>
  `EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn.fn_blocks` by
    (fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]) >>
  `EVERY (\bb. EVERY label_positions_ok bb.bb_instructions) fn'.fn_blocks` by
    (irule do_merge_jump_every_inst >> qexistsl [`a`, `b`, `fn`, `lm`, `lm'`] >>
     simp[update_phi_bypass_label_positions_ok] >> rpt strip_tac >>
     irule bypass_source_label_positions_ok >> simp[]) >>
  fs[EVERY_MEM, fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]
QED

Theorem do_merge_jump_entry_no_phis:
  wf_function fn /\ first_block_no_preds fn /\ scfg_phi_safe fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\
  can_bypass_jump fn a b /\ do_merge_jump fn a b lm = SOME (fn',lm') ==>
  EVERY (\inst. inst.inst_opcode <> PHI) (HD fn'.fn_blocks).bb_instructions
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `fn.fn_blocks <> []` by fs[wf_function_def, fn_has_entry_def] >>
  `(HD fn'.fn_blocks).bb_label = (HD fn.fn_blocks).bb_label` by
    (irule do_merge_jump_entry_label >> metis_tac[]) >>
  `fn'.fn_blocks <> []` by
    (`fn_has_entry fn'` by metis_tac[do_merge_jump_labels_entry] >>
     fs[fn_has_entry_def]) >>
  simp[EVERY_MEM] >> qx_gen_tac `phi` >> strip_tac >> strip_tac >>
  `MEM (HD fn'.fn_blocks) fn'.fn_blocks` by
    (Cases_on `fn'.fn_blocks` >> gvs[]) >>
  drule_all do_merge_jump_phi_source_exact >> strip_tac >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `bb = HD fn.fn_blocks` by metis_tac[same_label_same_block] >>
  drule scfg_phi_safe_entry >> disch_then assume_tac >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem do_merge_jump_ssa_invariant:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) /\ all_reachable fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  wf_ssa fn' /\ wf_function fn' /\ fn_inst_wf fn' /\ first_block_no_preds fn' /\
  scfg_phi_safe fn' /\ fn_defs_reach_uses fn' /\
  EVERY label_positions_ok (fn_insts fn') /\ all_reachable fn'
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `wf_function fn'` by (irule do_merge_jump_wf >> metis_tac[]) >>
  `fn_inst_wf fn'` by (irule do_merge_jump_fn_inst_wf >> metis_tac[]) >>
  `first_block_no_preds fn'` by
    (irule do_merge_jump_first_block_no_preds >> metis_tac[]) >>
  `all_reachable fn'` by (irule do_merge_jump_all_reachable >> metis_tac[]) >>
  `ssa_form fn'` by (irule do_merge_jump_ssa >> metis_tac[wf_ssa_def]) >>
  `scfg_phi_preds fn` by metis_tac[wf_ssa_phi_preds] >>
  `fn_defs_reach_uses fn'` by (irule do_merge_jump_defs_reach_uses >> metis_tac[]) >>
  `wf_ssa fn'` by
    (irule reachable_defs_reach_uses_wf_ssa >> simp[] >>
     rpt gen_tac >> strip_tac >> irule do_merge_jump_phi_shape >>
     metis_tac[]) >>
  `scfg_phi_safe fn'` by
    (irule wf_ssa_phi_safe >> conj_tac >- asm_rewrite_tac[] >>
     irule do_merge_jump_entry_no_phis >> metis_tac[]) >>
  `EVERY label_positions_ok (fn_insts fn')` by
    (drule_all do_merge_jump_label_positions_ok >> simp[]) >> simp[]
QED

Theorem try_bypass_ssa_invariant:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) /\ all_reachable fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  try_bypass fn lm a succs = (fn',lm',changed) ==>
  wf_ssa fn' /\ wf_function fn' /\ fn_inst_wf fn' /\ first_block_no_preds fn' /\
  scfg_phi_safe fn' /\ fn_defs_reach_uses fn' /\
  EVERY label_positions_ok (fn_insts fn') /\ all_reachable fn'
Proof
  qid_spec_tac `changed` >> qid_spec_tac `lm'` >> qid_spec_tac `fn'` >>
  Induct_on `succs` >- simp[try_bypass_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[Once try_bypass_def, AllCaseEqs()]
  >~ [`do_merge_jump _ _ _ _ = SOME _`]
  >- (irule do_merge_jump_ssa_invariant >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[lookup_block_member_label]) >>
  first_x_assum irule >> simp[]
QED

Theorem collapse_ssa_invariant_joint:
  (!fn lm visited lbl.
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
    scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
    EVERY label_positions_ok (fn_insts fn) /\ all_reachable fn ==>
    wf_ssa (FST (collapse_dfs fn lm visited lbl)) /\
    wf_function (FST (collapse_dfs fn lm visited lbl)) /\
    fn_inst_wf (FST (collapse_dfs fn lm visited lbl)) /\
    first_block_no_preds (FST (collapse_dfs fn lm visited lbl)) /\
    scfg_phi_safe (FST (collapse_dfs fn lm visited lbl)) /\
    fn_defs_reach_uses (FST (collapse_dfs fn lm visited lbl)) /\
    EVERY label_positions_ok (fn_insts (FST (collapse_dfs fn lm visited lbl))) /\
    all_reachable (FST (collapse_dfs fn lm visited lbl))) /\
  (!fn lm visited succs.
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
    scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
    EVERY label_positions_ok (fn_insts fn) /\ all_reachable fn ==>
    wf_ssa (FST (collapse_dfs_succs fn lm visited succs)) /\
    wf_function (FST (collapse_dfs_succs fn lm visited succs)) /\
    fn_inst_wf (FST (collapse_dfs_succs fn lm visited succs)) /\
    first_block_no_preds (FST (collapse_dfs_succs fn lm visited succs)) /\
    scfg_phi_safe (FST (collapse_dfs_succs fn lm visited succs)) /\
    fn_defs_reach_uses (FST (collapse_dfs_succs fn lm visited succs)) /\
    EVERY label_positions_ok (fn_insts (FST (collapse_dfs_succs fn lm visited succs))) /\
    all_reachable (FST (collapse_dfs_succs fn lm visited succs)))
Proof
  ho_match_mp_tac collapse_property_joint >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule chain_merge_ssa_invariant >>
      simp[] >> qexistsl [`a`, `b`, `fn`] >> simp[] >>
      metis_tac[lookup_block_member_label]) >>
  rpt gen_tac >> strip_tac >> irule try_bypass_ssa_invariant >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem block_label_operand_live:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ is_block_label_opcode inst.inst_opcode /\
  MEM (Label lbl) inst.inst_operands ==> MEM lbl (fn_labels fn)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (`phi_edge_uses_wf fn bb inst` by
        (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
      `MEM lbl (MAP FST (phi_pairs inst.inst_operands))` by
        metis_tac[phi_edge_uses_wf_def, phi_pair_label_mem] >>
      fs[phi_edge_uses_wf_def, MEM_MAP] >>
      `fn_cfg_edge fn lbl bb.bb_label` by metis_tac[] >>
      fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `is_terminator inst.inst_opcode` by fs[is_block_label_opcode_def] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `inst = LAST bb.bb_instructions` by metis_tac[bb_well_formed_terminator_last] >>
  `MEM lbl (bb_succs bb)` by
    (Cases_on `bb.bb_instructions` >> fs[bb_well_formed_def, bb_succs_def,
      get_successors_mem_label] >> metis_tac[]) >>
  fs[wf_function_def, fn_succs_closed_def] >> metis_tac[]
QED

Theorem subst_block_labels_inst_absent:
  (!l. MEM (Label l) inst.inst_operands ==> ~MEM l (MAP FST lm)) ==>
  subst_block_labels_inst lm inst = inst
Proof
  strip_tac >>
  `MAP (subst_label_map_op lm) inst.inst_operands = inst.inst_operands` by
    (GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
     irule MAP_CONG >> simp[] >> rpt strip_tac >>
     irule subst_label_map_op_absent >> metis_tac[]) >>
  simp[subst_block_labels_inst_def, subst_label_map_inst_def]
QED

Theorem subst_block_labels_fn_absent:
  wf_ssa fn /\ wf_function fn /\
  EVERY (\entry. ~MEM (FST entry) (fn_labels fn)) lm ==>
  subst_block_labels_fn lm fn = fn
Proof
  strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==> subst_block_labels_block lm bb = bb` by
    (rpt strip_tac >>
     `MAP (subst_block_labels_inst lm) bb.bb_instructions = bb.bb_instructions` by
       (GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
        irule MAP_CONG >> simp[] >> qx_gen_tac `inst` >> strip_tac >>
        Cases_on `is_block_label_opcode inst.inst_opcode`
        >- (irule subst_block_labels_inst_absent >> rpt strip_tac >>
            `MEM l (fn_labels fn)` by (irule block_label_operand_live >> metis_tac[]) >>
            fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
        simp[subst_block_labels_inst_def]) >>
     simp[subst_block_labels_block_def]) >>
  `MAP (subst_block_labels_block lm) fn.fn_blocks = fn.fn_blocks` by
    (GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
     irule MAP_CONG >> simp[]) >>
  simp[subst_block_labels_fn_def]
QED

Theorem collapse_dfs_sources_absent:
  ALL_DISTINCT (fn_labels fn) /\
  collapse_dfs fn [] visited lbl = (fn',lm',visited') ==>
  EVERY (\entry. ~MEM (FST entry) (fn_labels fn')) lm'
Proof
  strip_tac >>
  qspecl_then [`fn`, `[]`, `visited`, `lbl`] mp_tac (cj 1 collapse_events_joint) >>
  simp[collapse_dfs_result_def, collapse_result_events_def, fn_result_events_def] >>
  strip_tac >> gvs[] >> simp[EVERY_REVERSE] >>
  irule label_event_trace_sources_absent >> metis_tac[]
QED

Theorem collapse_dfs_subst_identity:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) /\ all_reachable fn /\
  collapse_dfs fn [] visited lbl = (fn',lm',visited') ==>
  subst_block_labels_fn lm' fn' = fn'
Proof
  strip_tac >>
  qspecl_then [`fn`, `[]`, `visited`, `lbl`] mp_tac
    (cj 1 collapse_ssa_invariant_joint) >> simp[] >> strip_tac >>
  irule subst_block_labels_fn_absent >> simp[] >>
  irule collapse_dfs_sources_absent >> goal_assum (drule_at Any) >>
  fs[wf_function_def]
QED

Theorem simplify_cfg_round_ssa_invariant:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) ==>
  wf_ssa (FST (simplify_cfg_round_with_labels fn)) /\
  wf_function (FST (simplify_cfg_round_with_labels fn)) /\
  fn_inst_wf (FST (simplify_cfg_round_with_labels fn)) /\
  first_block_no_preds (FST (simplify_cfg_round_with_labels fn)) /\
  scfg_phi_safe (FST (simplify_cfg_round_with_labels fn)) /\
  fn_defs_reach_uses (FST (simplify_cfg_round_with_labels fn)) /\
  EVERY label_positions_ok (fn_insts (FST (simplify_cfg_round_with_labels fn)))
Proof
  strip_tac >> Cases_on `fn_entry_label fn`
  >- simp[simplify_cfg_round_with_labels_def] >>
  drule_all simplify_cfg_round_entry_ssa_invariant >> strip_tac >>
  qabbrev_tac `start = fix_all_phis (remove_unreachable_blocks fn)` >>
  Cases_on `collapse_dfs start [] [] x` >> PairCases_on `r` >>
  `wf_ssa q /\ wf_function q /\ fn_inst_wf q /\ first_block_no_preds q /\
   scfg_phi_safe q /\ fn_defs_reach_uses q /\
   EVERY label_positions_ok (fn_insts q) /\ all_reachable q` by
    (qspecl_then [`start`, `[]`, `[]`, `x`] mp_tac
      (cj 1 collapse_ssa_invariant_joint) >> simp[]) >>
  `subst_block_labels_fn r0 q = q` by
    (drule_at (Pat `collapse_dfs _ _ _ _ = _`) collapse_dfs_subst_identity >> simp[]) >>
  drule_all simplify_cfg_round_entry_ssa_invariant >> strip_tac >>
  fs[Abbr `start`] >> simp[simplify_cfg_round_with_labels_def]
QED

Theorem simplify_cfg_iter_ssa_invariant:
  !fuel fn.
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) ==>
  wf_ssa (FST (simplify_cfg_iter_with_labels fuel fn)) /\
  wf_function (FST (simplify_cfg_iter_with_labels fuel fn)) /\
  fn_inst_wf (FST (simplify_cfg_iter_with_labels fuel fn)) /\
  first_block_no_preds (FST (simplify_cfg_iter_with_labels fuel fn)) /\
  scfg_phi_safe (FST (simplify_cfg_iter_with_labels fuel fn)) /\
  fn_defs_reach_uses (FST (simplify_cfg_iter_with_labels fuel fn)) /\
  EVERY label_positions_ok (fn_insts (FST (simplify_cfg_iter_with_labels fuel fn)))
Proof
  Induct_on `fuel` >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all simplify_cfg_round_ssa_invariant >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels fn` >> gvs[] >>
  simp[simplify_cfg_iter_with_labels_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `simplify_cfg_iter_with_labels fuel q` >> simp[] >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED

Theorem simplify_cfg_fn_ssa_invariant:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  EVERY label_positions_ok (fn_insts fn) ==>
  wf_ssa (simplify_cfg_fn fn)
Proof
  strip_tac >> simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def] >>
  drule_all simplify_cfg_iter_ssa_invariant >> simp[]
QED
