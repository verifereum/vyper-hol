(* PHI predecessor and local-reference interfaces for SimplifyCFG. *)
Theory simplifyCfgPhiShape
Ancestors
  simplifyCfgShape simplifyCfgGraphShape simplifyCfgDefs cfgTransform
  venomWf venomInst cfgTransformProps list rich_list

Theorem filter_phi_ops_label:
  !ops ps l. phi_well_formed ops ==>
  (MEM (Label l) (filter_phi_ops ps ops) <=>
   MEM (Label l) ops /\ MEM l ps)
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[filter_phi_ops_def, phi_well_formed_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem remove_phi_label_label:
  !ops b l. phi_well_formed ops ==>
  (MEM (Label l) (remove_phi_label b ops) <=>
   MEM (Label l) ops /\ l <> b)
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[remove_phi_label_def, phi_well_formed_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem update_phi_bypass_label:
  i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\ a <> b ==>
  (MEM (Label l) (update_phi_bypass a b i).inst_operands <=>
   if MEM (Label a) i.inst_operands then
     MEM (Label l) i.inst_operands /\ l <> b
   else ?k. MEM (Label k) i.inst_operands /\
             l = (if k = b then a else k))
Proof
  strip_tac >> simp[update_phi_bypass_def] >> IF_CASES_TAC >>
  simp[remove_phi_label_label, MEM_MAP] >>
  eq_tac >> rpt strip_tac
  >- (Cases_on `op` >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  qexists_tac `Label k` >> Cases_on `k = b` >> simp[]
QED

Theorem fix_all_phis_graph:
  EVERY (\bb. bb_well_formed bb) f.fn_blocks ==>
  MAP (\bb. (bb.bb_label, bb_succs bb)) (fix_all_phis f).fn_blocks =
  MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks
Proof
  strip_tac >> simp[fix_all_phis_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  rename1 `MEM bb f.fn_blocks` >>
  `bb_well_formed bb` by gvs[EVERY_MEM] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++
    [LAST bb.bb_instructions]` by
    metis_tac[bb_well_formed_def, APPEND_FRONT_LAST] >>
  metis_tac[fix_phis_in_block_cfg, bb_well_formed_def]
QED

Theorem block_graph_pred_labels:
  MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks =
    MAP (\bb. (bb.bb_label, bb_succs bb)) g.fn_blocks ==>
  pred_labels f lbl = pred_labels g lbl
Proof
  strip_tac >>
  `MAP FST (FILTER (\p. MEM lbl (SND p))
      (MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks)) =
   MAP FST (FILTER (\p. MEM lbl (SND p))
      (MAP (\bb. (bb.bb_label, bb_succs bb)) g.fn_blocks))` by
    asm_rewrite_tac[] >>
  gvs[pred_labels_def, block_preds_def, FILTER_MAP, MAP_MAP_o,
      combinTheory.o_DEF]
QED

Theorem fix_phi_inst_phi_label:
  inst_wf i /\ (fix_phi_inst ps i).inst_opcode = PHI /\
  MEM (Label l) (fix_phi_inst ps i).inst_operands ==>
  i.inst_opcode = PHI /\ MEM l ps
Proof
  Cases_on `i.inst_opcode = PHI`
  >- (strip_tac >> `phi_well_formed i.inst_operands` by gvs[inst_wf_def] >>
      qpat_x_assum `MEM (Label l) _` mp_tac >>
      qpat_x_assum `(fix_phi_inst ps i).inst_opcode = PHI` mp_tac >>
      simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops ps i.inst_operands` >> simp[] >>
      rename1 `h::rest` >> Cases_on `rest` >> simp[]
      >- metis_tac[filter_phi_ops_label, MEM] >>
      rename1 `h::h'::rest` >> Cases_on `rest` >> simp[] >>
      metis_tac[filter_phi_ops_label, MEM]) >>
  simp[fix_phi_inst_def]
QED

Theorem fix_all_phis_phi_preds:
  EVERY (\bb. bb_well_formed bb) f.fn_blocks /\
  EVERY inst_wf (fn_insts f) ==>
  !bb i l. MEM bb (fix_all_phis f).fn_blocks /\
    MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
    MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels (fix_all_phis f) bb.bb_label)
Proof
  strip_tac >>
  `!lbl. pred_labels (fix_all_phis f) lbl = pred_labels f lbl` by
    (gen_tac >> irule block_graph_pred_labels >> simp[fix_all_phis_graph]) >>
  simp[fix_all_phis_def, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  rename1 `MEM old f.fn_blocks` >>
  qpat_x_assum `MEM i _` mp_tac >>
  simp[fix_phis_in_block_def, MEM_FILTER, MEM_MAP] >> strip_tac >> gvs[] >>
  rename1 `MEM orig old.bb_instructions` >>
  `inst_wf orig` by
    (drule_all ctxLookupAgreeHelpersTheory.EVERY_fn_block >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  drule_all fix_phi_inst_phi_label >> simp[fix_phis_in_block_def]
QED

Theorem pred_labels_mem:
  MEM l (pred_labels f x) <=>
  ?bb. MEM bb f.fn_blocks /\ bb.bb_label = l /\ MEM x (bb_succs bb)
Proof
  simp[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem chain_merge_pred_labels:
  ALL_DISTINCT (fn_labels f) /\
  EVERY (\bb. bb_well_formed bb) f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_merge_blocks f a b /\
  g = f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks))
      (bb_succs (merge_blocks a b)) /\
  MEM x (fn_labels g) /\ MEM l (pred_labels f x) ==>
  MEM (if l = b.bb_label then a.bb_label else l) (pred_labels g x)
Proof
  strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `b.bb_instructions <> []` by
    gvs[EVERY_MEM, bb_well_formed_def] >>
  `a.bb_label <> b.bb_label` by gvs[can_merge_blocks_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label f.fn_blocks)))` by
    (simp[fn_labels_replace_block, merge_blocks_def] >>
     irule ALL_DISTINCT_remove_block >> gvs[fn_labels_def]) >>
  `!lbl. pred_labels g lbl = pred_labels
    (f with fn_blocks := replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label f.fn_blocks)) lbl` by
    (gen_tac >> irule block_graph_pred_labels >>
     simp[update_succ_phi_labels_graph]) >>
  `x <> b.bb_label` by
    (gvs[fn_labels_def, update_succ_phi_labels_labels,
         fn_labels_replace_block, merge_blocks_def,
         fn_labels_remove_block, MEM_FILTER]) >>
  qpat_x_assum `MEM l (pred_labels f x)`
    (strip_assume_tac o REWRITE_RULE [pred_labels_mem]) >>
  rename1 `MEM src f.fn_blocks` >>
  `src.bb_label = a.bb_label ==> src = a` by
    (strip_tac >> `lookup_block src.bb_label f.fn_blocks = SOME src` by
      (irule venomExecPropsTheory.MEM_lookup_block >> gvs[fn_labels_def]) >>
     gvs[]) >>
  `src.bb_label = b.bb_label ==> src = b` by
    (strip_tac >> `lookup_block src.bb_label f.fn_blocks = SOME src` by
      (irule venomExecPropsTheory.MEM_lookup_block >> gvs[fn_labels_def]) >>
     gvs[]) >>
  qpat_x_assum `!lbl. pred_labels g lbl = _`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `g = _` kall_tac >>
  simp[pred_labels_mem, replace_block_def, remove_block_def,
       MEM_MAP, MEM_FILTER] >>
  Cases_on `src.bb_label = b.bb_label`
  >- (gvs[] >> qexists_tac `merge_blocks a b` >>
      simp[merge_blocks_succs, merge_blocks_def, MEM_MAP, MEM_FILTER] >>
      metis_tac[]) >>
  Cases_on `src.bb_label = a.bb_label`
  >- gvs[can_merge_blocks_def] >>
  qexists_tac `src` >> simp[] >> conj_tac
  >- (qexists_tac `src` >> simp[]) >> metis_tac[]
QED
