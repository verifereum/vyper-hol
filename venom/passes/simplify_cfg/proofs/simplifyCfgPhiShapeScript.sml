(* PHI predecessor and local-reference interfaces for SimplifyCFG. *)
Theory simplifyCfgPhiShape
Ancestors
  simplifyCfgShape simplifyCfgGraphShape simplifyCfgDefs cfgTransform
  venomWf venomInst list rich_list

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
