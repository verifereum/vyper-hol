Theory simplifyCfgBypassDataflow
Ancestors
  list venomInst venomWf cfgTransform simplifyCfgDefs simplifyCfgLabelProps
  simplifyCfgStruct simplifyCfgPhiRepair simplifyCfgPhiPreds simplifyCfgDataflow
  simplifyCfgChainDataflow venomExecProofs rich_list

Theorem phi_pairs_remove_phi_label:
  !ops. phi_well_formed ops ==>
  phi_pairs (remove_phi_label lbl ops) =
    FILTER (\p. FST p <> lbl) (phi_pairs ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, remove_phi_label_def, phi_pairs_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_pairs_def]
QED

Theorem phi_pairs_subst_label_ops:
  !ops. phi_well_formed ops ==>
  phi_pairs (MAP (subst_label_op old new) ops) =
    MAP (\p. (if FST p = old then new else FST p, SND p)) (phi_pairs ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, subst_label_op_def, phi_pairs_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_pairs_def]
QED

Theorem update_phi_bypass_pair_origin:
  phi_well_formed inst.inst_operands /\ inst.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs (update_phi_bypass a b inst).inst_operands) ==>
  ?q. MEM (q,v) (phi_pairs inst.inst_operands) /\
      p = (if q = b then a else q)
Proof
  strip_tac >>
  Cases_on `MEM (Label a) inst.inst_operands`
  >- (gvs[update_phi_bypass_def, phi_pairs_remove_phi_label, MEM_FILTER] >>
      qexists `p` >> simp[]) >>
  `MAP (\op. case op of Label l => if l = b then Label a else Label l | _ => op)
       inst.inst_operands = MAP (subst_label_op b a) inst.inst_operands` by
    (AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> Cases >> simp[subst_label_op_def]) >>
  gvs[update_phi_bypass_def, phi_pairs_subst_label_ops, MEM_MAP] >>
  qexists `FST p'` >> simp[]
QED

Theorem update_phi_bypass_non_phi:
  inst.inst_opcode <> PHI ==> update_phi_bypass a b inst = inst
Proof
  simp[update_phi_bypass_def]
QED

Theorem subst_label_inst_use_source:
  MEM (Var v) (subst_label_inst old new inst).inst_operands ==>
  MEM (Var v) inst.inst_operands
Proof
  simp[subst_label_inst_def, MEM_MAP] >> rpt strip_tac >>
  Cases_on `y` >> gvs[subst_label_op_def, AllCaseEqs()]
QED

Theorem inst_wf_update_phi_bypass:
  inst_wf inst ==> inst_wf (update_phi_bypass a b inst)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (`phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
      `phi_well_formed (update_phi_bypass a b inst).inst_operands` by
        metis_tac[update_phi_bypass_phi_operands, update_phi_bypass_shape] >>
      gvs[inst_wf_def, update_phi_bypass_shape]) >>
  simp[update_phi_bypass_non_phi]
QED

Theorem do_merge_jump_block_map:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ MEM bb' fn'.fn_blocks ==>
  ?bb target. MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
    bb_succs b = [target] /\
    bb'.bb_label = bb.bb_label /\
    bb'.bb_instructions =
      MAP (\inst.
        if bb.bb_label = a.bb_label then
          (if target = a.bb_label then update_phi_bypass a.bb_label b.bb_label
           else I)
            (if ~is_terminator inst.inst_opcode then inst
             else canon_jnz_inst (subst_label_inst b.bb_label target inst))
        else if bb.bb_label = target then update_phi_bypass a.bb_label b.bb_label inst
        else inst) bb.bb_instructions
Proof
  strip_tac >> fs[do_merge_jump_def, AllCaseEqs()] >>
  drule lookup_block_member_label >> strip_tac >> gvs[] >>
  fs[replace_block_def, MEM_MAP, remove_block_def, MEM_FILTER] >>
  rename1 `src.bb_label <> b.bb_label` >>
  `lookup_block src.bb_label fn.fn_blocks = SOME src` by
    (irule venomExecPropsTheory.MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  qexists `src` >>
  Cases_on `src.bb_label = a.bb_label` >>
  Cases_on `src.bb_label = target.bb_label` >> gvs[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, combinTheory.I_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem do_merge_jump_index_source:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ MEM bb' fn'.fn_blocks ==>
  ?bb. MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
    bb'.bb_label = bb.bb_label /\
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    !i. i < LENGTH bb.bb_instructions ==>
      (EL i bb'.bb_instructions).inst_outputs = (EL i bb.bb_instructions).inst_outputs /\
      ((EL i bb'.bb_instructions).inst_opcode = PHI <=>
       (EL i bb.bb_instructions).inst_opcode = PHI) /\
      (!v. MEM (Var v) (EL i bb'.bb_instructions).inst_operands /\
           (EL i bb'.bb_instructions).inst_opcode <> PHI ==>
           MEM (Var v) (EL i bb.bb_instructions).inst_operands)
Proof
  strip_tac >> drule_all do_merge_jump_block_map >>
  disch_then (qx_choose_then `bb` (qx_choose_then `target` strip_assume_tac)) >>
  qexists `bb` >> simp[] >> gen_tac >> strip_tac >>
  simp[EL_MAP] >>
  rpt IF_CASES_TAC >>
  simp[update_phi_bypass_shape, canon_jnz_inst_shape, subst_label_inst_shape,
    combinTheory.I_DEF] >>
  rpt strip_tac >>
  gvs[update_phi_bypass_shape, canon_jnz_inst_shape, subst_label_inst_shape,
    is_terminator_def, update_phi_bypass_non_phi] >>
  metis_tac[canon_jnz_inst_var_subset, subst_label_inst_use_source]
QED

Theorem do_merge_jump_phi_pair_source:
  wf_function fn /\ fn_inst_wf fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\ MEM bb' fn'.fn_blocks /\
  MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs phi.inst_operands) ==>
  ?bb inst q target. MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
    bb'.bb_label = bb.bb_label /\ bb_succs b = [target] /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    MEM (q,v) (phi_pairs inst.inst_operands) /\
    p = (if bb.bb_label = target /\ q = b.bb_label then a.bb_label else q)
Proof
  strip_tac >> drule_all do_merge_jump_block_map >>
  disch_then (qx_choose_then `bb` (qx_choose_then `target` strip_assume_tac)) >>
  qpat_x_assum `MEM phi _` mp_tac >> simp[MEM_MAP] >>
  disch_then (qx_choose_then `inst` strip_assume_tac) >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `inst.inst_opcode = PHI` by
    (Cases_on `bb.bb_label = a.bb_label` >>
     Cases_on `bb.bb_label = target` >>
     Cases_on `target = a.bb_label` >>
     Cases_on `is_terminator inst.inst_opcode` >>
     gvs[update_phi_bypass_shape, canon_jnz_inst_shape, subst_label_inst_shape,
       combinTheory.I_DEF, is_terminator_def]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  qexistsl [`bb`, `inst`] >> simp[] >>
  Cases_on `bb.bb_label = target`
  >- (`phi = update_phi_bypass a.bb_label b.bb_label inst` by
        (Cases_on `bb.bb_label = a.bb_label` >> gvs[is_terminator_def]) >>
      gvs[] >> drule_all update_phi_bypass_pair_origin >> simp[]) >>
  `phi = inst` by
    (Cases_on `bb.bb_label = a.bb_label` >> gvs[is_terminator_def]) >>
  gvs[] >> qexists `p` >> simp[]
QED

Theorem do_merge_jump_output_block:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label ==>
  ?bb'. MEM bb' fn'.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    !i. i < LENGTH bb.bb_instructions ==>
      (EL i bb'.bb_instructions).inst_outputs = (EL i bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `MEM bb.bb_label (fn_labels fn')` by
    (drule_all do_merge_jump_fn_labels >>
     simp[fn_labels_def, MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  fs[fn_labels_def, MEM_MAP] >>
  rename1 `MEM out fn'.fn_blocks` >>
  drule_all do_merge_jump_index_source >>
  disch_then (qx_choose_then `src` strip_assume_tac) >>
  `lookup_block src.bb_label fn.fn_blocks = SOME src /\
   lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (conj_tac >> irule venomExecPropsTheory.MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def]) >>
  `src = bb` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `src = bb` SUBST_ALL_TAC >>
  qexists `out` >> simp[]
QED

Theorem bypassed_block_no_outputs:
  wf_function fn /\ fn_inst_wf fn /\ MEM b fn.fn_blocks /\
  can_bypass_jump fn a b /\ MEM inst b.bb_instructions ==>
  inst.inst_outputs = []
Proof
  strip_tac >>
  `bb_well_formed b /\ EVERY inst_wf b.bb_instructions /\
   LENGTH b.bb_instructions = 1` by
    (fs[wf_function_def, fn_inst_wf_def, can_bypass_jump_def, EVERY_MEM] >>
     metis_tac[]) >>
  `inst = LAST b.bb_instructions` by
    (Cases_on `b.bb_instructions` >> gvs[LENGTH_EQ_NUM_compute]) >>
  irule terminator_no_outputs >>
  fs[bb_well_formed_def, EVERY_MEM]
QED

Theorem do_merge_jump_output_witness:
  wf_function fn /\ fn_inst_wf fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
  ?bb' inst'. bb.bb_label <> b.bb_label /\
    MEM bb' fn'.fn_blocks /\ bb'.bb_label = bb.bb_label /\
    MEM inst' bb'.bb_instructions /\ MEM v inst'.inst_outputs
Proof
  strip_tac >>
  `bb.bb_label <> b.bb_label` by
    (strip_tac >>
     `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
       (irule venomExecPropsTheory.MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
     `bb = b` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `bb = b` SUBST_ALL_TAC >>
     `inst.inst_outputs = []` by
       (irule bypassed_block_no_outputs >> goal_assum (drule_at Any) >>
        simp[] >> metis_tac[lookup_block_member_label]) >>
     gvs[]) >>
  drule_all do_merge_jump_output_block >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_x_assum `MEM inst bb.bb_instructions`
    (qx_choose_then `i` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  `MEM (EL i out.bb_instructions) out.bb_instructions` by
    (simp[MEM_EL] >> qexists `i` >> simp[]) >>
  qexistsl [`out`, `EL i out.bb_instructions`] >> simp[] >>
  metis_tac[]
QED

Theorem do_merge_jump_endpoint_path_input:
  wf_function fn /\ lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  p <> [] /\ is_fn_path fn' p /\ MEM (LAST p) (fn_labels fn') /\
  LAST p = (if z = b.bb_label then a.bb_label else z) ==>
  ?q. is_fn_path fn q /\ q <> [] /\ HD q = HD p /\ LAST q = z /\
      !d. d <> b.bb_label /\ MEM d q ==> MEM d p
Proof
  strip_tac >>
  Cases_on `z = b.bb_label`
  >- (`LAST p = a.bb_label` by gvs[] >>
      drule_all do_merge_jump_path_input_last_b >>
      disch_then (qx_choose_then `q` strip_assume_tac) >>
      qexists `q` >> simp[] >> rpt strip_tac >>
      `MEM d (FRONT q)` by
        (qspec_then `q` mp_tac APPEND_FRONT_LAST >> simp[] >> metis_tac[MEM_APPEND, MEM]) >>
      `MEM d (FRONT p) \/ d = a.bb_label` by metis_tac[] >>
      qspec_then `p` mp_tac APPEND_FRONT_LAST >> simp[] >>
      metis_tac[MEM_APPEND, MEM]) >>
  drule_all do_merge_jump_path_input >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  qexists `q` >> simp[] >> rpt strip_tac >>
  metis_tac[bypass_path_surviving_member]
QED

Theorem do_merge_jump_entry:
  wf_function fn /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >>
  `MEM a fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `wf_function fn'` by metis_tac[do_merge_jump_wf] >>
  drule_all do_merge_jump_entry_label >>
  simp[fn_entry_label_def, entry_block_def] >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  gvs[wf_function_def, fn_has_entry_def] >>
  metis_tac[lookup_block_member_label]
QED

Theorem do_merge_jump_def_on_all_paths_endpoint:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb fn.fn_blocks /\ MEM bb' fn'.fn_blocks /\
  bb'.bb_label = (if bb.bb_label = b.bb_label then a.bb_label else bb.bb_label) /\
  def_on_all_paths fn bb NONE v ==>
  def_on_all_paths fn' bb' NONE v
Proof
  strip_tac >>
  `wf_function fn'` by metis_tac[do_merge_jump_wf] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[do_merge_jump_entry] >>
  drule_all def_on_all_paths_endpoint_witnesses >> strip_tac >>
  `!p. is_fn_path fn' p /\ p <> [] /\
    (?entry. fn_entry_label fn' = SOME entry /\ HD p = entry) /\
    LAST p = bb'.bb_label ==>
    ?db di. MEM db fn'.fn_blocks /\ MEM db.bb_label p /\
      MEM di db.bb_instructions /\ MEM v di.inst_outputs` suffices_by
    metis_tac[def_on_all_paths_endpoint_witnesses] >>
  rpt strip_tac >>
  `MEM (LAST p) (fn_labels fn')` by
    (simp[fn_labels_def, MEM_MAP] >> qexists `bb'` >> simp[]) >>
  `LAST p = (if bb.bb_label = b.bb_label then a.bb_label else bb.bb_label)` by
    metis_tac[] >>
  drule_all do_merge_jump_endpoint_path_input >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `?db di. MEM db fn.fn_blocks /\ MEM db.bb_label q /\
    MEM di db.bb_instructions /\ MEM v di.inst_outputs` by
    (qpat_x_assum `def_on_all_paths fn bb NONE v` mp_tac >>
     simp[def_on_all_paths_endpoint_witnesses] >>
     disch_then (qspec_then `q` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all do_merge_jump_output_witness >> strip_tac >>
  qexistsl [`bb''`, `inst'`] >> simp[]
QED

Theorem do_merge_jump_local_point_witness:
  LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
  (!i. i < LENGTH bb.bb_instructions ==>
    (EL i bb'.bb_instructions).inst_outputs = (EL i bb.bb_instructions).inst_outputs) /\
  j < LENGTH bb.bb_instructions /\
  (?i k. i < k /\ k < LENGTH bb.bb_instructions /\
    MEM v (EL i bb.bb_instructions).inst_outputs /\
    EL k bb.bb_instructions = EL j bb.bb_instructions) /\
  fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks ==>
  ?i. i < j /\ MEM v (EL i bb'.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `k = j` by
    metis_tac[inst_ids_el_eq] >>
  qexists `i` >> gvs[]
QED

Theorem do_merge_jump_def_on_all_paths_point:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb fn.fn_blocks /\ MEM bb' fn'.fn_blocks /\ bb'.bb_label = bb.bb_label /\
  LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
  (!i. i < LENGTH bb.bb_instructions ==>
    (EL i bb'.bb_instructions).inst_outputs = (EL i bb.bb_instructions).inst_outputs) /\
  j < LENGTH bb.bb_instructions /\
  def_on_all_paths fn bb (SOME (EL j bb.bb_instructions)) v ==>
  def_on_all_paths fn' bb' (SOME (EL j bb'.bb_instructions)) v
Proof
  strip_tac >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[do_merge_jump_entry] >>
  simp[def_on_all_paths_def] >> rpt strip_tac >>
  `MEM (LAST path) (fn_labels fn')` by
    (simp[fn_labels_def, MEM_MAP] >> qexists `bb'` >> simp[]) >>
  drule_all do_merge_jump_path_input >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  qpat_x_assum `def_on_all_paths fn bb _ v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `q` mp_tac) >> simp[] >> strip_tac
  >- (drule_all do_merge_jump_output_witness >> strip_tac >>
      disj1_tac >>
      `MEM def_bb.bb_label (FRONT q)` by
        (qpat_x_assum `!d. _` kall_tac >>
         simp[mem_front_index] >> qexists `k` >> simp[]) >>
      `MEM bb''.bb_label (FRONT path)` by metis_tac[] >>
      qpat_x_assum `MEM bb''.bb_label (FRONT path)` mp_tac >>
      simp[mem_front_index] >> disch_then (qx_choose_then `idx` strip_assume_tac) >>
      qexistsl [`idx`, `bb''`, `inst'`] >> simp[]) >>
  disj2_tac >>
  `?i. i < j /\ MEM v (EL i bb'.bb_instructions).inst_outputs` by
    (irule do_merge_jump_local_point_witness >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[wf_function_def]) >>
  qexists `i'` >> simp[] >> qexists `j` >> simp[]
QED

Theorem do_merge_jump_ordinary_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  fn_defs_reach_uses fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb' fn'.fn_blocks /\ MEM use bb'.bb_instructions /\
  use.inst_opcode <> PHI /\ MEM (Var v) use.inst_operands ==>
  def_on_all_paths fn' bb' (SOME use) v
Proof
  strip_tac >> drule_all do_merge_jump_index_source >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  qpat_x_assum `MEM use bb'.bb_instructions`
    (qx_choose_then `j` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  `j < LENGTH bb.bb_instructions` by metis_tac[] >>
  `(EL j bb.bb_instructions).inst_opcode <> PHI /\
   MEM (Var v) (EL j bb.bb_instructions).inst_operands` by metis_tac[] >>
  `def_on_all_paths fn bb (SOME (EL j bb.bb_instructions)) v` by
    (`MEM (EL j bb.bb_instructions) bb.bb_instructions` by
       (simp[MEM_EL] >> qexists `j` >> simp[]) >>
     qpat_x_assum `fn_defs_reach_uses fn` mp_tac >>
     simp[fn_defs_reach_uses_def] >>
     disch_then (qspecl_then [`bb`, `EL j bb.bb_instructions`] mp_tac) >> simp[]) >>
  qpat_x_assum `use = _` SUBST_ALL_TAC >>
  irule do_merge_jump_def_on_all_paths_point >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem do_merge_jump_phi_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  fn_defs_reach_uses fn /\ scfg_phi_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') /\
  MEM bb' fn'.fn_blocks /\ MEM phi bb'.bb_instructions /\ phi.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs phi.inst_operands) /\
  MEM pred' fn'.fn_blocks /\ pred'.bb_label = p ==>
  def_on_all_paths fn' pred' NONE v
Proof
  strip_tac >> drule_all do_merge_jump_phi_pair_source >>
  disch_then (qx_choose_then `bb` (qx_choose_then `inst`
    (qx_choose_then `q` (qx_choose_then `target` strip_assume_tac)))) >>
  `fn_cfg_edge fn q bb.bb_label` by metis_tac[scfg_phi_preds_edge] >>
  `?pred. MEM pred fn.fn_blocks /\ pred.bb_label = q` by
    (fs[fn_cfg_edge_def] >> metis_tac[]) >>
  `def_on_all_paths fn pred NONE v` by
    (qpat_x_assum `fn_defs_reach_uses fn` mp_tac >>
     simp[fn_defs_reach_uses_def] >>
     disch_then (qspecl_then [`bb`, `inst`] mp_tac) >> simp[] >>
     disch_then (qspec_then `pred` mp_tac) >> simp[]) >>
  `pred'.bb_label = (if pred.bb_label = b.bb_label then a.bb_label else pred.bb_label)` by
    (Cases_on `q = b.bb_label` >> simp[] >>
     `bb.bb_label = target` by
       (qpat_x_assum `fn_cfg_edge fn q bb.bb_label` mp_tac >>
        simp[fn_cfg_edge_def] >> rpt strip_tac >>
        `bb'' = b` by metis_tac[same_label_same_block, lookup_block_member_label] >>
        gvs[]) >> simp[]) >>
  irule do_merge_jump_def_on_all_paths_endpoint >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem do_merge_jump_defs_reach_uses:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  fn_defs_reach_uses fn /\ scfg_phi_preds fn /\
  lookup_block a.bb_label fn.fn_blocks = SOME a /\
  lookup_block b.bb_label fn.fn_blocks = SOME b /\ can_bypass_jump fn a b /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  fn_defs_reach_uses fn'
Proof
  strip_tac >> simp[fn_defs_reach_uses_def] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> rpt strip_tac
  >- (irule do_merge_jump_phi_defs_reach_uses >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule do_merge_jump_ordinary_defs_reach_uses >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
