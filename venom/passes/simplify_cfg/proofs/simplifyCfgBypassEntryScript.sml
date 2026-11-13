(* Simultaneous PHI snapshot transport for elementary jump bypass. *)
Theory simplifyCfgBypassEntry
Ancestors
  simplifyCfgBypassPhi simplifyCfgMergeEntry simplifyCfgControl
  simplifyCfgControlState simplifyCfgControlExec simplifyCfgDefs venomExecSemantics venomWf list
  simplifyCfgBypassPrecondition simplifyCfgBypassPhiClosure simplifyCfgBypassClosure
  simplifyCfgBypassPaths simplifyCfgBypassStatic simplifyCfgStaticInterface simplifyCfgBypassShape
  simplifyCfgPhiSemantics unitLabelMapIdentity cfgTransform venomExecProofs venomExecProps
  contextCodegenRel instIdxIndep
  simplifyCfgDataflow

Theorem scfg_update_phi_bypass_eval_one:
  bb_well_formed bb /\ phi_values_agree A B bb.bb_instructions /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  phi_well_formed i.inst_operands /\ A <> B /\ s.vs_prev_bb = SOME p /\
  resolve_phi p i.inst_operands = SOME v ==>
  eval_one_phi (scfg_ctrl c (SOME (if p = B then A else p)) n s)
    (update_phi_bypass A B i) = eval_one_phi s i
Proof
  strip_tac >> drule_all scfg_update_phi_bypass_selected >> strip_tac >>
  simp[eval_one_phi_def, scfg_ctrl_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[] >> Cases_on `outs` >> simp[] >>
  metis_tac[scfg_ctrl_operand, scfg_ctrl_def]
QED

Theorem scfg_update_phi_bypass_eval_phis:
  bb_well_formed bb /\ phi_values_agree A B bb.bb_instructions /\
  A <> B /\ s.vs_prev_bb = SOME p /\
  (!i. MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
    phi_well_formed i.inst_operands /\ ?v. resolve_phi p i.inst_operands = SOME v) ==>
  eval_phis (scfg_ctrl c (SOME (if p = B then A else p)) n s)
    (MAP (update_phi_bypass A B) bb.bb_instructions) =
  exec_result_map (scfg_ctrl c (SOME (if p = B then A else p)) n)
    (eval_phis s bb.bb_instructions)
Proof
  strip_tac >> irule scfg_eval_phis_map >> simp[] >>
  rpt strip_tac >> irule scfg_update_phi_bypass_eval_one >> metis_tac[]
QED

Definition scfg_bypass_aligned_def:
  scfg_bypass_aligned a b s t <=> s.vs_current_bb <> b.bb_label /\
    t = scfg_ctrl s.vs_current_bb
      (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb)
      s.vs_inst_idx s
End

Theorem scfg_normalized_phi_selection:
  scfg_normalized fn /\ MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
  i.inst_opcode = PHI /\ fn_cfg_edge fn p bb.bb_label ==>
  phi_well_formed i.inst_operands /\ ?v. resolve_phi p i.inst_operands = SOME v
Proof
  strip_tac >>
  `fn_inst_wf fn /\ simplify_cfg_fn_ok fn` by
    metis_tac[scfg_normalized_static, scfg_static_inst_wf, scfg_static_ok] >>
  `inst_wf i` by (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[fn_insts_MEM]) >>
  conj_tac >- (qpat_x_assum `inst_wf i` mp_tac >> simp[inst_wf_def]) >>
  `fn_reachable fn bb.bb_label` by metis_tac[scfg_normalized_reachable] >>
  qpat_x_assum `fn_cfg_edge _ _ _`
    (qx_choose_then `pb` strip_assume_tac o REWRITE_RULE [fn_cfg_edge_def]) >>
  `fn_reachable fn pb.bb_label` by metis_tac[scfg_normalized_reachable] >>
  fs[simplify_cfg_fn_ok_def] >> metis_tac[]
QED

Theorem scfg_bypass_phi_prefix_length:
  phi_prefix_length (scfg_bypass_block a b bb).bb_instructions =
  phi_prefix_length bb.bb_instructions
Proof
  simp[scfg_bypass_block_def] >>
  qspec_tac (`bb.bb_instructions`, `xs`) >> Induct >> simp[phi_prefix_length_def]
QED

Theorem scfg_bypass_eval_one_phi:
  scfg_bypass_hyp fn a b fn' /\ MEM bb fn.fn_blocks /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  fn_cfg_edge fn p bb.bb_label /\ s.vs_prev_bb = SOME p ==>
  eval_one_phi
    (scfg_ctrl c (SOME (if p = b.bb_label then a.bb_label else p)) n s)
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) bb.bb_label i) =
  eval_one_phi s i
Proof
  strip_tac >>
  `scfg_normalized fn /\ wf_function fn` by
    metis_tac[scfg_bypass_hyp_def, scfg_bypass_old_static, scfg_static_wf] >>
  Cases_on `bb.bb_label = HD (bb_succs b)`
  >- (`bb_well_formed bb /\ phi_values_agree a.bb_label b.bb_label bb.bb_instructions /\
       a.bb_label <> b.bb_label` by
        (fs[scfg_bypass_hyp_def] >> gvs[] >>
         metis_tac[lookup_block_member_label, same_label_same_block,
           wf_function_def, can_bypass_jump_labels_distinct]) >>
      `phi_well_formed i.inst_operands /\ ?v. resolve_phi p i.inst_operands = SOME v` by
        metis_tac[scfg_normalized_phi_selection] >>
      simp[scfg_bypass_image_phi] >> irule scfg_update_phi_bypass_eval_one >> metis_tac[]) >>
  `p <> b.bb_label` by
    (fs[scfg_bypass_hyp_def] >> gvs[] >>
     metis_tac[scfg_bypass_outgoing, wf_function_def]) >>
  simp[scfg_bypass_image_phi, eval_one_phi_def, scfg_ctrl_def] >>
  namedCases_on `i.inst_outputs` ["", "out outs"] >> simp[] >> Cases_on `outs` >> simp[] >>
  Cases_on `resolve_phi p i.inst_operands` >> simp[] >>
  metis_tac[scfg_ctrl_operand, scfg_ctrl_def]
QED

Theorem scfg_bypass_eval_phis:
  scfg_bypass_hyp fn a b fn' /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (case s.vs_prev_bb of NONE => fn_entry_label fn = SOME s.vs_current_bb
    | SOME p => fn_cfg_edge fn p s.vs_current_bb) ==>
  eval_phis
    (scfg_ctrl c (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p)
      s.vs_prev_bb) n s)
    (scfg_bypass_block a b bb).bb_instructions =
  exec_result_map
    (scfg_ctrl c (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p)
      s.vs_prev_bb) n) (eval_phis s bb.bb_instructions)
Proof
  strip_tac >> simp[scfg_bypass_block_def] >> irule scfg_eval_phis_map >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `PHI <> JMP /\ PHI <> JNZ` by simp[] >>
      metis_tac[scfg_bypass_image_opcode]) >>
  rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  Cases_on `s.vs_prev_bb` >> gvs[]
  >- (`simplify_cfg_fn_ok fn /\ wf_function fn` by
        metis_tac[scfg_bypass_old_static, scfg_static_ok, scfg_static_wf] >>
      metis_tac[scfg_phi_not_entry]) >>
  qpat_x_assum `bb.bb_label = s.vs_current_bb` (SUBST_ALL_TAC o SYM) >>
  irule scfg_bypass_eval_one_phi >> metis_tac[]
QED

Theorem scfg_bypass_enters_block:
  scfg_bypass_hyp fn a b fn' /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  (case s.vs_prev_bb of NONE => fn_entry_label fn = SOME s.vs_current_bb
    | SOME p => fn_cfg_edge fn p s.vs_current_bb) ==>
  (enters_block fn' t t1 <=>
   ?s1. enters_block fn s s1 /\ scfg_bypass_aligned a b s1 t1)
Proof
  strip_tac >> drule_all scfg_bypass_eval_phis >>
  disch_then (qspecl_then [`0`, `s.vs_current_bb`] assume_tac) >>
  drule scfg_bypass_lookup_eq >>
  disch_then (qspec_then `s.vs_current_bb` assume_tac) >>
  gvs[scfg_bypass_aligned_def] >>
  simp[enters_block_def, scfg_ctrl_def, scfg_bypass_phi_prefix_length] >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[exec_result_map_def, scfg_ctrl_def] >>
  `v.vs_current_bb = s.vs_current_bb /\ v.vs_prev_bb = s.vs_prev_bb` by
    (drule eval_phis_only_updates_vs_vars >> disch_then SUBST1_TAC >> simp[]) >>
  eq_tac >> strip_tac >> gvs[venomStateTheory.venom_state_component_equality]
QED
