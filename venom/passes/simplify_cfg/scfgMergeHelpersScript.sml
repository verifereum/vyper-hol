(* 
 * Simplify-CFG Merge Helpers
 *
 * Helper lemmas for block merge and jump threading proofs.
 *)

Theory scfgMergeHelpers
Ancestors
  scfgPhiCorrect scfgTransform list relation
Libs
  scfgDefsTheory scfgEquivTheory scfgPhiCorrectTheory scfgTransformTheory
  scfgPhiLemmasTheory
  venomSemTheory venomInstTheory venomStateTheory listTheory

(* ===== Lookup / Label Helpers ===== *)

Theorem lookup_block_unique:
  !lbl blocks bb bb'.
    ALL_DISTINCT (MAP (\b. b.bb_label) blocks) /\
    lookup_block lbl blocks = SOME bb /\
    MEM bb' blocks /\
    bb'.bb_label = lbl ==> bb' = bb
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  fs[listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem block_last_jmp_to_successors:
  !bb lbl.
    block_last_jmp_to lbl bb ==> block_successors bb = [lbl]
Proof
  rw[block_last_jmp_to_def, block_successors_def, get_successors_def,
     block_last_inst_def, is_terminator_def, venomStateTheory.get_label_def]
QED

Theorem pred_labels_only_jmp_target:
  !fn a a_lbl b_lbl lbl.
    cfg_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    block_last_jmp_to b_lbl a /\
    MEM a_lbl (pred_labels fn lbl) ==> lbl = b_lbl
Proof
  rpt strip_tac >>
  gvs[cfg_wf_def, pred_labels_def, listTheory.MEM_MAP, listTheory.MEM_FILTER,
      block_last_jmp_to_def, block_successors_def, get_successors_def,
      block_last_inst_def, is_terminator_def, venomStateTheory.get_label_def] >>
  sg `bb = a`
  >- (
    qpat_x_assum `lookup_block _ _ = SOME a` mp_tac >>
    qpat_x_assum `MEM bb _` mp_tac >>
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    qabbrev_tac `blocks = fn.fn_blocks` >> pop_assum kall_tac >>
    MAP_EVERY qid_spec_tac [`a`, `bb`, `blocks`] >>
    Induct >> simp[lookup_block_def] >>
    rpt strip_tac >> gvs[AllCaseEqs(), listTheory.MEM_MAP] >> metis_tac[]
  )
  >- gvs[is_terminator_def, venomStateTheory.get_label_def]
QED

Theorem pred_labels_no_jmp_other:
  !fn a a_lbl b_lbl lbl.
    cfg_wf fn /\
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    block_last_jmp_to b_lbl a /\
    lbl <> b_lbl ==> ~MEM a_lbl (pred_labels fn lbl)
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  drule_all pred_labels_only_jmp_target >> simp[]
QED

Theorem lookup_block_replace_label_block:
  !lbl blocks bb old new.
    lookup_block lbl blocks = SOME bb ==>
    lookup_block lbl (MAP (replace_label_block old new) blocks) =
    SOME (replace_label_block old new bb)
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), replace_label_block_def]
QED

Theorem lookup_block_replace_label_block_none:
  !lbl blocks old new.
    lookup_block lbl blocks = NONE ==>
    lookup_block lbl (MAP (replace_label_block old new) blocks) = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def, replace_label_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* ===== PHI Label Replacement ===== *)

Theorem resolve_phi_replace_label_id:
  !old new ops val_op.
    old <> new /\
    ~MEM (Label new) ops /\
    phi_vals_not_label ops /\
    resolve_phi old ops = SOME val_op ==>
    resolve_phi new (MAP (replace_label_operand old new) ops) = SOME val_op
Proof
  rpt strip_tac >>
  drule_all resolve_phi_replace_label >> strip_tac >>
  `(!lbl. val_op <> Label lbl)` by
    (irule resolve_phi_vals_not_label >> simp[]) >>
  simp[replace_label_operand_def]
QED

Theorem step_inst_replace_label_non_phi:
  !old new inst s1 s2.
    state_equiv_cfg s1 s2 /\
    inst.inst_opcode <> PHI ==>
    result_equiv_cfg (step_inst inst s1)
                     (step_inst (replace_label_inst old new inst) s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def,
       exec_binop_result_equiv_cfg, exec_unop_result_equiv_cfg,
       exec_modop_result_equiv_cfg,
       eval_operand_state_equiv_cfg, update_var_state_equiv_cfg,
       mstore_state_equiv_cfg, sstore_state_equiv_cfg, tstore_state_equiv_cfg,
       write_memory_with_expansion_state_equiv_cfg, jump_to_state_equiv_cfg,
       halt_state_state_equiv_cfg, revert_state_state_equiv_cfg,
       state_equiv_cfg_refl] >>
  gvs[AllCaseEqs(), result_equiv_cfg_def]
QED

Theorem step_inst_replace_label_phi:
  !old new preds inst s1 s2.
    state_equiv_cfg s1 s2 /\
    inst.inst_opcode = PHI /\
    s1.vs_prev_bb = SOME old /\
    s2.vs_prev_bb = SOME new /\
    old <> new /\
    phi_inst_wf preds inst /\
    MEM old preds /\
    ~MEM new preds
  ==>
    result_equiv_cfg (step_inst inst s1)
                     (step_inst (replace_label_inst old new inst) s2)
Proof
  rpt strip_tac >>
  drule_all phi_inst_wf_props >> strip_tac >>
  `resolve_phi old inst.inst_operands = SOME val_op` by
    (irule phi_ops_complete_MEM >> simp[]) >>
  `~MEM (Label new) inst.inst_operands` by
    (irule phi_ops_all_preds_no_label >> simp[]) >>
  `resolve_phi new (MAP (replace_label_operand old new) inst.inst_operands) =
   SOME val_op` by
    (irule resolve_phi_replace_label_id >> simp[]) >>
  simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def] >>
  simp[eval_operand_state_equiv_cfg, update_var_state_equiv_cfg]
QED

Theorem step_inst_replace_label_no_phi_old:
  !old new inst s.
    (inst.inst_opcode = PHI ==> ~MEM (Label old) inst.inst_operands) ==>
    result_equiv_cfg (step_inst inst s)
                     (step_inst (replace_label_inst old new inst) s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    `replace_label_inst old new inst = inst` by (
      Cases_on `inst` >>
      simp[replace_label_inst_def] >>
      qpat_x_assum `~MEM (Label old) _` mp_tac >>
      Induct_on `inst_operands` >> simp[replace_label_operand_def]
    ) >>
    simp[result_equiv_cfg_refl]
  )
  >- (
    `state_equiv_cfg s s` by simp[state_equiv_cfg_refl] >>
    drule_all step_inst_replace_label_non_phi >> simp[]
  )
QED

Theorem step_inst_replace_label_phi_prev_diff:
  !old new preds inst s prev.
    inst.inst_opcode = PHI /\
    s.vs_prev_bb = SOME prev /\
    prev <> old /\
    phi_inst_wf preds inst /\
    MEM prev preds
  ==>
    result_equiv_cfg (step_inst inst s)
                     (step_inst (replace_label_inst old new inst) s)
Proof
  rpt strip_tac >>
  drule_all phi_inst_wf_props >> strip_tac >>
  `resolve_phi prev (MAP (replace_label_operand old new) inst.inst_operands) =
   resolve_phi prev inst.inst_operands` by
    (irule resolve_phi_replace_label_other >> simp[]) >>
  simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def] >>
  simp[update_var_state_equiv_cfg, state_equiv_cfg_refl]
QED

val _ = export_theory();
