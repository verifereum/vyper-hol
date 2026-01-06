(* 
 * Simplify-CFG Merge Helpers
 *
 * Helper lemmas for block merge and jump threading proofs.
 *)

Theory scfgMergeHelpers
Ancestors
  scfgPhiCorrect scfgTransform scfgStateOps list relation
Libs
  scfgDefsTheory scfgEquivTheory scfgPhiCorrectTheory scfgTransformTheory
  scfgStateOpsTheory
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

(* ===== Label Replacement Helpers ===== *)

(* Replacing labels in operands doesn't affect evaluation *)
Theorem eval_operand_replace_label:
  !old new op s.
    eval_operand (replace_label_operand old new op) s = eval_operand op s
Proof
  Cases_on `op` >> simp[replace_label_operand_def, eval_operand_def] >>
  rw[eval_operand_def]
QED

Theorem exec_binop_replace_label_equiv:
  !f old new inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_binop f inst s1)
      (exec_binop f (inst with inst_operands :=
         MAP (replace_label_operand old new) inst.inst_operands) s2)
Proof
  rpt strip_tac >> simp[exec_binop_def] >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_cfg_def] >>
  Cases_on `t` >> simp[result_equiv_cfg_def] >>
  Cases_on `t'` >> simp[result_equiv_cfg_def, eval_operand_replace_label] >>
  drule eval_operand_state_equiv_cfg >> strip_tac >>
  simp[eval_operand_state_equiv_cfg] >>
  rpt CASE_TAC >> gvs[result_equiv_cfg_def, update_var_state_equiv_cfg]
QED

Theorem exec_unop_replace_label_equiv:
  !f old new inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_unop f inst s1)
      (exec_unop f (inst with inst_operands :=
         MAP (replace_label_operand old new) inst.inst_operands) s2)
Proof
  rpt strip_tac >> simp[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_cfg_def] >>
  Cases_on `t` >> simp[result_equiv_cfg_def, eval_operand_replace_label] >>
  drule eval_operand_state_equiv_cfg >> strip_tac >>
  simp[eval_operand_state_equiv_cfg] >>
  rpt CASE_TAC >> gvs[result_equiv_cfg_def, update_var_state_equiv_cfg]
QED

Theorem exec_modop_replace_label_equiv:
  !f old new inst s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg (exec_modop f inst s1)
      (exec_modop f (inst with inst_operands :=
         MAP (replace_label_operand old new) inst.inst_operands) s2)
Proof
  rpt strip_tac >> simp[exec_modop_def] >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_cfg_def] >>
  Cases_on `t` >> simp[result_equiv_cfg_def] >>
  Cases_on `t'` >> simp[result_equiv_cfg_def] >>
  Cases_on `t` >> simp[result_equiv_cfg_def, eval_operand_replace_label] >>
  drule eval_operand_state_equiv_cfg >> strip_tac >>
  simp[eval_operand_state_equiv_cfg] >>
  rpt CASE_TAC >> gvs[result_equiv_cfg_def, update_var_state_equiv_cfg]
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
  drule_all resolve_phi_vals_not_label >> strip_tac >>
  Cases_on `val_op` >> gvs[replace_label_operand_def]
QED

(* CHEATED - 92 opcode cases, needs systematic handling *)
Theorem step_inst_replace_label_non_phi:
  !old new inst s1 s2.
    state_equiv_cfg s1 s2 /\
    inst.inst_opcode <> PHI ==>
    result_equiv_cfg (step_inst inst s1)
                     (step_inst (replace_label_inst old new inst) s2)
Proof
  cheat
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
  drule_all phi_ops_complete_MEM >> strip_tac >>
  `~MEM (Label new) inst.inst_operands` by
    (drule_all phi_ops_all_preds_no_label >> simp[]) >>
  `resolve_phi new (MAP (replace_label_operand old new) inst.inst_operands) =
   SOME val_op` by
    (drule_all resolve_phi_replace_label >>
     drule_all resolve_phi_vals_not_label >> strip_tac >>
     Cases_on `val_op` >> gvs[replace_label_operand_def]) >>
  simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def] >>
  simp[eval_operand_state_equiv_cfg, update_var_state_equiv_cfg] >>
  drule_all eval_operand_state_equiv_cfg >> strip_tac >> gvs[] >>
  Cases_on `eval_operand val_op s2` >> simp[result_equiv_cfg_def] >>
  irule update_var_state_equiv_cfg >> simp[]
QED

Theorem step_inst_replace_label_no_phi_old:
  !old new inst s.
    (inst.inst_opcode = PHI ==> ~MEM (Label old) inst.inst_operands) ==>
    result_equiv_cfg (step_inst inst s)
                     (step_inst (replace_label_inst old new inst) s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[]
  >- (
    `replace_label_inst old new inst = inst` by (
      Cases_on `inst` >> gvs[replace_label_inst_def] >>
      `MAP (replace_label_operand old new) l = l` suffices_by
        simp[instruction_component_equality] >>
      Induct_on `l` >> simp[] >> rpt strip_tac >>
      Cases_on `h` >> gvs[replace_label_operand_def]
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
  simp[result_equiv_cfg_refl]
QED

val _ = export_theory();
