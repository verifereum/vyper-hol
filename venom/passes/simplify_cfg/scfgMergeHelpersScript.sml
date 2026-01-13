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

(* Key insight: pred_labels fn lbl = [unique_pred] means only one block jumps to lbl.
   If bb.bb_label <> unique_pred, then bb is not that block, so lbl not in bb's successors. *)
Theorem block_no_successor_label_when_not_predecessor:
  !fn bb lbl unique_pred.
    cfg_wf fn /\
    MEM bb fn.fn_blocks /\
    pred_labels fn lbl = [unique_pred] /\
    bb.bb_label <> unique_pred ==>
    ~MEM lbl (block_successors bb)
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[pred_labels_def] >>
  `MEM bb [bb']` by (qpat_x_assum `FILTER _ _ = _` (SUBST1_TAC o SYM) >>
    simp[listTheory.MEM_FILTER]) >> gvs[]
QED

(* Lookup in remove_block *)
Theorem lookup_block_remove_block:
  !lbl b_lbl blocks bb.
    lookup_block lbl blocks = SOME bb /\ lbl <> b_lbl ==>
    lookup_block lbl (remove_block b_lbl blocks) = SOME bb
Proof
  Induct_on `blocks`
  >- simp[lookup_block_def, remove_block_def]
  >- (rpt strip_tac >> simp[lookup_block_def, remove_block_def] >>
      IF_CASES_TAC >> gvs[lookup_block_def] >> IF_CASES_TAC >> gvs[])
QED

Theorem lookup_block_remove_block_same:
  !b_lbl blocks.
    lookup_block b_lbl (remove_block b_lbl blocks) = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def, remove_block_def] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[lookup_block_def]
QED

Theorem lookup_block_remove_block_none:
  !lbl b_lbl blocks.
    lookup_block lbl blocks = NONE ==>
    lookup_block lbl (remove_block b_lbl blocks) = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def, remove_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> IF_CASES_TAC >> gvs[lookup_block_def]
QED

(* Lookup in replace_block *)
Theorem lookup_block_replace_block:
  !lbl blocks bb' bb.
    lookup_block lbl blocks = SOME bb ==>
    lookup_block lbl (replace_block bb' blocks) =
      if lbl = bb'.bb_label then SOME bb' else SOME bb
Proof
  Induct_on `blocks` >> simp[lookup_block_def, replace_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  IF_CASES_TAC >> gvs[lookup_block_def] >> rw[]
QED

Theorem lookup_block_replace_block_none:
  !lbl blocks bb'.
    lookup_block lbl blocks = NONE ==>
    lookup_block lbl (replace_block bb' blocks) = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def, replace_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> IF_CASES_TAC >> gvs[lookup_block_def]
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

(* Helper tactics for step_inst_replace_label_non_phi *)
val binop_tac = irule exec_binop_replace_label_equiv >> simp[];
val unop_tac = irule exec_unop_replace_label_equiv >> simp[];
val modop_tac = irule exec_modop_replace_label_equiv >> simp[];
val error_tac = simp[result_equiv_cfg_def];
val halt_tac = simp[result_equiv_cfg_def, halt_state_state_equiv_cfg];
val revert_tac = simp[result_equiv_cfg_def, revert_state_state_equiv_cfg];
val nop_tac = simp[result_equiv_cfg_def, state_equiv_cfg_refl];
val jump_tac = simp[result_equiv_cfg_def, jump_to_state_equiv_cfg];

val ctx_output_tac =
  Cases_on `inst.inst_outputs` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
  Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
  irule update_var_state_equiv_cfg_eq >> gvs[state_equiv_cfg_def];

val read1_update_tac =
  Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
  Cases_on `t` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
  `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
  CASE_TAC >> gvs[result_equiv_cfg_def] >>
  Cases_on `inst.inst_outputs` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
  Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
  CASE_TAC >> gvs[result_equiv_cfg_def] >>
  irule update_var_state_equiv_cfg_eq >>
  simp[mload_state_equiv_cfg, sload_state_equiv_cfg, tload_state_equiv_cfg];

val store2_tac =
  Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
  Cases_on `t` >> gvs[result_equiv_cfg_def] >>
  Cases_on `t'` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
  `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >>
  `eval_operand h' s2 = eval_operand h' s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
  rpt CASE_TAC >> gvs[result_equiv_cfg_def, mstore_state_equiv_cfg, sstore_state_equiv_cfg, tstore_state_equiv_cfg];

val jnz_tac =
  rpt (Cases_on `t'` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
       TRY (Cases_on `h'` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, replace_label_operand_def]) >>
       TRY (IF_CASES_TAC >> gvs[]) >>
       TRY (Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, eval_operand_replace_label])) >>
  TRY (`eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[]) >>
  rpt (CASE_TAC >> gvs[result_equiv_cfg_def]) >>
  TRY (IF_CASES_TAC >> gvs[result_equiv_cfg_def, jump_to_state_equiv_cfg]);

val state_equiv_tac = simp[halt_state_state_equiv_cfg, revert_state_state_equiv_cfg, jump_to_state_equiv_cfg, state_equiv_cfg_refl];

(* 92 opcode cases - fully proven *)
Theorem step_inst_replace_label_non_phi:
  !old new inst s1 s2.
    state_equiv_cfg s1 s2 /\
    inst.inst_opcode <> PHI ==>
    result_equiv_cfg (step_inst inst s1)
                     (step_inst (replace_label_inst old new inst) s2)
Proof
  rpt strip_tac >> simp[step_inst_def, replace_label_inst_def] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  FIRST [binop_tac, unop_tac, modop_tac, error_tac, halt_tac, revert_tac, nop_tac, jump_tac]
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    CASE_TAC >> gvs[result_equiv_cfg_def]
    >- simp[result_equiv_cfg_refl]
    >- (
      Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
      CASE_TAC >> gvs[result_equiv_cfg_def] >>
      irule update_var_state_equiv_cfg_eq >> simp[mload_state_equiv_cfg]))
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t'` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >>
    `eval_operand h' s2 = eval_operand h' s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    rpt CASE_TAC >> gvs[result_equiv_cfg_def, mstore_state_equiv_cfg])
  >- (
    Cases_on `inst.inst_outputs` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, msize_update_var_state_equiv_cfg])
  >- read1_update_tac
  >- store2_tac
  >- read1_update_tac
  >- store2_tac
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `h` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, replace_label_operand_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, jump_to_state_equiv_cfg]
    >- (IF_CASES_TAC >> gvs[result_equiv_cfg_def, jump_to_state_equiv_cfg])
    >- (IF_CASES_TAC >> gvs[result_equiv_cfg_def]))
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `h'` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, replace_label_operand_def] >>
    IF_CASES_TAC >> gvs[]
    >- (
      Cases_on `t'` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
      Cases_on `h'` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, replace_label_operand_def] >>
      IF_CASES_TAC >> gvs[] >>
      Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, eval_operand_replace_label]
      >- (
        `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
        CASE_TAC >> gvs[result_equiv_cfg_def, jump_to_state_equiv_cfg])
      >- (
        `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
        CASE_TAC >> gvs[result_equiv_cfg_def] >>
        IF_CASES_TAC >> gvs[result_equiv_cfg_def, jump_to_state_equiv_cfg]))
    >- (
      jnz_tac
      >- simp[jump_to_state_equiv_cfg]
      >- simp[jump_to_state_equiv_cfg]
      >- rpt (simp[jump_to_state_equiv_cfg])
      >- simp[jump_to_state_equiv_cfg]))
  >- simp[halt_state_state_equiv_cfg]
  >- simp[revert_state_state_equiv_cfg]
  >- simp[halt_state_state_equiv_cfg]
  >- state_equiv_tac
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `inst.inst_outputs` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t'` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    CASE_TAC >> gvs[result_equiv_cfg_def, update_var_state_equiv_cfg])
  >- ctx_output_tac
  >- ctx_output_tac
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    CASE_TAC >> gvs[result_equiv_cfg_def] >>
    Cases_on `inst.inst_outputs` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, calldataload_update_var_state_equiv_cfg] >>
    CASE_TAC >> gvs[result_equiv_cfg_def, calldataload_update_var_state_equiv_cfg])
  >- ctx_output_tac
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t'` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >>
    `eval_operand h' s2 = eval_operand h' s1` by simp[eval_operand_state_equiv_cfg] >>
    `eval_operand h'' s2 = eval_operand h'' s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    rpt CASE_TAC >> gvs[result_equiv_cfg_def, calldatacopy_state_equiv_cfg])
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- ctx_output_tac
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    CASE_TAC >> gvs[result_equiv_cfg_def] >>
    Cases_on `inst.inst_outputs` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, accounts_state_equiv_cfg] >>
    CASE_TAC >> gvs[result_equiv_cfg_def] >>
    irule balance_update_var_state_equiv_cfg >> simp[])
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    CASE_TAC >> gvs[result_equiv_cfg_def] >>
    Cases_on `inst.inst_outputs` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    CASE_TAC >> gvs[result_equiv_cfg_def] >>
    irule blockhash_update_var_state_equiv_cfg >> simp[])
  >- ctx_output_tac
  >- (
    Cases_on `inst.inst_outputs` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, result_equiv_cfg_refl] >>
    irule returndatasize_update_var_state_equiv_cfg >> simp[])
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t'` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >>
    `eval_operand h' s2 = eval_operand h' s1` by simp[eval_operand_state_equiv_cfg] >>
    `eval_operand h'' s2 = eval_operand h'' s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    rpt CASE_TAC >> gvs[result_equiv_cfg_def]
    >- (irule revert_state_state_equiv_cfg >> simp[])
    >- gvs[state_equiv_cfg_def]
    >- gvs[state_equiv_cfg_def]
    >- (
      `s1.vs_returndata = s2.vs_returndata` by gvs[state_equiv_cfg_def] >> simp[] >>
      irule write_memory_with_expansion_state_equiv_cfg >> simp[]))
  >- ctx_output_tac
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t'` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >>
    `eval_operand h' s2 = eval_operand h' s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    `s1.vs_memory = s2.vs_memory` by gvs[state_equiv_cfg_def] >> simp[] >>
    rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
    irule update_var_state_equiv_cfg_eq >> gvs[state_equiv_cfg_def])
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t'` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >>
    `eval_operand h' s2 = eval_operand h' s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    rpt CASE_TAC >> gvs[result_equiv_cfg_def] >>
    irule update_var_state_equiv_cfg_eq >> gvs[state_equiv_cfg_def])
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    CASE_TAC >> gvs[result_equiv_cfg_def] >>
    CASE_TAC >> gvs[result_equiv_cfg_def, revert_state_state_equiv_cfg, state_equiv_cfg_refl])
  >- (
    Cases_on `inst.inst_operands` >> gvs[result_equiv_cfg_def] >>
    Cases_on `t` >> gvs[result_equiv_cfg_def, eval_operand_replace_label] >>
    `eval_operand h s2 = eval_operand h s1` by simp[eval_operand_state_equiv_cfg] >> simp[] >>
    CASE_TAC >> gvs[result_equiv_cfg_def] >>
    IF_CASES_TAC >> gvs[result_equiv_cfg_def, halt_state_state_equiv_cfg, state_equiv_cfg_refl])
QED

(* Helper: MAP replace_label_operand preserves list structure *)
Theorem map_replace_label_operand_length:
  !ops old new. LENGTH (MAP (replace_label_operand old new) ops) = LENGTH ops
Proof
  Induct >> simp[]
QED

(* For non-PHI non-terminator instructions, replacing labels has no effect
   since labels are only used by PHI and terminator instructions *)
Theorem step_inst_replace_label_non_phi_eq:
  !inst s old new.
    inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode ==>
    step_inst inst s = step_inst (replace_label_inst old new inst) s
Proof
  rpt strip_tac >>
  simp[step_inst_def, replace_label_inst_def] >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  (* For all non-PHI non-terminator opcodes, the operands are evaluated,
     and eval_operand_replace_label shows replacing labels has no effect *)
  simp[exec_binop_def, exec_unop_def, exec_modop_def] >>
  rpt (CASE_TAC >> gvs[eval_operand_replace_label])
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

(* When prev_bb is NONE, PHI always errors, so replacing labels doesn't matter *)
Theorem step_inst_replace_label_prev_bb_none:
  !inst s1 s2 old new.
    state_equiv_cfg s1 s2 /\ s1.vs_prev_bb = NONE /\ s2.vs_prev_bb = NONE ==>
    result_equiv_cfg (step_inst inst s1)
      (step_inst (replace_label_inst old new inst) s2)
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (
    simp[step_inst_def, replace_label_inst_def, result_equiv_cfg_def] >>
    Cases_on `inst.inst_outputs` >> simp[result_equiv_cfg_def] >>
    Cases_on `t` >> simp[result_equiv_cfg_def])
  >- (irule step_inst_replace_label_non_phi >> simp[])
QED

Theorem step_inst_replace_label_phi_prev_diff:
  !old new preds inst s prev.
    inst.inst_opcode = PHI /\
    s.vs_prev_bb = SOME prev /\
    prev <> old /\
    prev <> new /\
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

(* Key lemma: replacing labels doesn't change successors when old is not a successor *)
Theorem block_successors_replace_label_block:
  !bb old new. ~MEM old (block_successors bb) ==>
    block_successors (replace_label_block old new bb) = block_successors bb
Proof
  rpt strip_tac >> simp[block_successors_def, replace_label_block_def] >>
  Cases_on `block_last_inst bb` >> simp[block_last_inst_def]
  >- (gvs[] >> fs[block_last_inst_def, AllCaseEqs()])
  >- (
    fs[block_last_inst_def, AllCaseEqs()] >> gvs[] >>
    `bb.bb_instructions <> []` by gvs[NULL_EQ] >>
    simp[LAST_MAP] >>
    qabbrev_tac `last_inst = LAST bb.bb_instructions` >>
    simp[get_successors_def, replace_label_inst_def] >>
    IF_CASES_TAC >> simp[] >>
    `~MEM old (get_successors last_inst)` by
      fs[block_successors_def, block_last_inst_def, Abbr `last_inst`] >>
    fs[get_successors_def] >> gvs[] >>
    sg `!ops. ~MEM old (MAP THE (FILTER IS_SOME (MAP get_label ops))) ==>
              MAP get_label (MAP (replace_label_operand old new) ops) =
              MAP get_label ops`
    >- (Induct >> simp[] >> rpt strip_tac >>
        Cases_on `h` >> gvs[replace_label_operand_def, get_label_def])
    >- (first_x_assum (qspec_then `last_inst.inst_operands` mp_tac) >> simp[]))
QED

(* Helper: replace_label_inst removes old label from operands (when old <> new) *)
Theorem replace_label_inst_not_mem_old:
  !old new inst.
    old <> new ==>
    ~MEM (Label old) (replace_label_inst old new inst).inst_operands
Proof
  rpt strip_tac >>
  gvs[scfgDefsTheory.replace_label_inst_def, listTheory.MEM_MAP] >>
  Cases_on `y` >> gvs[scfgDefsTheory.replace_label_operand_def] >>
  Cases_on `s = old` >> gvs[]
QED

(* ===== update_last_inst Helpers ===== *)

(* Helper: update_last_inst preserves length *)
Theorem update_last_inst_length:
  !f l. LENGTH (update_last_inst f l) = LENGTH l
Proof
  gen_tac >> Induct >> rw[scfgDefsTheory.update_last_inst_def] >>
  Cases_on `l` >> gvs[scfgDefsTheory.update_last_inst_def]
QED

(* Helper: update_last_inst preserves elements before last *)
Theorem update_last_inst_el_unchanged:
  !f l idx.
    l <> [] /\ idx < LENGTH l - 1 ==>
    EL idx (update_last_inst f l) = EL idx l
Proof
  gen_tac >> Induct >> rw[scfgDefsTheory.update_last_inst_def] >>
  Cases_on `l` >> gvs[scfgDefsTheory.update_last_inst_def] >>
  Cases_on `idx` >> gvs[]
QED

(* Helper: update_last_inst applies f to the LAST element *)
Theorem update_last_inst_last:
  !f l. l <> [] ==> LAST (update_last_inst f l) = f (LAST l)
Proof
  Induct_on `l` >- simp[] >>
  rpt strip_tac >> Cases_on `l`
  >- simp[scfgDefsTheory.update_last_inst_def]
  >- (simp[scfgDefsTheory.update_last_inst_def] >>
      first_x_assum (qspec_then `f` mp_tac) >> simp[] >>
      strip_tac >> Cases_on `update_last_inst f (h'::t)`
      >- (`LENGTH (update_last_inst f (h'::t)) = LENGTH (h'::t)` by
            simp[update_last_inst_length] >> gvs[])
      >- simp[listTheory.LAST_CONS])
QED

(* Helper: EL at last position gives f(LAST l) *)
Theorem update_last_inst_el_last:
  !f l. l <> [] ==> EL (PRE (LENGTH l)) (update_last_inst f l) = f (LAST l)
Proof
  rpt strip_tac >>
  `LENGTH (update_last_inst f l) = LENGTH l` by simp[update_last_inst_length] >>
  `update_last_inst f l <> []` by (CCONTR_TAC >> gvs[]) >>
  `EL (PRE (LENGTH l)) (update_last_inst f l) = LAST (update_last_inst f l)` by
    (`PRE (LENGTH l) = PRE (LENGTH (update_last_inst f l))` by simp[] >>
     pop_assum SUBST1_TAC >> irule (GSYM listTheory.LAST_EL) >> simp[]) >>
  simp[update_last_inst_last]
QED

(* ===== Identity Lemmas for Label Replacement ===== *)

(* When old label is not a predecessor, replace_label_in_phi is identity on PHI instructions *)
Theorem replace_label_in_phi_not_pred:
  !inst old new preds.
    phi_inst_wf preds inst /\ ~MEM old preds ==>
    replace_label_in_phi old new inst = inst
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (simp[scfgDefsTheory.replace_label_in_phi_def] >>
      `~MEM (Label old) inst.inst_operands` by (
        gvs[phi_inst_wf_def] >>
        drule_all scfgPhiLemmasTheory.phi_ops_all_preds_no_label >> simp[]) >>
      `MAP (replace_label_operand old new) inst.inst_operands = inst.inst_operands` by (
        irule listTheory.LIST_EQ >>
        simp[listTheory.EL_MAP, listTheory.LENGTH_MAP] >> rpt strip_tac >>
        Cases_on `EL x inst.inst_operands` >> simp[replace_label_operand_def] >>
        CCONTR_TAC >> gvs[] >> gvs[listTheory.MEM_EL] >> metis_tac[]) >>
      simp[venomInstTheory.instruction_component_equality])
  >- simp[scfgDefsTheory.replace_label_in_phi_def]
QED

(* When old label is not a predecessor, replace_phi_in_block is identity *)
Theorem replace_phi_in_block_not_pred:
  !bb old new preds.
    phi_block_wf preds bb /\ ~MEM old preds ==>
    replace_phi_in_block old new bb = bb
Proof
  rpt strip_tac >> simp[scfgDefsTheory.replace_phi_in_block_def] >>
  `MAP (replace_label_in_phi old new) bb.bb_instructions = bb.bb_instructions` by (
    irule listTheory.LIST_EQ >>
    simp[listTheory.EL_MAP, listTheory.LENGTH_MAP] >> rpt strip_tac >>
    irule replace_label_in_phi_not_pred >>
    qexists_tac `preds` >> simp[] >>
    gvs[phi_block_wf_def] >> first_x_assum irule >>
    simp[listTheory.MEM_EL] >> metis_tac[]) >>
  simp[venomInstTheory.basic_block_component_equality]
QED

(* replace_phi_in_block is identity on update_last_inst when original has phi_block_wf
   and f preserves the opcode (so the last instruction stays a terminator, not PHI)
   and old label is not in the operands of the transformed last instruction *)
Theorem replace_phi_in_block_update_last_inst:
  !bb old new preds f.
    phi_block_wf preds bb /\ ~MEM old preds /\ bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (!inst. (f inst).inst_opcode = inst.inst_opcode) /\
    ~MEM (Label old) (f (LAST bb.bb_instructions)).inst_operands ==>
    replace_phi_in_block old new
      (bb with bb_instructions := update_last_inst f bb.bb_instructions) =
    (bb with bb_instructions := update_last_inst f bb.bb_instructions)
Proof
  rpt strip_tac >>
  simp[scfgDefsTheory.replace_phi_in_block_def,
       venomInstTheory.basic_block_component_equality] >>
  irule listTheory.LIST_EQ >>
  simp[listTheory.LENGTH_MAP, update_last_inst_length] >> rpt strip_tac >>
  simp[listTheory.EL_MAP, update_last_inst_length] >>
  Cases_on `x < LENGTH bb.bb_instructions - 1`
  >- (simp[update_last_inst_el_unchanged] >>
      irule replace_label_in_phi_not_pred >> qexists_tac `preds` >> simp[] >>
      gvs[phi_block_wf_def] >> first_x_assum irule >>
      simp[listTheory.MEM_EL] >> qexists_tac `x` >>
      gvs[rich_listTheory.LENGTH_FRONT, rich_listTheory.FRONT_EL])
  >- (`x = LENGTH bb.bb_instructions - 1` by simp[] >>
      simp[update_last_inst_el_last, scfgDefsTheory.replace_label_in_phi_def] >>
      `PRE (LENGTH bb.bb_instructions) = LENGTH bb.bb_instructions - 1` by simp[] >>
      gvs[GSYM update_last_inst_el_last] >>
      COND_CASES_TAC >> simp[] >>
      `(update_last_inst f bb.bb_instructions)❲LENGTH bb.bb_instructions - 1❳ =
       f (LAST bb.bb_instructions)` by
        (simp[GSYM arithmeticTheory.PRE_SUB1] >>
         irule update_last_inst_el_last >> simp[]) >>
      `(f (LAST bb.bb_instructions)).inst_opcode =
       (LAST bb.bb_instructions).inst_opcode` by simp[] >>
      gvs[is_terminator_def])
QED

(* Lookup through conditional MAP when f preserves labels and is identity on target *)
Theorem lookup_block_MAP_conditional_identity:
  !lbl blocks bb f P.
    lookup_block lbl blocks = SOME bb /\
    f bb = bb /\
    (!b. (f b).bb_label = b.bb_label) ==>
    lookup_block lbl (MAP (\b. if P b.bb_label then f b else b) blocks) = SOME bb
Proof
  Induct_on `blocks` >> simp[venomInstTheory.lookup_block_def] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[] >>
  Cases_on `P h.bb_label` >> gvs[]
QED
(* Helper: jump_only_target implies block_successors is singleton *)
Theorem jump_only_target_block_successors:
  !bb lbl. jump_only_target bb = SOME lbl ==> block_successors bb = [lbl]
Proof
  rpt strip_tac >>
  gvs[jump_only_target_def, block_successors_def, block_last_inst_def,
      get_successors_def, AllCaseEqs(), is_terminator_def, get_label_def]
QED

(* Helper: replace_label_inst is identity when old label not in operands *)
Theorem replace_label_inst_id:
  !old new inst.
    ~MEM (Label old) inst.inst_operands ==>
    replace_label_inst old new inst = inst
Proof
  rpt strip_tac >>
  simp[scfgDefsTheory.replace_label_inst_def, instruction_component_equality] >>
  irule listTheory.LIST_EQ >> simp[listTheory.LENGTH_MAP] >> rpt strip_tac >>
  simp[listTheory.EL_MAP] >>
  Cases_on `EL x inst.inst_operands` >> simp[scfgDefsTheory.replace_label_operand_def] >>
  CCONTR_TAC >> gvs[] >> gvs[listTheory.MEM_EL] >> metis_tac[]
QED

(* Helper: replace_label_block is identity when no instruction has old label *)
Theorem replace_label_block_identity_no_old_label:
  !old new bb.
    (!inst. MEM inst bb.bb_instructions ==> ~MEM (Label old) inst.inst_operands) ==>
    replace_label_block old new bb = bb
Proof
  rpt strip_tac >>
  simp[scfgDefsTheory.replace_label_block_def, basic_block_component_equality] >>
  irule listTheory.LIST_EQ >> simp[listTheory.LENGTH_MAP] >> rpt strip_tac >>
  simp[listTheory.EL_MAP] >>
  irule replace_label_inst_id >>
  first_x_assum irule >> simp[listTheory.MEM_EL] >> qexists_tac `x` >> simp[]
QED

(* Helper: terminator instructions don't have Label lbl if lbl not in successors *)
Theorem terminator_no_label_when_not_successor:
  !inst lbl.
    is_terminator inst.inst_opcode /\ ~MEM lbl (get_successors inst) ==>
    ~MEM (Label lbl) inst.inst_operands
Proof
  rpt strip_tac >> CCONTR_TAC >>
  gvs[venomInstTheory.get_successors_def, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  first_x_assum (qspec_then `SOME lbl` mp_tac) >>
  simp[venomStateTheory.get_label_def] >>
  qexists_tac `Label lbl` >> simp[venomStateTheory.get_label_def]
QED

(* Helper: replace_label_block is identity after update_last_inst when:
   - PHIs don't have old label (phi_block_wf + ~MEM old preds)
   - old <> new (so terminator doesn't have old after replacement)
   - block has terminator at last position
   - IR invariant: non-PHI, non-terminator instructions have no Label operands *)
Theorem replace_label_block_update_last_inst_identity:
  !bb old new preds.
    phi_block_wf preds bb /\ ~MEM old preds /\ old <> new /\
    bb.bb_instructions <> [] /\
    block_terminator_last bb /\
    (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI /\
            ~is_terminator inst.inst_opcode ==> !lbl. ~MEM (Label lbl) inst.inst_operands) ==>
    replace_label_block old new
      (bb with bb_instructions :=
        update_last_inst (replace_label_inst old new) bb.bb_instructions) =
    (bb with bb_instructions :=
        update_last_inst (replace_label_inst old new) bb.bb_instructions)
Proof
  (* Strategy: case split on index in update_last_inst
     - x < LENGTH-1: PHIs use phi_ops_all_preds_no_label; non-PHI non-term via assumption
     - x = LENGTH-1: replace_label_inst_not_mem_old since old <> new *)
  rpt strip_tac >>
  simp[scfgDefsTheory.replace_label_block_def, basic_block_component_equality] >>
  irule listTheory.LIST_EQ >>
  simp[listTheory.LENGTH_MAP, update_last_inst_length] >> rpt strip_tac >>
  simp[listTheory.EL_MAP, update_last_inst_length] >>
  Cases_on `x < LENGTH bb.bb_instructions - 1`
  >- ((* FRONT case *)
      simp[update_last_inst_el_unchanged] >> irule replace_label_inst_id >>
      Cases_on `bb.bb_instructions❲x❳.inst_opcode = PHI`
      >- ((* PHI case *)
          gvs[phi_block_wf_def] >>
          `phi_inst_wf preds bb.bb_instructions❲x❳` by
            (first_x_assum irule >> simp[listTheory.MEM_EL] >>
             qexists_tac `x` >> simp[rich_listTheory.LENGTH_FRONT]) >>
          gvs[phi_inst_wf_def] >>
          metis_tac[scfgPhiLemmasTheory.phi_ops_all_preds_no_label])
      >- ((* non-PHI case: use IR invariant assumption *)
          gvs[block_terminator_last_def, get_instruction_def] >>
          `~is_terminator bb.bb_instructions❲x❳.inst_opcode` by
            (CCONTR_TAC >> gvs[] >>
             first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
          `MEM bb.bb_instructions❲x❳ bb.bb_instructions` by
            (simp[listTheory.MEM_EL] >> qexists_tac `x` >> simp[]) >>
          first_x_assum drule >> simp[]))
  >- ((* LAST case *)
      `x = LENGTH bb.bb_instructions - 1` by gvs[] >>
      simp[GSYM arithmeticTheory.PRE_SUB1, update_last_inst_el_last] >>
      irule replace_label_inst_id >> irule replace_label_inst_not_mem_old >> simp[])
QED

(* Helper: terminator in block has same successors as block_successors *)
Theorem terminator_inst_block_successors:
  !bb inst.
    block_terminator_last bb /\
    MEM inst bb.bb_instructions /\
    is_terminator inst.inst_opcode ==>
    get_successors inst = block_successors bb
Proof
  rpt strip_tac >>
  gvs[block_terminator_last_def, get_instruction_def] >>
  `?n. n < LENGTH bb.bb_instructions /\ EL n bb.bb_instructions = inst` by
    (gvs[listTheory.MEM_EL] >> metis_tac[]) >>
  `n = LENGTH bb.bb_instructions - 1` by
    (first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  gvs[scfgDefsTheory.block_successors_def, scfgDefsTheory.block_last_inst_def] >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  simp[listTheory.NULL_EQ] >>
  `LAST bb.bb_instructions = EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions` by
    simp[listTheory.LAST_EL] >>
  `PRE (LENGTH bb.bb_instructions) = LENGTH bb.bb_instructions - 1` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  gvs[]
QED

val _ = export_theory();
