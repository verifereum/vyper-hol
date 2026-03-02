(*
 * Liveness Analysis — Internal Correctness Proofs
 *
 * Proofs are re-exported via livenessAnalysisPropsScript.sml.
 * This file contains the actual proof bodies (currently cheated).
 *)

Theory livenessProofs
Ancestors
  livenessDefs cfgDefs

(* ===== Set-as-list helper properties ===== *)

Theorem list_union_set_proof:
  ∀xs ys. set (list_union xs ys) = set xs ∪ set ys
Proof
  cheat
QED

Theorem live_update_set_proof:
  ∀defs uses live.
    set (live_update defs uses live) = (set live DIFF set defs) ∪ set uses
Proof
  cheat
QED

Theorem list_union_no_dups_proof:
  ∀xs ys. ALL_DISTINCT xs ==> ALL_DISTINCT (list_union xs ys)
Proof
  cheat
QED

Theorem live_update_no_dups_proof:
  ∀defs uses live.
    ALL_DISTINCT live ==> ALL_DISTINCT (live_update defs uses live)
Proof
  cheat
QED

(* ===== Fixpoint ===== *)

Theorem liveness_iterate_fixpoint_proof:
  ∀cfg bbs order lr.
    liveness_one_pass cfg bbs (liveness_iterate cfg bbs order lr) order =
    liveness_iterate cfg bbs order lr
Proof
  cheat
QED

Theorem liveness_analyze_fixpoint_proof:
  ∀fn.
    let cfg = cfg_analyze fn in
    let lr = liveness_analyze fn in
    liveness_one_pass cfg fn.fn_blocks lr cfg.cfg_dfs_post = lr
Proof
  cheat
QED

(* ===== Monotonicity ===== *)

Theorem liveness_one_pass_monotone_proof:
  ∀cfg bbs order lr1 lr2.
    lr_leq lr1 lr2 ==>
    lr_leq (liveness_one_pass cfg bbs lr1 order)
            (liveness_one_pass cfg bbs lr2 order)
Proof
  cheat
QED

Theorem liveness_one_pass_increasing_proof:
  ∀cfg bbs order lr.
    lr_leq (init_liveness bbs) lr ==>
    lr_leq lr (liveness_one_pass cfg bbs lr order)
Proof
  cheat
QED

(* ===== Boundedness ===== *)

Theorem live_vars_bounded_proof:
  ∀fn lbl idx v.
    let lr = liveness_analyze fn in
    MEM v (live_vars_at lr lbl idx) ==>
    MEM v (fn_all_vars fn.fn_blocks)
Proof
  cheat
QED

(* ===== PHI correctness ===== *)

Theorem input_vars_from_phi_correct_proof:
  ∀src_label instrs base v.
    MEM v (input_vars_from src_label instrs base) ==>
    MEM v base ∨
    ∃inst. MEM inst instrs ∧ inst.inst_opcode = PHI ∧
           MEM (src_label, v) (phi_pairs inst.inst_operands)
Proof
  cheat
QED

Theorem input_vars_from_non_phi_proof:
  ∀src_label instrs base.
    EVERY (λinst. inst.inst_opcode ≠ PHI) instrs ==>
    input_vars_from src_label instrs base = base
Proof
  cheat
QED

(* ===== Soundness ===== *)

Theorem liveness_sound_proof:
  ∀fn lbl idx v.
    let cfg = cfg_analyze fn in
    let lr = liveness_analyze fn in
    let bbs = fn.fn_blocks in
    wf_function fn ∧
    MEM v (live_vars_at lr lbl idx) ==>
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  cheat
QED
