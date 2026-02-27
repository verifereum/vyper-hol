(*
 * Liveness Analysis Correctness (Statements Only)
 *
 * Structured in five layers:
 *
 * 1) Set-as-list helpers
 *    - list_union and live_update have clean set semantics.
 *    - Both preserve ALL_DISTINCT.
 *
 * 2) Fixpoint
 *    - liveness_analyze returns a result stable under another pass.
 *
 * 3) Monotonicity
 *    - liveness_one_pass is order-preserving (lr_leq).
 *    - Starting from init, each pass only adds variables.
 *
 * 4) Boundedness
 *    - All live variables come from the function's instructions.
 *
 * 5) PHI correctness
 *    - input_vars_from adds only source-matching PHI operands.
 *
 * 6) Soundness
 *    - If v is live at a point, there exists a path where v is used
 *      before being redefined.
 *
 * Proofs live in proofs/livenessProofsScript.sml;
 * this file re-exports via ACCEPT_TAC.
 *)

Theory livenessAnalysisProps
Ancestors
  livenessProofs

(* ==========================================================================
   1) Set-as-list helpers
   ========================================================================== *)

Theorem list_union_set:
  ∀xs ys. set (list_union xs ys) = set xs ∪ set ys
Proof
  ACCEPT_TAC list_union_set_proof
QED

Theorem live_update_set:
  ∀defs uses live.
    set (live_update defs uses live) = (set live DIFF set defs) ∪ set uses
Proof
  ACCEPT_TAC live_update_set_proof
QED

Theorem list_union_no_dups:
  ∀xs ys. ALL_DISTINCT xs ==> ALL_DISTINCT (list_union xs ys)
Proof
  ACCEPT_TAC list_union_no_dups_proof
QED

Theorem live_update_no_dups:
  ∀defs uses live.
    ALL_DISTINCT live ==> ALL_DISTINCT (live_update defs uses live)
Proof
  ACCEPT_TAC live_update_no_dups_proof
QED

(* ==========================================================================
   2) Fixpoint
   ========================================================================== *)

(* The iterate loop returns a fixpoint: one more pass changes nothing. *)
Theorem liveness_iterate_fixpoint:
  ∀cfg bbs order lr.
    liveness_one_pass cfg bbs (liveness_iterate cfg bbs order lr) order =
    liveness_iterate cfg bbs order lr
Proof
  ACCEPT_TAC liveness_iterate_fixpoint_proof
QED

(* Top-level: liveness_analyze returns a fixpoint. *)
Theorem liveness_analyze_fixpoint:
  ∀fn.
    let cfg = cfg_analyze fn in
    let lr = liveness_analyze fn in
    liveness_one_pass cfg fn.fn_blocks lr cfg.cfg_dfs_post = lr
Proof
  ACCEPT_TAC liveness_analyze_fixpoint_proof
QED

(* ==========================================================================
   3) Monotonicity
   ========================================================================== *)

(* One pass is monotone: larger input ==> larger output. *)
Theorem liveness_one_pass_monotone:
  ∀cfg bbs order lr1 lr2.
    lr_leq lr1 lr2 ==>
    lr_leq (liveness_one_pass cfg bbs lr1 order)
            (liveness_one_pass cfg bbs lr2 order)
Proof
  ACCEPT_TAC liveness_one_pass_monotone_proof
QED

(* Starting from init, one pass only adds variables (never removes). *)
Theorem liveness_one_pass_increasing:
  ∀cfg bbs order lr.
    lr_leq (init_liveness bbs) lr ==>
    lr_leq lr (liveness_one_pass cfg bbs lr order)
Proof
  ACCEPT_TAC liveness_one_pass_increasing_proof
QED

(* ==========================================================================
   4) Boundedness
   ========================================================================== *)

(* All variables in any live set come from the function's instructions. *)
Theorem live_vars_bounded:
  ∀fn lbl idx v.
    let lr = liveness_analyze fn in
    MEM v (live_vars_at lr lbl idx) ==>
    MEM v (fn_all_vars fn.fn_blocks)
Proof
  ACCEPT_TAC live_vars_bounded_proof
QED

(* ==========================================================================
   5) PHI correctness
   ========================================================================== *)

(* input_vars_from only adds variables from source-matching PHI operands. *)
Theorem input_vars_from_phi_correct:
  ∀src_label instrs base v.
    MEM v (input_vars_from src_label instrs base) ==>
    MEM v base ∨
    ∃inst. MEM inst instrs ∧ inst.inst_opcode = PHI ∧
           MEM (src_label, v) (phi_pairs inst.inst_operands)
Proof
  ACCEPT_TAC input_vars_from_phi_correct_proof
QED

(* Non-PHI instructions don't affect input_vars_from. *)
Theorem input_vars_from_non_phi:
  ∀src_label instrs base.
    EVERY (λinst. inst.inst_opcode ≠ PHI) instrs ==>
    input_vars_from src_label instrs base = base
Proof
  ACCEPT_TAC input_vars_from_non_phi_proof
QED

(* ==========================================================================
   6) Soundness
   ========================================================================== *)

(* If v is live at (lbl, idx), there exists a path where v is used
   before being redefined. *)
Theorem liveness_sound:
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
  ACCEPT_TAC liveness_sound_proof
QED
