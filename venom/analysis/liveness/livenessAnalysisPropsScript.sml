(*
 * Liveness Analysis Correctness (Statements Only)
 *
 * Exported API for consumers of the liveness analysis.
 *
 * 1) Fixpoint — liveness_analyze returns a stable result.
 * 2) Boundedness — live variables come from the function's instructions.
 * 3) Soundness — if v is live, it is used before redefinition on some path.
 *
 * Internal proof machinery (list helpers, monotonicity, PHI correctness,
 * iterate-level fixpoint) lives in proofs/livenessProofsScript.sml.
 *
 * Proofs re-exported via ACCEPT_TAC.
 *)

Theory livenessAnalysisProps
Ancestors
  livenessProofs

(* ==========================================================================
   1) Fixpoint
   ========================================================================== *)

(* liveness_analyze returns a fixpoint: one more pass changes nothing. *)
Theorem liveness_analyze_fixpoint:
  ∀fn.
    let cfg = cfg_analyze fn in
    let lr = liveness_analyze fn in
    liveness_one_pass cfg fn.fn_blocks lr cfg.cfg_dfs_post = lr
Proof
  ACCEPT_TAC liveness_analyze_fixpoint_proof
QED

(* ==========================================================================
   2) Boundedness
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
   3) Soundness
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
