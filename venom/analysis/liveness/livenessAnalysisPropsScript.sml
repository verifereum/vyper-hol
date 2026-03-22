(*
 * Liveness Analysis Properties (Statements Only)
 *
 * FROZEN — do not modify statements. Proofs via ACCEPT_TAC from livenessProofs.
 *
 * 1) Boundedness — live variables come from the function's instructions.
 * 2) Soundness — if v is live, it is used before redefinition on some path.
 *)

Theory livenessAnalysisProps
Ancestors
  livenessProofs

(* ==========================================================================
   1) Boundedness
   ========================================================================== *)

Theorem live_vars_bounded:
  ∀fn lbl idx v.
    let st = liveness_analyze fn in
    MEM v (live_vars_at st lbl idx) ⇒
    MEM v (fn_all_vars fn.fn_blocks)
Proof
  ACCEPT_TAC live_vars_bounded_proof
QED

(* ==========================================================================
   2) Soundness
   ========================================================================== *)

Theorem liveness_sound:
  ∀fn lbl idx v.
    let cfg = cfg_analyze fn in
    let st = liveness_analyze fn in
    let bbs = fn.fn_blocks in
    wf_function fn ∧
    MEM v (live_vars_at st lbl idx) ⇒
    ∃path.
      cfg_exec_path cfg ((lbl, idx) :: path) ∧
      used_before_defined bbs v ((lbl, idx) :: path)
Proof
  ACCEPT_TAC liveness_sound_proof
QED
