(*
 * Liveness Analysis Properties (Statements Only)
 *
 * FROZEN — do not modify statements. Proofs via ACCEPT_TAC from livenessProofs.
 *
 * Soundness — if v is live, it is used before redefinition on some path.
 *
 * Boundedness, the transfer equations and forward propagation live only
 * in livenessProofs.
 *)

Theory livenessAnalysisProps
Ancestors
  livenessProofs

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
