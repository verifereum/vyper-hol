(* Exact equations for staging the original worklist transition. *)
Theory worklistStepCompute
Ancestors worklistDefs
Libs
  proofAuditLib

Theorem wl_step_cons:
  wl_step changed process deps (lbl::rest,st) =
    let next = process lbl st in
    if changed lbl st next then (rest ++ deps lbl,next)
    else (rest,next)
Proof
  simp[wl_step_def]
QED

Theorem wl_step_nil:
  wl_step changed process deps ([],st) = ([],st)
Proof
  simp[wl_step_def]
QED

val () = proofAuditLib.check_theory "worklistStepCompute";
