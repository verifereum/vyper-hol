(*
 * Checked call-stack and callable graph invariants.
 *)

Theory vyperTypeCallStackSoundness
Ancestors
  relation

(* ===== Generic relation closure infrastructure ===== *)

Theorem RTC_then_R_TC:
  RTC R x y /\ R y z ==> TC R x z
Proof
  metis_tac[RTC_CASES_TC, TC_RULES]
QED

