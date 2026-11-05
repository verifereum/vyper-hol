(* Conditional transport of captured compiler variables, not source locals. *)
Theory bodyPtrSubscriptTransport
Ancestors
  bodyPtrDefs

Theorem ghost_kept_provenance:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p ==>
  FLOOKUP G p = FLOOKUP G0 p
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_taint:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ not_fresh_at sa p ==>
  op_taint tn (Var p) = op_taint tn0 (Var p)
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_ptr_covers:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  not_fresh_at sa p /\ lookup_var p s = lookup_var p s0 /\
  ptr_covers G0 tn0 p s0 sz ==>
  ptr_covers G tn p s sz
Proof
  rpt strip_tac >>
  drule_all ghost_kept_provenance >>
  drule_all ghost_kept_taint >>
  rpt strip_tac >> gvs[ptr_covers_def]
QED
