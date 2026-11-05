Theory lowerDloadFrameRepresentation
Ancestors
  lowerDloadFrameFloor lowerDloadLifetime lowerDloadOwnership
  venomExecSemantics venomState finite_map pred_set

Theorem ld_representation_empty:
  !owner bs bt sz. owner IN {} /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ (?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz))
Proof
  simp[]
QED

(* The independent floor facts are ld_setup_callee_floor. *)
Theorem ld_representation_enter:
  setup_callee fn args caller = SOME child /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= caller.vs_alloca_next) ==>
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= caller.vs_alloca_next \/
    (?j. j NOTIN keys /\ FLOOKUP child.vs_allocas j = SOME(bt,sz)))
Proof
  metis_tac[]
QED

(* Floor restoration itself is ld_return_floor. No memory restoration. *)
Theorem ld_representation_return:
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ (?j. j NOTIN keys /\ FLOOKUP caller.vs_allocas j = SOME(bt,sz))) /\
  bind_outputs outs vals (merge_callee_state caller callee) = SOME bound /\
  (!owner bs bt sz. owner IN live' /\ ld_site_entry E' owner bs bt sz ==>
    owner IN live /\ ld_site_entry E owner bs bt sz) ==>
  (!owner bs bt sz. owner IN live' /\ ld_site_entry E' owner bs bt sz ==>
    bt+sz <= f \/
    (?j. j NOTIN keys /\ FLOOKUP (adopt_return_fmp ir bound).vs_allocas j = SOME(bt,sz)))
Proof
  strip_tac >> drule ld_bind_outputs_allocas >> strip_tac >>
  gvs[adopt_return_fmp_allocas, merge_callee_state_def] >> metis_tac[]
QED
