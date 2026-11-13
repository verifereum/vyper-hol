(* Output windows contained in registered allocations add no memory effects. *)
Theory bodyAbiEncodeRegisteredFrame
Ancestors
  abiEncoderWindowPhase abiEncoderRegisteredEffect venomState finite_map list
  pred_set arithmetic pair

Theorem abi_encode_registered_phase:
  window_phase ctx func st en ids outs s t /\
  (!b n. MEM (b,n) outs ==> ?id base size.
    id IN ids /\ FLOOKUP t.vs_allocas id = SOME (base,size) /\
    base <= b /\ b+n <= base+size) ==>
  window_phase ctx func st en ids [] s t
Proof
  simp[window_phase_def, abi_encoder_registered_effect_def] >>
  strip_tac >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule_all >> decide_tac
QED
