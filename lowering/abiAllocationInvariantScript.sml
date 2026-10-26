(* Ordinary caller allocation invariants follow from actual execution from an
   empty allocation map, including calls that restore the caller's map. *)
Theory abiAllocationInvariant
Ancestors
  venomMemProofs venomMemDefs venomExecSemantics venomState venomInst
  finite_map relation

Theorem abi_alloca_invariant_reachable:
  !entry initial.
  RTC (\s t. ?fuel inst. P inst /\ step_inst fuel ctx inst s = OK t) entry initial ==>
  alloca_inv entry ==> alloca_inv initial
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >> fs[] >>
  drule_all alloca_inv_step_inst_proof >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem abi_alloca_invariant_initial:
  entry.vs_allocas = FEMPTY /\
  RTC (\s t. ?fuel inst. P inst /\ step_inst fuel ctx inst s = OK t) entry initial ==>
  alloca_inv initial
Proof
  strip_tac >> `alloca_inv entry` by (irule alloca_inv_empty_proof >> simp[]) >>
  drule_all abi_alloca_invariant_reachable >> simp[]
QED
