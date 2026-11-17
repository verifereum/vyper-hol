(* Stable conjunct projections from the compiler simulation relations. *)
Theory stateRelProj
Ancestors
  loweringStateRelDefs

Theorem state_rel_local_ptrs_rel:
  state_rel H func cenv cx vs ss ==> local_ptrs_rel func cenv vs.scopes ss
Proof
  simp[state_rel_def]
QED
