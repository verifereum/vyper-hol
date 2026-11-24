(* The linked AugAssign continuation receives the reached trace domain
   and the compiler-counter bounds at the selected store. *)
Theory bodyAugIdentifiedStoreMods
Ancestors
  bodyAugToStoreMods

Theorem augassign_identified_store_mods:
  ^(concl augassign_to_identified_store_mods)
Proof
  ACCEPT_TAC augassign_to_identified_store_mods
QED
