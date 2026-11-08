(* Held leaf: successful allocation-backed decoding for every coherent type.
   Proved separately by the decoder-induction lane (C1.3.3); admitted here so
   the return seam can be assembled in parallel. *)
Theory abiValidAllocatedSuccess
Ancestors
  abiValidAllocatedMembers

Theorem abi_valid_allocated_success:
  !ce env sf ty tv. abi_valid_allocated_type_contract ce env sf ty tv
Proof
  cheat
QED
