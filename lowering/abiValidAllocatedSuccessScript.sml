(* Successful allocation-backed decoding for every coherent type: the
   decoder success induction the extcall return seam consumes. *)
Theory abiValidAllocatedSuccess
Ancestors
  abiValidAllocatedMembers

Theorem abi_valid_allocated_success:
  !ce env sf ty tv. abi_valid_allocated_type_contract ce env sf ty tv
Proof
  cheat
QED
