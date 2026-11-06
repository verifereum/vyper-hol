Theory exprSimAbiDecodeResourceAudit
Ancestors
  exprSimAbiDecodeBuiltin words

(* The outcome interface requires representability independently of allocation
   room.  In Resources this conjunct is discharged at both resource constructors
   (fresh allocation and reused allocation). *)
Theorem abi_decode_resources_max_representable:
  abi_builtin_decode_site_resources ctx func st last mn mx outsz cnt p d s ==>
  mx < dimword (:256)
Proof
  simp[abi_builtin_decode_site_resources_def]
QED
