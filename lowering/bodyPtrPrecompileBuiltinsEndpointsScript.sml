Theory bodyPtrPrecompileBuiltinsEndpoints
Ancestors fragGasSeqPtr

Theorem inst_seq_ptr_endpoint_property:
  inst_seq_ptr D lo ctx fn PG G tn xs s H tau /\
  (?H' tau'. inst_seq_ptr D lo ctx fn PG G tn xs s H' tau' /\
     P H' tau') ==> P H tau
Proof
  metis_tac[inst_seq_ptr_ghost_unique]
QED
