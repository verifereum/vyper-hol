Theory bodyPtrPrecompileBuiltinsEndpoints
Ancestors fragGasSeqPtr

(* Endpoints agree only for the identical cursor state and instruction list. *)
Theorem inst_seq_ptr_endpoint_unique:
  !xs s G tn H tau H' tau'.
    inst_seq_ptr D lo ctx fn PG G tn xs s H tau /\
    inst_seq_ptr D lo ctx fn PG G tn xs s H' tau' ==>
    H = H' /\ tau = tau'
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[inst_seq_ptr_def] >> metis_tac[]
QED

Theorem inst_seq_ptr_endpoint_property:
  inst_seq_ptr D lo ctx fn PG G tn xs s H tau /\
  (?H' tau'. inst_seq_ptr D lo ctx fn PG G tn xs s H' tau' /\
     P H' tau') ==> P H tau
Proof
  metis_tac[inst_seq_ptr_endpoint_unique]
QED
