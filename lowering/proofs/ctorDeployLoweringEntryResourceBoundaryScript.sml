(* Pointwise memory boundaries for the actual registered witness. *)
Theory ctorDeployLoweringEntryResourceBoundary
Ancestors
  abiEncoderRegisteredEffect valueEncoding venomState finite_map list
  pred_set arithmetic pair

Theorem deploy_ctor_registered_memory_exclusion:
  abi_encoder_registered_effect ids outs s t /\
  (!b n. MEM (b,n) outs ==> a < b \/ b+n <= a) /\
  (!i b n. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,n) ==>
    a < b \/ b+n <= a) ==>
  mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
  qpat_x_assum `!a. _ ==> _` irule >>
  simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem deploy_ctor_registered_memory_prefix:
  abi_encoder_registered_effect ids outs s t /\ a < q /\
  (!b n. MEM (b,n) outs ==> q <= b) /\
  (!i b n. i IN ids /\ FLOOKUP t.vs_allocas i = SOME (b,n) ==>
    q <= b) ==>
  mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory
Proof
  strip_tac >> irule deploy_ctor_registered_memory_exclusion >>
  qexistsl_tac [`ids`, `outs`] >>
  metis_tac[LESS_LESS_EQ_TRANS]
QED
