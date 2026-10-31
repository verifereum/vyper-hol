(* Registered-slot effects exclude only actual final allocation entries,
   never the unregistered remainder of a physical scratch reserve. *)
Theory abiEncoderRegisteredEffect
Ancestors
  valueEncoding venomState finite_map pred_set list

Definition abi_encoder_registered_effect_def:
  abi_encoder_registered_effect ids outs (s0:venom_state) (s:venom_state) <=>
    (!i r. FLOOKUP s0.vs_allocas i = SOME r ==> FLOOKUP s.vs_allocas i = SOME r) /\
    (!i. i NOTIN ids ==> FLOOKUP s.vs_allocas i = FLOOKUP s0.vs_allocas i) /\
    (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs /\
      (!i b sz. i IN ids /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
        a < b \/ b+sz <= a) ==>
      mem_bytes_at a 1 s.vs_memory = mem_bytes_at a 1 s0.vs_memory) /\
    s.vs_accounts = s0.vs_accounts /\ s.vs_transient = s0.vs_transient /\
    s.vs_logs = s0.vs_logs /\ s.vs_requests = s0.vs_requests
End

Theorem abi_encoder_registered_effect_refl:
  abi_encoder_registered_effect ids outs s s
Proof
  simp[abi_encoder_registered_effect_def]
QED

Theorem abi_encoder_registered_effect_allocated:
  abi_encoder_registered_effect ids outs s t /\ FLOOKUP s.vs_allocas i = SOME r ==>
  FLOOKUP t.vs_allocas i = SOME r
Proof
  simp[abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem abi_encoder_registered_effect_trans:
  abi_encoder_registered_effect ids outs s t /\
  abi_encoder_registered_effect ids outs t u ==>
  abi_encoder_registered_effect ids outs s u
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def] >>
  disch_then strip_assume_tac >> metis_tac[]
QED

Theorem abi_encoder_registered_effect_enlarge:
  abi_encoder_registered_effect ids outs s t /\ ids SUBSET larger /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) more ==>
       EVERY (\(b,n). a < b \/ b+n <= a) outs) ==>
  abi_encoder_registered_effect larger more s t
Proof
  simp_tac bool_ss [abi_encoder_registered_effect_def, SUBSET_DEF] >>
  disch_then strip_assume_tac >> rpt conj_tac >> metis_tac[]
QED
