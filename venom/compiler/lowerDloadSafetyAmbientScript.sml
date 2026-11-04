(* Opcode-independent ambient projections of synchronization. *)
Theory lowerDloadSafetyAmbient
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadDefs words

Theorem ld_sync_labels:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  s.vs_labels = t.vs_labels
Proof
  strip_tac >> drule ld_sync_memory >>
  simp[ld_nonghost_def]
QED

Theorem ld_sync_target_headroom:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  dload_headroom_ok C fn inst s ==>
  t.vs_alloca_next < dimword(:256)
Proof
  strip_tac >> drule ld_sync_frontier >>
  gvs[dload_headroom_ok_def]
QED
