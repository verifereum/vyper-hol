(* Read the copied snapshot element under arbitrary destination-memory taint. *)
Theory bodyForArraySnapshotReadbackMods
Ancestors
  robustCopyTransportPtr rawCallBufferPtr valueCopy arithmetic

Theorem for_array_snapshot_readback_mods:
  val_wf tv v /\ val_footprint tv v <= bytes /\
  mem_bytes_at dst bytes result =
    mem_bytes_at src bytes (if ctor then source else section) /\
  (!i. dst <= i /\ i < dst + bytes ==>
    (i IN dirty' <=> ctor /\ src + (i - dst) IN dirty)) /\
  (ctor ==> !m. mem_agree_outside dirty source m ==> val_in_memory tv v src m) /\
  (~ctor ==> val_in_memory tv v src section) ==>
  !m. mem_agree_outside dirty' result m ==> val_in_memory tv v dst m
Proof
  Cases_on `ctor` >> simp[] >> strip_tac
  >- (gen_tac >> disch_tac >> irule robust_val_in_memory_copy_transport >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`source`,`result`,`bytes`,`src`,`dirty`,`dirty'`] >> simp[] >>
      qx_gen_tac `j` >> disch_tac >>
      qpat_assum `!i. dst <= i /\ _ ==> _` (qspec_then `dst + j` mp_tac) >>
      simp[]) >>
  gen_tac >> disch_tac >>
  `val_in_memory tv v dst result` by
    (irule val_in_memory_relocate >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`src`,`bytes`,`section`] >> simp[]) >>
  irule clean_footprint_robust_val_in_memory >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`dirty'`,`result`] >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_assum `!j. dst <= j /\ _ ==> _` (qspec_then `i` irule) >> decide_tac
QED
