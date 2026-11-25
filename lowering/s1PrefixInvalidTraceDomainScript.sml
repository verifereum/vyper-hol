Theory s1PrefixInvalidTraceDomain
Ancestors
  s1PrefixDefs gasOutcomeFull vyperStorageTrace vyperState venomState list
  bodyFullExtCallPackingReady[qualified,ignore_grammar]

Theorem gas_prefix_full_invalid_trace_domain:
  storage_trace_frame source /\ ~storage_trace_domain cx st0 es.storage_trace /\
  ~s.vs_halted ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (es,s,G,tn)
Proof
  strip_tac >> simp[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`, `PG`,
                   `G`, `tn`, `s`] >> simp[gas_origin_ptr_focus_nil]) >>
  rpt strip_tac >>
  drule_all vyperStorageTraceTheory.storage_trace_frame_prefix >> simp[] >> strip_tac >>
  `es.storage_trace ++ observations = obs_pre ++ StorageOutcome rq outcome :: sfx` by fs[] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [APPEND_EQ_APPEND])
  >- (`l = []` by (Cases_on `l` >> fs[]) >>
      metis_tac[APPEND_NIL,
                bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]) >>
  metis_tac[valid_horizon_append,
            bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]
QED
