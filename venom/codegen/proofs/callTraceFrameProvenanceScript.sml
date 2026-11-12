(* Account-facing provenance for entries observed at the root frame depth. *)
Theory callTraceFrameProvenance
Ancestors
  callTraceEntryProvenance callTraceRootMetadata

Theorem call_trace_entry_provenance:
  wf_state es /\
  (FST (HD es.contexts)).msgParams.callee = a /\
  MEM (rq,oc) (call_trace es) ==>
  ?s t u. run_call_reaches es s /\ wf_state s /\
    LENGTH s.contexts = LENGTH es.contexts /\
    (FST (HD s.contexts)).msgParams.callee = a /\
    observable_call (FST (HD s.contexts)) /\
    rq.cr_accounts = s.rollback.accounts /\
    rq.cr_tStorage = s.rollback.tStorage /\
    oc.co_accounts = t.rollback.accounts /\
    oc.co_tStorage = t.rollback.tStorage /\
    ((step s = (INL u,t) /\ LENGTH t.contexts = LENGTH s.contexts) \/
     (?c. step s = (INL u,c) /\
          LENGTH c.contexts = SUC (LENGTH s.contexts) /\
          run_call c = SOME (INL (),t)))
Proof
  strip_tac >> drule_all call_trace_entry_origin >> strip_tac >>
  drule_all run_call_reaches_root_msgParams >> strip_tac >>
  qexistsl [`s`, `t`, `u`] >> simp[]
QED
