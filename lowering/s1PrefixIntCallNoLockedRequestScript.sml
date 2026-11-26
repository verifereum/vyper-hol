(* The callee cannot observe a new request without a lock in the trace domain. *)
Theory s1PrefixIntCallNoLockedRequest
Ancestors
  bodyFullIntCallCallee s1PrefixDefs gasOutcomeFull
  vyperStorageFootprint vyperState venomState vyperInterpreter
  bodyFullExtCallPackingReady[qualified,ignore_grammar]

Theorem intcall_callee_no_locked_request_prefix:
  ~s.vs_halted /\
  ~(?u locked. lock_if_nr cx nr (is_view_mut mut) es = (INL u,locked) /\
               storage_trace_domain cx st0 locked.storage_trace) ==>
  gas_prefix_full (DF,lo,explicit,ctx,callee,PG) cx st0
    (intcall_callee_src cx name mut nr ss) (es,s,G,tn)
Proof
  strip_tac >> rewrite_tac[gas_prefix_full_def] >> qexists `[]` >>
  conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`,
                    `callee`, `PG`, `G`, `tn`, `s`] >>
      simp[storage_trace_domain_def, gas_origin_ptr_focus_nil]) >>
  rpt gen_tac >> strip_tac >>
  drule_all intcall_callee_outcome_after_lock >> strip_tac >>
  metis_tac[valid_horizon_append,
            bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]
QED
