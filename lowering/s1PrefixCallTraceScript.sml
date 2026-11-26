(* Source-side request facts at a cut in the whole external-call trace. *)
Theory s1PrefixCallTrace
Ancestors
  s1PrefixExternalRecordFrame s1PrefixOrderedEval s1PrefixRecordCut
  s1PrefixOutcomeEvents

Theorem prefix_call_trace_outcome_facts:
  call_external_trace (SOME os) gs am tx = (res,am',rqs,obs) /\
  obs = pre ++ StorageOutcome rq outcome :: sfx ==>
  (computed_precompile rq ==>
     outcome.co_accounts = rq.cr_accounts /\ outcome.co_tStorage = rq.cr_tStorage) /\
  (~computed_precompile rq ==>
     recorded_outcomes_count pre < LENGTH rqs /\
     EL (recorded_outcomes_count pre) rqs = rq)
Proof
  strip_tac >>
  `prefix_record_ok rqs obs` by
    (irule (Q.INST [`P` |-> `prefix_record_ok`] prefix_call_trace_from_frames) >>
     simp_tac bool_ss [prefix_record_ok_updates, prefix_record_entry_frames] >>
     metis_tac[]) >>
  qpat_x_assum `obs = _` SUBST_ALL_TAC >>
  drule prefix_record_ok_cut >> simp[]
QED
