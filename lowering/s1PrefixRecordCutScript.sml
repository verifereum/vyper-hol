(* Read an ordered source request record at an outcome cut. *)
Theory s1PrefixRecordCut
Ancestors
  s1PrefixOutcomeEvents e2eRequestCutDefs list

Theorem prefix_outcome_events_length_count[local]:
  !obs. LENGTH (prefix_outcome_events obs) = recorded_outcomes_count obs
Proof
  Induct_on `obs` >> simp[prefix_outcome_events_def, recorded_outcomes_count_def] >>
  Cases_on `h` >> simp[prefix_outcome_events_def, recorded_outcomes_count_def]
QED

Theorem prefix_record_ok_cut:
  prefix_record_ok rqs (pre ++ StorageOutcome rq co :: sfx) ==>
    (computed_precompile rq ==>
       co.co_accounts = rq.cr_accounts /\ co.co_tStorage = rq.cr_tStorage) /\
    (recorded_outcomes_count pre < LENGTH rqs /\
     EL (recorded_outcomes_count pre) rqs = rq)
Proof
  strip_tac >>
  `LENGTH (prefix_outcome_events pre) = recorded_outcomes_count pre` by
    irule prefix_outcome_events_length_count >>
    simp[] >>
  `prefix_outcome_events (pre ++ StorageOutcome rq co :: sfx) =
     prefix_outcome_events pre ++ [(rq,co)] ++ prefix_outcome_events sfx` by
    simp[prefix_outcome_events_append, prefix_outcome_events_def,
         APPEND_ASSOC] >>
  qpat_x_assum `prefix_record_ok _ _` mp_tac >>
  simp[prefix_record_ok_def, prefix_outcome_events_append,
       prefix_outcome_events_def, EVERY_APPEND] >>
  strip_tac >>
  qpat_assum `LENGTH (prefix_outcome_events _) = recorded_outcomes_count _`
    (fn h => REWRITE_TAC[GSYM h]) >>
  simp[EL_APPEND_EQN]
QED
