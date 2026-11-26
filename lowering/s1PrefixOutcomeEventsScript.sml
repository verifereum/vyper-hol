(* The ordered request/outcome projection of source storage observations. *)
Theory s1PrefixOutcomeEvents
Ancestors
  vyperState extCallOracle list pair

Definition prefix_outcome_events_def:
  (prefix_outcome_events [] = []) /\
  (prefix_outcome_events (StorageRoot tr slot ty :: obs) =
     prefix_outcome_events obs) /\
  (prefix_outcome_events (StorageLock slot :: obs) =
     prefix_outcome_events obs) /\
  (prefix_outcome_events (StorageBackend acc ts :: obs) =
     prefix_outcome_events obs) /\
  (prefix_outcome_events (StorageOutcome rq co :: obs) =
     (rq,co) :: prefix_outcome_events obs)
End

Definition prefix_record_ok_def:
  prefix_record_ok rqs obs <=>
    rqs = MAP FST (prefix_outcome_events obs) /\
    EVERY (\(rq,co). computed_precompile rq ==>
             co.co_accounts = rq.cr_accounts /\ co.co_tStorage = rq.cr_tStorage)
      (prefix_outcome_events obs)
End

Theorem prefix_outcome_events_append:
  prefix_outcome_events (xs ++ ys) =
    prefix_outcome_events xs ++ prefix_outcome_events ys
Proof
  Induct_on `xs` >> simp[prefix_outcome_events_def] >>
  Cases_on `h` >> simp[prefix_outcome_events_def]
QED

Theorem prefix_record_ok_updates:
  prefix_record_ok [] [] /\
  (prefix_record_ok rqs obs ==>
     prefix_record_ok rqs (obs ++ [StorageRoot tr slot ty])) /\
  (prefix_record_ok rqs obs ==>
     prefix_record_ok rqs (obs ++ [StorageBackend acc ts])) /\
  (prefix_record_ok rqs obs ==>
     prefix_record_ok rqs (obs ++ [StorageLock key])) /\
  (prefix_record_ok rqs obs /\
   (computed_precompile rq ==>
      co.co_accounts = rq.cr_accounts /\ co.co_tStorage = rq.cr_tStorage) ==>
   prefix_record_ok (rqs ++ [rq]) (obs ++ [StorageOutcome rq co]))
Proof
  simp[prefix_record_ok_def, prefix_outcome_events_append,
       prefix_outcome_events_def, EVERY_APPEND] >>
  strip_tac >> simp[]
QED
