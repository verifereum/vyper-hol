(* Requests and storage observations taken together: each recorded request
   leaves exactly one StorageOutcome in the trace, so a trace prefix fixes how
   many requests were recorded when it was taken. *)
Theory vyperRequestTrace
Ancestors
  vyperStorageFootprint vyperCallOutcome vyperState extCallOracle list

(* The requests a trace records: one per outcome taken for a request that is
   not a computed precompile, as record_request keeps only those. *)
Definition recorded_outcomes_count_def:
  recorded_outcomes_count observations =
    LENGTH (FILTER (\observation. case observation of
      StorageOutcome rq outcome => ~computed_precompile rq | _ => F)
      observations)
End

Theorem recorded_outcomes_count_simps[simp]:
  recorded_outcomes_count [] = 0 /\
  recorded_outcomes_count (xs ++ ys) =
    recorded_outcomes_count xs + recorded_outcomes_count ys /\
  recorded_outcomes_count [StorageOutcome rq outcome] =
    (if computed_precompile rq then 0 else 1) /\
  recorded_outcomes_count [StorageBackend accounts transient] = 0 /\
  recorded_outcomes_count [StorageRoot b offset tv] = 0 /\
  recorded_outcomes_count [StorageLock slot] = 0
Proof
  simp[recorded_outcomes_count_def, FILTER_APPEND_DISTRIB] >>
  Cases_on `computed_precompile rq` >> simp[]
QED

Theorem record_request_length:
  LENGTH (record_request rq rqs) =
    LENGTH rqs + (if computed_precompile rq then 0 else 1)
Proof
  rw[record_request_def]
QED

(* Taking an outcome adds one request to the list exactly when it adds one
   recorded outcome to the trace. *)
Theorem take_request_outcome_recorded_count:
  take_request_outcome rq st = (res,st') ==>
  recorded_outcomes_count st'.storage_trace + LENGTH st.requests =
    recorded_outcomes_count st.storage_trace + LENGTH st'.requests /\
  IS_PREFIX st'.requests st.requests /\
  IS_PREFIX st'.storage_trace st.storage_trace
Proof
  rw[take_request_outcome_def] >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[AllCaseEqs(), record_request_def] >>
  rw[] >> gvs[]
QED

Theorem take_create_outcome_recorded_count:
  take_create_outcome kind value initcode st = (res,st') ==>
  recorded_outcomes_count st'.storage_trace + LENGTH st.requests =
    recorded_outcomes_count st.storage_trace + LENGTH st'.requests /\
  IS_PREFIX st'.requests st.requests /\
  IS_PREFIX st'.storage_trace st.storage_trace
Proof
  rw[take_create_outcome_def] >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[AllCaseEqs(), record_request_def] >>
  rw[] >> gvs[]
QED

(* Adopting an outcome records no request; it may add one backend. *)
Theorem adopt_call_outcome_recorded_count:
  adopt_call_outcome rq outcome st = (res,st') ==>
  st'.requests = st.requests /\
  recorded_outcomes_count st'.storage_trace =
    recorded_outcomes_count st.storage_trace /\
  IS_PREFIX st'.storage_trace st.storage_trace
Proof
  rw[adopt_call_outcome_equation] >> simp[]
QED

(* An outcome event imposes nothing on a horizon; a backend must be well
   formed on its regions. *)
Theorem valid_horizon_snoc_outcome:
  valid_horizon cx st0 H (xs ++ [StorageOutcome rq outcome]) <=>
  valid_horizon cx st0 H xs
Proof
  simp[valid_horizon_def, storage_observations_ok_def,
       storage_trace_regions_def, storage_trace_locks_def,
       storage_roots_fit_def, storage_trace_backends_well_formed_def,
       EVERY_APPEND, FLAT_APPEND]
QED

Theorem valid_horizon_snoc_backend:
  valid_horizon cx st0 H (xs ++ [StorageBackend accounts transient]) <=>
  valid_horizon cx st0 H xs /\
  storage_well_formed_on cx
    (empty_state with <|accounts := accounts; tStorage := transient|>) (FST H)
Proof
  simp[valid_horizon_def, storage_observations_ok_def,
       storage_trace_regions_def, storage_trace_locks_def,
       storage_roots_fit_def, storage_trace_backends_well_formed_def,
       EVERY_APPEND, FLAT_APPEND] >>
  metis_tac[]
QED
