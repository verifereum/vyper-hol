(* TASK031 LOCAL clients of actual evaluator/take/adopt contracts. These do not
   activate Send/ExtCall, duplicate evaluation, or replay generated fixtures. *)
Theory vyperStorageOutcomeTest
Ancestors
  list option pair sum words vyperAST vyperState vyperInterpreter
  extCallOracle vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeBranches vyperCallOutcomeFrame
  vyperEvalOutcomeSuffix vyperCallOutcomeStorage vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperTypeSoundness vyperTypeSystem
  vyperTypeInvariants vyperCallOutcomeTest
Libs monadsyntax

(* Original TASK031 claims/proofs retained: exact SOME-list equality is
   refuted by activated_ExtCall_consumes_counterexample. Mode equivalence
   and a general suffix remain valid, including default consumption.
Theorem inactive_evaluator_modes:
  eval_stmt cx s st = (res,st') ==>
  (st.outcomes = NONE <=> st'.outcomes = NONE) /\
  (!os. st.outcomes = SOME os ==> st'.outcomes = SOME os)
Proof
  strip_tac >> imp_res_tac eval_outcomes_preserved_mutual >> simp[]
QED

Theorem actual_default_evaluator_suffix:
  eval_expr cx (THE drv) st = (res,st') ==>
  outcome_suffix st.outcomes st'.outcomes /\
  (st.outcomes = NONE <=> st'.outcomes = NONE) /\
  (!os. st.outcomes = SOME os ==> st'.outcomes = SOME os)
Proof
  strip_tac >> imp_res_tac eval_outcomes_preserved_mutual >> simp[]
QED
*)

Theorem inactive_evaluator_modes:
  eval_stmt cx s st = (res,st') ==>
  (st.outcomes = NONE <=> st'.outcomes = NONE) /\
  outcome_suffix st.outcomes st'.outcomes
Proof
  strip_tac >> imp_res_tac eval_outcome_suffix_mutual >>
  drule outcome_suffix_modes >> simp[]
QED

Theorem actual_default_evaluator_suffix:
  eval_expr cx (THE drv) st = (res,st') ==>
  outcome_suffix st.outcomes st'.outcomes /\
  (st.outcomes = NONE <=> st'.outcomes = NONE)
Proof
  strip_tac >> imp_res_tac eval_outcome_suffix_mutual >>
  drule outcome_suffix_modes >> simp[]
QED

Theorem remaining_oracle_storage_EVERY:
  oracle_storage_ok cx st /\ st.outcomes = SOME (prefix ++ rest) /\
  st'.outcomes = SOME rest ==>
  oracle_storage_ok cx st'
Proof
  strip_tac >> irule oracle_storage_ok_suffix >> qexists_tac `st` >>
  simp[outcome_suffix_def] >> qexists_tac `prefix` >> simp[]
QED

(* This is stronger than a fixture with a well-typed payload: neither payload
   storage nor account typing is assumed in the no-adoption case. *)
Theorem arbitrary_static_failed_payloads_preserve_storage:
  contract_storage_well_formed cx st /\
  take_call_outcome gas_cap target data value st = (INL (rq,co),st1) /\
  adopt_call_outcome rq co st1 = (INL (),st2) /\
  (rq.cr_static \/ ~co.co_success) ==>
  contract_storage_well_formed cx st2 /\ outcome_suffix st.outcomes st2.outcomes
Proof
  metis_tac[take_adopt_call_outcome_no_adoption_storage]
QED

(* Rejected successful payloads consume one ordinary entry before returning
   the runtime guard error; persistent/transient storage is not installed. *)
Theorem ordinary_guard_error_storage_suffix:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  st.outcomes = SOME (co::rest) /\
  rq = (call_outcome_request target data value st with cr_gas := gas_cap) /\
  ~computed_precompile rq /\ co.co_success /\ ~rq.cr_static /\
  ~accounts_runtime_well_typed co.co_accounts ==>
  take_call_outcome gas_cap target data value st =
    (INR (Error (RuntimeError "call outcome accounts")),
     st with <|outcomes := SOME rest; requests := st.requests ++ [rq];
       storage_trace := st.storage_trace ++ [StorageOutcome rq co]|>) /\
  contract_storage_well_formed cx
    (st with <|outcomes := SOME rest; requests := st.requests ++ [rq];
      storage_trace := st.storage_trace ++ [StorageOutcome rq co]|>) /\
  oracle_storage_ok cx
    (st with <|outcomes := SOME rest; requests := st.requests ++ [rq];
      storage_trace := st.storage_trace ++ [StorageOutcome rq co]|>) /\
  outcome_suffix st.outcomes (SOME rest)
Proof
  strip_tac >> drule_all take_call_outcome_ordinary >> strip_tac >> fs[] >>
  drule_all take_call_outcome_storage_suffix >> simp[]
QED

Theorem take_guard_error_storage_client:
  contract_storage_well_formed cx st /\ oracle_storage_ok cx st /\
  take_call_outcome gas_cap target data value st = (INR exc,st') ==>
  contract_storage_well_formed cx st' /\ oracle_storage_ok cx st' /\
  outcome_suffix st.outcomes st'.outcomes
Proof
  strip_tac >> drule_all take_call_outcome_storage_suffix >> simp[]
QED

(* Computed calls append a request when they consume an outcome. *)
Theorem computed_outcome_suffix_client:
  take_call_outcome gas_cap target data value st = (res,st') /\
  st.outcomes = SOME os /\
  computed_precompile (call_outcome_request target data value st) ==>
  st'.outcomes = SOME (DROP 1 os) /\
  st'.requests = st.requests ++
    (if os = [] then []
     else [call_outcome_request target data value st with cr_gas := gas_cap])
Proof
  Cases_on `os` >> strip_tac
  >- gvs[take_call_outcome_exhausted] >>
  rename1 `head::tail` >> gvs[take_call_outcome_def, take_request_outcome_def] >>
  pairarg_tac >>
  `rest = tail` by
    (mp_tac (Q.INST
       [`rq` |-> `call_outcome_request target data value st with cr_gas := gas_cap`,
        `os` |-> `head::tail`] take_outcome_rest) >> simp[]) >>
  gvs[AllCaseEqs(), record_request_def]
QED

(* Focused existing real-helper CV observations: ordinary success installs
   slot 8; static/failed bad-account payloads retain slot 4; rejected guard
   consumes an outcome. *)
Theorem focused_actual_boundary_snapshots:
  outcome_test_take_adopt 9w [1w] (SOME 5)
    [outcome_test_outcome T 17; outcome_test_outcome F 0] 17 8w 2 2 1 /\
  outcome_test_take_adopt 9w [] NONE
    [outcome_test_outcome T (2 ** 256)] 3 4w 1 2 0 /\
  outcome_test_take_adopt 9w [] (SOME 0)
    [outcome_test_outcome F (2 ** 256)] 3 4w 1 2 0 /\
  outcome_test_error_observations
Proof
  metis_tac[outcome_ordinary_success_cv, outcome_static_failed_cv,
            outcome_guard_rejected_NONE_cv]
QED

Theorem focused_computed_exhausted_snapshots:
  SND (take_call_outcome NONE 9w [] (SOME 0)
    (outcome_test_state with outcomes := SOME [])) =
    (outcome_test_state with outcomes := SOME []) /\
  SND (take_call_outcome NONE 1w [] NONE
    (outcome_test_state with outcomes := SOME [])) =
    (outcome_test_state with outcomes := SOME []) /\
  outcome_test_take_adopt 2w [] (SOME 0)
    [outcome_test_outcome F (2 ** 256)] 3 4w 1 2 0 /\
  outcome_test_take_adopt 2w [] (SOME 0)
    [outcome_test_outcome T 17; outcome_test_outcome T 17] 3 4w 1 2 1 /\
  outcome_test_take_adopt 1w [] NONE
    [outcome_test_outcome T 17] 3 4w 1 2 0 /\
  outcome_test_take_adopt 6w (REPLICATE 63 0w ++ [1w]) (SOME 0)
    [outcome_test_outcome T 17] 3 4w 1 2 0
Proof
  simp[outcome_exhausted_computed_cv]
QED
