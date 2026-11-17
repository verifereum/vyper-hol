(* Storage observations survive a failed source call and a failed lock check. *)
Theory vyperStorageTraceTest
Ancestors
  vyperInterpreter vyperState vyperContext vyperValue vyperAST
  vyperCallOutcome vyperCallOutcomeProps extCallOracle vyperStorage
  vyperStorageBackend vyperStorageFootprint
Libs
  wordsLib

Definition storage_trace_test_program_def:
  storage_trace_test_program =
    [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 4);
     FunctionDecl External Nonpayable F F "fail" [] [] NoneT
       [AnnAssign "seen" (BaseT (UintT 256))
          (TopLevelName (BaseT (UintT 256)) (NONE,"x"));
        Assert (Literal (BaseT BoolT) (BoolL F)) AssertBare]]
End

Definition storage_trace_test_machine_def:
  storage_trace_test_machine = initial_machine_state with
    <|sources := [(0w, [(NONE,storage_trace_test_program)])];
      layouts := [(0w, ([((NONE,"x"),4)], []))]|>
End

(* The real source call reads x before reverting; the machine rolls back,
   while the read remains part of the finite storage contract. *)
Theorem failed_call_retains_storage_root:
  call_external_trace (SOME []) [] storage_trace_test_machine
    (empty_call_txn with function_name := "fail") =
    (INR (AssertException ""), storage_trace_test_machine, [],
     [StorageRoot F 4 (BaseTV (UintT 256))])
Proof
  EVAL_TAC
QED

Theorem failed_lock_check_retains_observation:
  lookup_storage (n2w slot) (lookup_transient_storage addr st.tStorage) = 1w ==>
  acquire_nonreentrant_lock addr slot is_view st =
    (INR (Error (RuntimeError "nonreentrant lock")),
     st with storage_trace := st.storage_trace ++ [StorageLock slot])
Proof
  simp[acquire_nonreentrant_lock_def, record_storage_event_def,
       get_transient_storage_def, bind_def, ignore_bind_def, return_def, raise_def]
QED

(* Failed CREATE still adopts its backend, unlike a failed message call. *)
Theorem failed_create_records_adopted_backend:
  ~rq.cr_static /\ rq.cr_kind <> MessageCall /\
  rq.cr_kind <> DelegateMessageCall /\ ~outcome.co_success ==>
  (SND (adopt_call_outcome rq outcome st)).storage_trace =
    st.storage_trace ++ [StorageBackend outcome.co_accounts outcome.co_tStorage]
Proof
  simp[adopt_call_outcome_equation]
QED

(* The restart exposed DelegateMessageCall, absent from the saved test:
   failed delegate calls roll back rather than adopting the supplied backend. *)
Theorem failed_delegate_preserves_storage_trace:
  rq.cr_kind = DelegateMessageCall /\ ~outcome.co_success ==>
  (SND (adopt_call_outcome rq outcome st)).storage_trace = st.storage_trace
Proof
  simp[adopt_call_outcome_equation]
QED

(* A concrete message call rejected before execution adopts no backend. *)
Theorem insufficient_balance_preserves_storage_trace:
  st.outcomes = NONE /\
  ~cx.txn.is_static /\
  ~flags.rcf_is_delegate /\ ~flags.rcf_is_static /\
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = 0 /\
  (lookup_account cx.txn.target st.accounts).balance < amount ==>
  (SND (eval_raw_call cx flags target calldata amount gas st)).storage_trace =
    st.storage_trace
Proof
  strip_tac >>
  `~(amount <= (lookup_account cx.txn.target st.accounts).balance)` by decide_tac >>
  simp[eval_raw_call_def, frame_call_value_def, run_raw_call_def, run_ext_call_def,
       ext_call_value_transfer_ok_def, type_check_def, assert_def,
       bind_def, ignore_bind_def, get_accounts_def, get_transient_storage_def,
       lift_option_def, update_accounts_def, update_transient_def,
       append_logs_def, update_pending_deletions_def, return_def, raise_def,
       evaluation_state_component_equality] >>
  Cases_on `LENGTH calldata < dimword(:256)` >>
  gvs[wordsTheory.dimword_def, return_def, raise_def]
QED

Theorem concrete_static_raw_call_preserves_storage_trace:
  st.outcomes = NONE /\
  ~flags.rcf_is_delegate /\ flags.rcf_is_static /\
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = 0 /\
  run_raw_call cx flags target calldata 0 gas st.accounts st.tStorage =
    SOME (T, [], st.accounts, st.tStorage, [], []) ==>
  eval_raw_call cx flags target calldata 0 gas st =
    (INL (Value (BoolV T)), st)
Proof
  strip_tac >>
  Cases_on `cx.txn.is_static` >>
  simp[eval_raw_call_def, frame_call_value_def, check_def,
       type_check_def, assert_def, bind_def, ignore_bind_def,
       get_accounts_def, get_transient_storage_def, lift_option_def,
       update_accounts_def, update_transient_def, append_logs_def,
       update_pending_deletions_def,
       return_def, evaluation_state_component_equality]
QED

Theorem concrete_static_ext_call_preserves_storage_trace:
  st.outcomes = NONE /\
  run_ext_call cx.txn.target target calldata NONE gas st.accounts st.tStorage
    (vyper_to_tx_params cx.txn) =
    SOME (T, [], st.accounts, st.tStorage, [], []) ==>
  eval_ext_call_effects cx target calldata NONE gas st.accounts st = (INL [], st)
Proof
  strip_tac >>
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def,
       get_transient_storage_def, lift_option_def,
       update_accounts_def, update_transient_def, append_logs_def,
       update_pending_deletions_def,
       return_def, evaluation_state_component_equality]
QED

(* Rejected oracle accounts are observed but never adopted. The finite
   guard checks the observed data bound without requiring those accounts. *)
Theorem rejected_accounts_trace_domain:
  st.storage_trace = [] /\ st.outcomes = SOME os /\
  take_outcome rq os = (outcome,rest) /\
  outcome.co_success /\ ~rq.cr_static /\
  ~accounts_runtime_well_typed outcome.co_accounts /\
  LENGTH outcome.co_returnData < dimword(:256) ==>
  FST (take_request_outcome rq st) =
    INR (Error (RuntimeError "call outcome accounts")) /\
  storage_trace_domain cx st
    (SND (take_request_outcome rq st)).storage_trace
Proof
  simp[take_request_outcome_def] >> strip_tac >>
  simp[storage_trace_domain_def, valid_horizon_def,
       storage_trace_horizon_def, storage_trace_regions_def,
       storage_trace_locks_def, regions_consistent_def,
       storage_locks_separated_def, storage_well_formed_on_def,
       storage_observations_ok_def, storage_roots_fit_def,
       storage_trace_backends_well_formed_def]
QED
