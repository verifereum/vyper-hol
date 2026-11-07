(* Storage observations survive a failed source call and a failed lock check. *)
Theory vyperStorageTraceTest
Ancestors
  vyperInterpreter vyperState vyperContext vyperValue vyperAST
  vyperCallOutcome vyperCallOutcomeProps extCallOracle vyperStorage
  vyperStorageBackend
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
  ~rq.cr_static /\ rq.cr_kind <> MessageCall /\ ~outcome.co_success ==>
  (SND (adopt_call_outcome rq outcome st)).storage_trace =
    st.storage_trace ++ [StorageBackend outcome.co_accounts outcome.co_tStorage]
Proof
  simp[adopt_call_outcome_equation]
QED

(* A concrete message call rejected before execution adopts no backend. *)
Theorem insufficient_balance_preserves_storage_trace:
  st.outcomes = NONE /\
  ~flags.rcf_is_delegate /\ ~flags.rcf_is_static /\
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = 0 /\
  (lookup_account cx.txn.target st.accounts).balance < amount ==>
  eval_raw_call cx flags target calldata amount gas st =
    (INL (Value (BoolV F)), st)
Proof
  strip_tac >>
  `~(amount <= (lookup_account cx.txn.target st.accounts).balance)` by decide_tac >>
  simp[eval_raw_call_def, run_raw_call_def, run_ext_call_def,
       ext_call_value_transfer_ok_def, type_check_def, assert_def,
       bind_def, ignore_bind_def, get_accounts_def, get_transient_storage_def,
       lift_option_def, update_accounts_def, update_transient_def,
       append_logs_def, return_def, evaluation_state_component_equality]
QED

Theorem concrete_static_raw_call_preserves_storage_trace:
  st.outcomes = NONE /\
  ~flags.rcf_is_delegate /\ flags.rcf_is_static /\
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = 0 /\
  run_raw_call cx flags target calldata 0 gas st.accounts st.tStorage =
    SOME (T, [], st.accounts, st.tStorage, []) ==>
  eval_raw_call cx flags target calldata 0 gas st =
    (INL (Value (BoolV T)), st)
Proof
  strip_tac >>
  simp[eval_raw_call_def, type_check_def, assert_def, bind_def, ignore_bind_def,
       get_accounts_def, get_transient_storage_def, lift_option_def,
       update_accounts_def, update_transient_def, append_logs_def,
       return_def, evaluation_state_component_equality]
QED

Theorem concrete_static_ext_call_preserves_storage_trace:
  st.outcomes = NONE /\
  run_ext_call cx.txn.target target calldata NONE gas st.accounts st.tStorage
    (vyper_to_tx_params cx.txn) =
    SOME (T, [], st.accounts, st.tStorage, []) ==>
  eval_ext_call_effects cx target calldata NONE gas st.accounts st = (INL [], st)
Proof
  strip_tac >>
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def,
       get_transient_storage_def, lift_option_def,
       update_accounts_def, update_transient_def, append_logs_def,
       return_def, evaluation_state_component_equality]
QED
