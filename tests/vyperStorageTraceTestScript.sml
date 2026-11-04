(* Storage observations survive a failed source call and a failed lock check. *)
Theory vyperStorageTraceTest
Ancestors
  vyperInterpreter vyperState vyperContext vyperValue vyperAST
  vyperCallOutcome vyperCallOutcomeProps extCallOracle
Libs
  wordsLib

Definition storage_trace_test_program_def:
  storage_trace_test_program =
    [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 4);
     FunctionDecl External Nonpayable F F "fail" [] [] NoneT
       [Expr (TopLevelName (BaseT (UintT 256)) (NONE,"x"));
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
