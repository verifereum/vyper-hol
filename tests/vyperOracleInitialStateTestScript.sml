(* TASK026: arbitrary oracle bookkeeping at source entry, not consumption. *)
Theory vyperOracleInitialStateTest
Ancestors
  list option vyperAST vyperValue vyperValueOperation vyperContext
  vyperState vyperInterpreter vyperTypeInvariants vyperTypeInitialState
Libs
  wordsLib cv_transLib

(* The old projections, including storage and immutable tables, are unchanged;
 * both new fields retain exactly the arbitrary supplied values. *)
Theorem oracle_initial_state_projections:
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).accounts = am.accounts /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).tStorage = am.tStorage /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).scopes = scs /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).immutables = am.immutables /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).logs = am.logs /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).pending_deletions = am.pending_deletions /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).outcomes = orc /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).requests = rqs
Proof
  simp[initial_state_def]
QED

Theorem oracle_initial_state_typing_modes:
  machine_well_typed am /\ scope_well_typed scope ==>
  state_well_typed (initial_state am [scope] with <|outcomes := NONE; requests := rqs|>) /\
  state_well_typed (initial_state am [scope] with <|outcomes := SOME os; requests := rqs|>) /\
  accounts_well_typed
    (initial_state am [scope] with <|outcomes := SOME os; requests := rqs|>).accounts
Proof
  simp[initial_state_def, machine_well_typed_def, state_well_typed_def]
QED

Theorem oracle_initial_state_invariant_modes:
  (env_consistent env cx
     (initial_state am scs with <|outcomes := NONE; requests := rqs|>) <=>
   env_consistent env cx (initial_state am scs)) /\
  (env_consistent env cx
     (initial_state am scs with <|outcomes := SOME os; requests := rqs|>) <=>
   env_consistent env cx (initial_state am scs))
Proof
  simp[]
QED

(* Original pre-activation statement/proof retained. The Send conjunct is
   false in SOME mode: vyperSendModesTest.send_zero_initial_state_not_inert
   was saved in inertcounter2 before this minimal amendment.
(* Exercise the complete arbitrary initial state, including arbitrary
 * nonempty prior requests/outcomes. SOME still does not consume an outcome. *)
Theorem oracle_initial_state_inert_modes:
  let st = initial_state am scs with <|outcomes := orc; requests := rqs|> in
    eval_expr empty_evaluation_context
      (Call NoneT Send
        [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE) st =
      (INL (Value NoneV), st) /\
    eval_expr empty_evaluation_context
      (Call NoneT (ExtCall T F ("unused", [], NoneT)) [] NONE) st =
      (INR (Error (TypeError "ExtCall no target")), st)
Proof
  EVAL_TAC >> simp[return_def, transfer_value_def]
QED
*)


Theorem oracle_initial_state_zero_address:
  dest_AddressV (BytesV (REPLICATE 20 0w)) = SOME 0w
Proof
  CONV_TAC cv_eval
QED

(* Exact whole-state behavior, including callee logs and scheduled deletions.
   A failed concrete call leaves the complete initial state unchanged. *)
Theorem oracle_initial_state_concrete_send:
  st.outcomes = NONE ==>
  eval_expr empty_evaluation_context
    (Call NoneT (Send F)
      [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
       Literal (BaseT (UintT 256)) (IntL 0)] NONE) st =
    (case run_ext_call empty_evaluation_context.txn.target 0w [] (SOME 0) 0
            st.accounts st.tStorage
            (vyper_to_tx_params empty_evaluation_context.txn) of
     | NONE => (INR (Error (RuntimeError "send run failed")), st)
     | SOME (success, data, accounts, transient, logs, deletions) =>
         if success then
           (INL (Value NoneV), st with
             <|accounts := accounts; tStorage := transient;
               logs := st.logs ++ logs;
               pending_deletions := deletions ++ st.pending_deletions|>)
         else (INR (Error (RuntimeError "send failed")), st))
Proof
  strip_tac >>
  simp[evaluate_def, evaluate_literal_def, materialise_def,
       type_check_def, assert_def, bind_def, ignore_bind_def, return_def,
       lift_option_type_def, eval_send_def,
       oracle_initial_state_zero_address, dest_NumV_def,
       ext_call_kwarg_def, forwarded_gas_def, get_accounts_def,
       get_transient_storage_def] >>
  Cases_on `run_ext_call empty_evaluation_context.txn.target 0w [] (SOME 0) 0
    st.accounts st.tStorage (vyper_to_tx_params empty_evaluation_context.txn)` >>
  simp[lift_option_def, bind_def, return_def, raise_def] >>
  rename1 `run_ext_call _ _ _ _ _ _ _ _ = SOME result` >>
  PairCases_on `result` >> Cases_on `result0` >>
  simp[check_def, assert_def, bind_def, ignore_bind_def, return_def,
       update_accounts_def, update_transient_def, append_logs_def,
       update_pending_deletions_def, evaluation_state_component_equality]
QED

(* Keep the public name and all arbitrary entry-state coverage. NONE Send
   follows the concrete callee result; the empty ExtCall is unchanged in
   either oracle mode and fails before recording or consuming an outcome.
   There are no keyword operands, so ExtCall opts = [] and Call drv = NONE. *)
Theorem oracle_initial_state_inert_modes:
  let st = initial_state am scs with <|outcomes := orc; requests := rqs|> in
    (orc = NONE ==>
      eval_expr empty_evaluation_context
        (Call NoneT (Send F)
          [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
           Literal (BaseT (UintT 256)) (IntL 0)] NONE) st =
        (case run_ext_call empty_evaluation_context.txn.target 0w [] (SOME 0) 0
                am.accounts am.tStorage
                (vyper_to_tx_params empty_evaluation_context.txn) of
         | NONE => (INR (Error (RuntimeError "send run failed")), st)
         | SOME (success, data, accounts, transient, logs, deletions) =>
             if success then
               (INL (Value NoneV), st with
                 <|accounts := accounts; tStorage := transient;
                   logs := am.logs ++ logs;
                   pending_deletions := deletions ++ am.pending_deletions|>)
             else (INR (Error (RuntimeError "send failed")), st))) /\
    eval_expr empty_evaluation_context
      (Call NoneT (ExtCall T F ("unused", [], NoneT) []) [] NONE) st =
      (INR (Error (TypeError "ExtCall operands")), st)
Proof
  simp_tac pure_ss [LET_THM] >> conj_tac
  >- (strip_tac >> gvs[] >>
      simp[oracle_initial_state_concrete_send, initial_state_def]) >>
  simp[evaluate_def, eval_ext_call_def, bind_def, return_def, raise_def]
QED
