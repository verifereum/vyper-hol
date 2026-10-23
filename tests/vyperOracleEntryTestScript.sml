(* Entry API regressions: actual CPS/CV entries, arbitrary body-state
   certificates, full NONE/SOME results, rollback and final requests.
   TASK056: obsolete pair-projection owner removed; direct clean entry API. *)
Theory vyperOracleEntryTest
Ancestors
  vyperInterpreter vyperSmallStep vyperCall extCallOracle
  vyperState vyperContext vyperValue vyperAST finite_map list option
Libs cv_transLib wordsLib

(* SHA's transitive grammar exports an unrelated constant named body. *)
val _ = Parse.hide "body";

(* These certificates distinguish the supplied oracle from an accidental
   NONE initializer, and the final request selector from a hardcoded [].
   The body premise is schematic: it does not assert that the inert evaluator
   can currently produce nonempty requests. *)
Theorem entry_body_failure_requests:
  ~cx.in_deploy /\ cx.txn.value = 0 /\
  eval_stmts cx body
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>) =
      (INR (Error (RuntimeError msg)), st) ==>
  call_external_function orc am cx F Nonpayable [] [] [] [] [] body NoneT =
    (INR (Error (RuntimeError msg)), am, st.requests)
Proof
  simp[call_external_function_def, bind_arguments_def,
       send_call_value_def, return_def, bind_def, ignore_bind_def,
       set_scopes_def, initial_state_def]
QED

Theorem entry_body_success_requests:
  ~cx.in_deploy /\ cx.txn.value = 0 /\
  eval_stmts cx body
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>) =
      (INL (), st) ==>
  call_external_function orc am cx F Nonpayable [] [] [] [] [] body NoneT =
    (INL NoneV, abstract_machine_from_state am.sources am.exports am.layouts st,
     st.requests)
Proof
  simp[call_external_function_def, bind_arguments_def,
       send_call_value_def, return_def, bind_def, ignore_bind_def,
       set_scopes_def, initial_state_def]
QED

Theorem entry_return_cast_failure_requests:
  ~cx.in_deploy /\ cx.txn.value = 0 /\
  evaluate_type (type_env_all_modules []) ret = SOME tv /\ safe_cast tv v = NONE /\
  eval_stmts cx body
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>) =
      (INR (ReturnException v), st) ==>
  call_external_function orc am cx F Nonpayable [] [] [] [] [] body ret =
    (INR (Error (TypeError "ext cast ret")), am, st.requests)
Proof
  simp[call_external_function_def, bind_arguments_def,
       send_call_value_def, return_def, bind_def, ignore_bind_def,
       set_scopes_def, initial_state_def]
QED

Definition entry_test_program_def:
  entry_test_program =
    [FunctionDecl External Nonpayable F F "ok" [] [] NoneT [Pass];
     FunctionDecl External Nonpayable F F "fail" [] [] NoneT
       [Assert (Literal (BaseT BoolT) (BoolL F)) AssertBare];
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Pass]]
End
val () = cv_auto_trans entry_test_program_def;

Definition entry_test_machine_def:
  entry_test_machine = initial_machine_state with
    sources := [(0w, [(NONE, entry_test_program)])]
End
val () = cv_auto_trans entry_test_machine_def;

Definition entry_test_observations_def:
  entry_test_observations orc =
  let am = entry_test_machine in
  let ok = call_external orc am (empty_call_txn with function_name := "ok") in
  let bad = call_external orc am (empty_call_txn with function_name := "fail") in
  let fresh = call_external_transaction orc am
      (empty_call_txn with function_name := "fail") in
  let loaded = load_contract orc initial_machine_state
      (empty_call_txn with function_name := "__init__")
      [(NONE, entry_test_program)] [] in
    FST ok = INL NoneV /\ SND (SND ok) = [] /\
    ISL (FST ok) /\ ISR (FST bad) /\ SND (SND bad) = [] /\
    (FST (SND bad)).logs = am.logs /\
    (FST (SND fresh)).logs = [] /\ SND (SND fresh) = [] /\
    (case loaded of INR _ => F | INL (deployed,rqs) =>
       rqs = [] /\ LENGTH deployed.sources = 1) /\
    ISR (load_contract orc initial_machine_state
      (empty_call_txn with function_name := "__init__")
      [(NONE, [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT
        [Assert (Literal (BaseT BoolT) (BoolL F)) AssertBare]])] [])
End
val () = cv_auto_trans entry_test_observations_def;

Theorem entry_none_cv:
  entry_test_observations NONE
Proof
  CONV_TAC cv_eval
QED

Theorem entry_some_cv:
  entry_test_observations (SOME []) /\
  entry_test_observations (SOME [extCallOracle$failed_outcome
    <|cr_target := 9w; cr_value := 0; cr_data := []; cr_static := F;
      cr_accounts := empty_accounts; cr_tStorage := empty_transient_storage|>])
Proof
  CONV_TAC cv_eval
QED

Theorem entry_failure_machine_rollback:
  call_external orc am tx = (INR exc,am',rqs) ==>
  am' = am
Proof
  metis_tac[call_external_error_rollback]
QED

Theorem entry_transaction_failure_rollback:
  call_external_transaction orc am tx = (INR exc,am',rqs) ==>
  am' = clear_machine_logs am
Proof
  simp[call_external_transaction_def] >>
  metis_tac[call_external_error_rollback]
QED

Theorem entry_none_initial_body_identity:
  initial_state am scs with <|outcomes := NONE; requests := []|> =
  initial_state am scs
Proof
  simp[initial_state_def]
QED

Definition entry_body_initializer_observations_def:
  entry_body_initializer_observations = (
    IS_SOME ((initial_state initial_machine_state [FEMPTY] with
      <|outcomes := SOME []; requests := []|>).outcomes) /\
    NULL ((initial_state initial_machine_state [FEMPTY] with
      <|outcomes := NONE; requests := []|>).requests))
End
val () = cv_auto_trans entry_body_initializer_observations_def;

Theorem entry_body_initializer_cv:
  entry_body_initializer_observations
Proof
  CONV_TAC cv_eval
QED
