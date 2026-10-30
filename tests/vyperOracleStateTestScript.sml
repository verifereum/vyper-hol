(* Record migration regressions refreshed for Send/ExtCall constructors.
 * The concrete zero-value Send to an empty account remains inert; ordinary
 * SOME Send consumes/records an outcome. Original claims are retained below. *)
Theory vyperOracleStateTest
Ancestors
  arithmetic integer words list option finite_map finite_set cv_type While
  vfmState[ignore_grammar] vfmContext[ignore_grammar] vfmExecution[ignore_grammar]
  vyperAST vyperValue vyperValueOperation vyperContext vyperEvmBoundary
  vyperState vyperInterpreter vyperSmallStep extCallOracle
Libs
  cv_transLib wordsLib

Theorem initial_state_oracle_defaults:
  (initial_state am scs).outcomes = NONE /\
  (initial_state am scs).requests = [] /\
  empty_state.outcomes = NONE /\ empty_state.requests = []
Proof
  simp[initial_state_def, empty_state_def]
QED

Definition oracle_initialization_ok_def:
  oracle_initialization_ok = (
    IS_NONE ((initial_state initial_machine_state [FEMPTY]).outcomes) /\
    NULL ((initial_state initial_machine_state [FEMPTY]).requests) /\
    IS_NONE empty_state.outcomes /\ NULL empty_state.requests)
End
val () = cv_auto_trans oracle_initialization_ok_def;

Theorem oracle_initialization_cv:
  oracle_initialization_ok
Proof
  CONV_TAC cv_eval
QED

(* Existing whole-record equality and commuting updates, not a field API. *)
Theorem oracle_state_record_updates:
  (st with <|outcomes := os; requests := rqs|>) with scopes := scs =
  (st with scopes := scs) with <|outcomes := os; requests := rqs|> /\
  (st with <|outcomes := st.outcomes; requests := st.requests|>) = st
Proof
  simp[evaluation_state_component_equality]
QED

Theorem oracle_state_cv_roundtrip:
  to_evaluation_state
    (from_vyperState_evaluation_state
      (st with <|outcomes := os; requests := rqs|>)) =
  st with <|outcomes := os; requests := rqs|>
Proof
  metis_tac[from_to_evaluation_state_thm, from_to_def]
QED

Definition oracle_state_smoke_def:
  oracle_state_smoke os rqs =
  let st = empty_state with <|outcomes := os; requests := rqs|> in
    eval_expr empty_evaluation_context
      (Call NoneT (Send F)
        [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE) st =
      (INL (Value NoneV), st) /\
    eval_expr empty_evaluation_context
      (Call NoneT (ExtCall T F ("unused", [], NoneT) []) [] NONE) st =
      (INR (Error (TypeError "ExtCall operands")), st)
End
(* CV cannot translate equality on function-valued account/storage records.
 * Check whole-state equality above by kernel reduction, and translate the
 * result projections separately through the migrated monadic representation. *)
Definition oracle_state_observations_def:
  oracle_state_observations os rqs =
  let st = empty_state with <|outcomes := os; requests := rqs|> in
    FST (eval_expr empty_evaluation_context
      (Call NoneT (Send F)
        [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE) st) =
      INL (Value NoneV) /\
    FST (eval_expr empty_evaluation_context
      (Call NoneT (ExtCall T F ("unused", [], NoneT) []) [] NONE) st) =
      INR (Error (TypeError "ExtCall operands"))
End
(* Original precondition translation/proof retained. The now-registered
   cont_pre_eval_expr_cps closes both termination obligations during
   translation, so cv_auto_trans_pre correctly reports no precondition.
val oracle_state_observations_pre_def = oracle_state_observations_def
  |> SRULE [eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "oracle_state_observations_pre";

Theorem oracle_state_observations_pre[cv_pre]:
  oracle_state_observations_pre os rqs
Proof
  rw[oracle_state_observations_pre_def, cont_pre_IS_SOME_cont] >>
  qmatch_goalsub_abbrev_tac `eval_expr_cps cx ee ss DoneK` >>
  qspecl_then [`cx`, `ee`, `ss`, `DoneK`] mp_tac (cj 5 eval_cps_eq) >>
  Cases_on `eval_expr cx ee ss` >>
  rename1 `eval_expr cx ee ss = (res, st1)` >> Cases_on `res` >> simp[] >>
  disch_then (fn th => REWRITE_TAC [th]) >>
  simp[cont_def, Once OWHILE_THM, nextk_def]
QED
*)
val () = oracle_state_observations_def
  |> SRULE [eval_expr_eq_cont_cps] |> cv_auto_trans;

(* Keep the old public validity predicate explicit: these are precisely
   the two expression-termination obligations, not a big-step computation. *)
Definition oracle_state_observations_pre_def:
  oracle_state_observations_pre os rqs <=>
    cont_pre (eval_expr_cps empty_evaluation_context
      (Call NoneT (Send F)
        [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE)
      (empty_state with <|outcomes := os; requests := rqs|>) DoneK) /\
    cont_pre (eval_expr_cps empty_evaluation_context
      (Call NoneT (ExtCall T F ("unused", [], NoneT) []) [] NONE)
      (empty_state with <|outcomes := os; requests := rqs|>) DoneK)
End

Theorem oracle_state_observations_pre[cv_pre]:
  oracle_state_observations_pre os rqs
Proof
  simp[oracle_state_observations_pre_def, cont_pre_eval_expr_cps]
QED

(* Preserve the original Hol_reln exports as explicit derived claims.
   The registered CPS validity rewrite makes translation unconditional, but
   does not remove the old constructor premise from these public schemas.
   The historical ind and strongind coincide because there is no recursive
   occurrence of this predicate in its sole constructor premise. *)
(* Local parsing name for the raw record constructor used by Hol_reln;
   record literals instead elaborate to updates of ARB. *)
val () = temp_overload_on ("OracleStateRecord",
  prim_mk_const {Thy = "vyperState", Name = "recordtype.evaluation_state"});
Theorem oracle_state_observations_pre_cases:
  !a0 a1.
    oracle_state_observations_pre a0 a1 <=>
    !v. v =
      (let v0 = empty_state in
        vyperState$evaluation_state_CASE v0 (\v1 v2 v3 v4 v5 v6 v7 v8.
          OracleStateRecord v1 v2 v3 v4 v5 v6 a0 a1)) ==>
      cont_pre (eval_expr_cps empty_evaluation_context
        (Call NoneT (Send F)
          [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
           Literal (BaseT (UintT 256)) (IntL 0)] NONE) v DoneK) /\
      cont_pre (eval_expr_cps empty_evaluation_context
        (Call NoneT (ExtCall T F ("unused", [], NoneT) []) [] NONE) v DoneK)
Proof
  Cases_on `empty_state` >>
  simp[oracle_state_observations_pre_def, evaluation_state_case_def,
       evaluation_state_fn_updates]
QED

Theorem oracle_state_observations_pre_rules:
  !os rqs.
    (!v. v =
      (let v0 = empty_state in
        vyperState$evaluation_state_CASE v0 (\v1 v2 v3 v4 v5 v6 v7 v8.
          OracleStateRecord v1 v2 v3 v4 v5 v6 os rqs)) ==>
      cont_pre (eval_expr_cps empty_evaluation_context
        (Call NoneT (Send F)
          [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
           Literal (BaseT (UintT 256)) (IntL 0)] NONE) v DoneK) /\
      cont_pre (eval_expr_cps empty_evaluation_context
        (Call NoneT (ExtCall T F ("unused", [], NoneT) []) [] NONE) v DoneK)) ==>
    oracle_state_observations_pre os rqs
Proof
  simp[oracle_state_observations_pre_cases]
QED

Theorem oracle_state_observations_pre_ind:
  !P.
    (!os rqs.
      (!v. v =
        (let v0 = empty_state in
          vyperState$evaluation_state_CASE v0 (\v1 v2 v3 v4 v5 v6 v7 v8.
            OracleStateRecord v1 v2 v3 v4 v5 v6 os rqs)) ==>
        cont_pre (eval_expr_cps empty_evaluation_context
          (Call NoneT (Send F)
            [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
             Literal (BaseT (UintT 256)) (IntL 0)] NONE) v DoneK) /\
        cont_pre (eval_expr_cps empty_evaluation_context
          (Call NoneT (ExtCall T F ("unused", [], NoneT) []) [] NONE) v DoneK)) ==>
      P os rqs) ==>
    !a0 a1. oracle_state_observations_pre a0 a1 ==> P a0 a1
Proof
  simp[oracle_state_observations_pre_cases]
QED

Theorem oracle_state_observations_pre_strongind:
  !P.
    (!os rqs.
      (!v. v =
        (let v0 = empty_state in
          vyperState$evaluation_state_CASE v0 (\v1 v2 v3 v4 v5 v6 v7 v8.
            OracleStateRecord v1 v2 v3 v4 v5 v6 os rqs)) ==>
        cont_pre (eval_expr_cps empty_evaluation_context
          (Call NoneT (Send F)
            [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
             Literal (BaseT (UintT 256)) (IntL 0)] NONE) v DoneK) /\
        cont_pre (eval_expr_cps empty_evaluation_context
          (Call NoneT (ExtCall T F ("unused", [], NoneT) []) [] NONE) v DoneK)) ==>
      P os rqs) ==>
    !a0 a1. oracle_state_observations_pre a0 a1 ==> P a0 a1
Proof
  simp[oracle_state_observations_pre_cases]
QED

(* Original pre-activation claim, falsified by the closed actual zero Send
   counterexample saved in vyperSendModesTest before this amendment.
Theorem oracle_state_inert_eval:
  oracle_state_smoke os rqs
Proof
  EVAL_TAC >> simp[return_def, transfer_value_def]
QED
*)
(* Isolate the concrete EVM computation from the source evaluator and its
   arbitrary bookkeeping. STOP on empty code changes no state: in particular
   neither transaction parameters nor transient storage need to be concrete. *)
Theorem oracle_empty_call_context_count:
  LENGTH (make_ext_call_state caller callee code calldata value_opt gas
    accounts tStorage txParams).contexts = 1
Proof
  simp[make_ext_call_state_def]
QED

Theorem oracle_empty_call_step:
  vfmExecution$step
    (make_ext_call_state 0w 0w [] [] (SOME 0) 0
       empty_accounts tStorage txParams) =
  (INR NONE,
    make_ext_call_state 0w 0w [] [] (SOME 0) 0
      empty_accounts tStorage txParams)
Proof
  EVAL_TAC
QED

Theorem oracle_empty_call_run:
  vfmExecution$run_call
    (make_ext_call_state 0w 0w [] [] (SOME 0) 0
       empty_accounts tStorage txParams) =
  SOME (INR NONE,
    make_ext_call_state 0w 0w [] [] (SOME 0) 0
      empty_accounts tStorage txParams)
Proof
  simp[Once vfmExecutionTheory.run_call_def] >>
  simp[Once OWHILE_THM, oracle_empty_call_context_count,
       oracle_empty_call_step] >>
  simp[Once OWHILE_THM]
QED

Theorem oracle_empty_call_precheck:
  ext_call_value_transfer_ok 0w 0w (SOME 0) empty_accounts /\
  (lookup_account (0w:address) empty_accounts).code = [] /\
  ~fIN (0w:address) precompile_addresses
Proof
  EVAL_TAC >> simp[MEM_fset_REP, fIN_fset_ABS] >> EVAL_TAC
QED

Theorem oracle_empty_run_ext_call:
  run_ext_call 0w 0w [] (SOME 0) 0 empty_accounts tStorage txParams =
    SOME (T, [], empty_accounts, tStorage, [])
Proof
  simp[run_ext_call_def, oracle_empty_call_precheck, oracle_empty_call_run] >>
  EVAL_TAC >> simp[]
QED

Theorem oracle_zero_send_operands:
  dest_AddressV (BytesV (REPLICATE 20 0w)) = SOME 0w /\
  dest_NumV (IntV 0) = SOME 0
Proof
  CONV_TAC cv_eval
QED

(* Only accounts/outcomes matter here. All other fields, including arbitrary
   scopes, logs, requests and transient storage, are preserved as a record. *)
Theorem oracle_zero_send_inert:
  st.outcomes = NONE /\ st.accounts = empty_accounts ==>
  eval_expr empty_evaluation_context
    (Call NoneT (Send F)
      [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
       Literal (BaseT (UintT 256)) (IntL 0)] NONE) st =
    (INL (Value NoneV), st)
Proof
  strip_tac >>
  simp[evaluate_def, evaluate_literal_def, read_result_def,
       type_check_def, assert_def, bind_def, ignore_bind_def, return_def] >>
  simp[eval_send_def, oracle_zero_send_operands, ext_call_kwarg_def,
       forwarded_gas_def, lift_option_type_def, get_accounts_def,
       get_transient_storage_def, type_check_def, assert_def,
       bind_def, ignore_bind_def, return_def] >>
  simp[empty_evaluation_context_def, empty_call_txn_def,
       oracle_empty_run_ext_call] >>
  simp[lift_option_def, check_def, assert_def, bind_def, ignore_bind_def,
       update_accounts_def, update_transient_def, append_logs_def,
       return_def, evaluation_state_component_equality]
QED

Theorem oracle_empty_extcall_inert:
  eval_expr cx
    (Call ty (ExtCall static_call skip_check (name, args, ret) opts) [] dflt) st =
    (INR (Error (TypeError "ExtCall operands")), st)
Proof
  simp[evaluate_def, read_results_def, eval_ext_call_def,
       bind_def, return_def, raise_def]
QED

Theorem oracle_state_inert_eval:
  os = NONE ==> oracle_state_smoke os rqs
Proof
  strip_tac >> gvs[oracle_state_smoke_def] >> conj_tac
  >- (irule oracle_zero_send_inert >> simp[empty_state_def]) >>
  simp[oracle_empty_extcall_inert]
QED

Theorem oracle_state_none_cv:
  oracle_state_observations NONE []
Proof
  CONV_TAC cv_eval
QED

(* Original false expectations retained; neither selected fixture was dropped.
(* Empty SOME must not activate outcome consumption in this task, and a
 * failing outcome must not change today's successful zero-value Send. *)
Theorem oracle_state_some_cv:
  oracle_state_observations (SOME []) [] /\
  oracle_state_observations (SOME [extCallOracle$failed_outcome
    <|cr_kind := MessageCall; cr_gas := NONE; cr_data_len := 0; cr_target := 0w; cr_value := 0; cr_data := []; cr_static := F;
      cr_accounts := empty_accounts; cr_tStorage := empty_transient_storage|>])
    [<|cr_kind := MessageCall; cr_gas := NONE; cr_data_len := 0; cr_target := 0w; cr_value := 0; cr_data := []; cr_static := F;
       cr_accounts := empty_accounts; cr_tStorage := empty_transient_storage|>]
Proof
  CONV_TAC cv_eval
QED
*)
(* The same two fixtures now fail Send. Direct CPS snapshots in
   vyperSendCpsCVTest additionally certify the consumed suffix/requests. *)
Theorem oracle_state_some_cv:
  ~oracle_state_observations (SOME []) [] /\
  ~oracle_state_observations (SOME [extCallOracle$failed_outcome
    <|cr_kind := MessageCall; cr_gas := NONE; cr_data_len := 0; cr_target := 0w; cr_value := 0; cr_data := []; cr_static := F;
      cr_accounts := empty_accounts; cr_tStorage := empty_transient_storage|>])
    [<|cr_kind := MessageCall; cr_gas := NONE; cr_data_len := 0; cr_target := 0w; cr_value := 0; cr_data := []; cr_static := F;
       cr_accounts := empty_accounts; cr_tStorage := empty_transient_storage|>]
Proof
  CONV_TAC cv_eval
QED
