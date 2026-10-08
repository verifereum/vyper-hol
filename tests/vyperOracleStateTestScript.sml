(* TASK025 record migration only: both modes are still inert. These checks
 * exercise the complete state, including nonempty shared-oracle values.
 * No oracle-taking entry API or evaluator clause is introduced here. *)
Theory vyperOracleStateTest
Ancestors
  arithmetic integer words list option finite_map cv_type While vyperAST vyperValue vyperContext
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
      (Call NoneT Send
        [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE) st =
      (INL (Value NoneV), st) /\
    eval_expr empty_evaluation_context
      (Call NoneT (ExtCall T ("unused", [], NoneT)) [] NONE) st =
      (INR (Error (TypeError "ExtCall no target")), st)
End
(* CV cannot translate equality on function-valued account/storage records.
 * Check whole-state equality above by kernel reduction, and translate the
 * result projections separately through the migrated monadic representation. *)
Definition oracle_state_observations_def:
  oracle_state_observations os rqs =
  let st = empty_state with <|outcomes := os; requests := rqs|> in
    FST (eval_expr empty_evaluation_context
      (Call NoneT Send
        [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE) st) =
      INL (Value NoneV) /\
    FST (eval_expr empty_evaluation_context
      (Call NoneT (ExtCall T ("unused", [], NoneT)) [] NONE) st) =
      INR (Error (TypeError "ExtCall no target"))
End
val oracle_state_observations_pre_def = oracle_state_observations_def
  |> SRULE [eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "oracle_state_observations_pre";

Theorem oracle_state_observations_pre[cv_pre]:
  oracle_state_observations_pre os rqs
Proof
  rw[oracle_state_observations_pre_def, cont_pre_IS_SOME_cont] >>
  qmatch_goalsub_abbrev_tac `eval_expr_cps cx ee ss DoneK` >>
  qspecl_then [`cx`, `ee`, `ss`, `DoneK`] mp_tac (cj 8 eval_cps_eq) >>
  Cases_on `eval_expr cx ee ss` >>
  rename1 `eval_expr cx ee ss = (res, st1)` >> Cases_on `res` >> simp[] >>
  disch_then (fn th => REWRITE_TAC [th]) >>
  simp[cont_def, Once OWHILE_THM, nextk_def]
QED

Theorem oracle_state_inert_eval:
  oracle_state_smoke os rqs
Proof
  EVAL_TAC >> simp[return_def, transfer_value_def]
QED

Theorem oracle_state_none_cv:
  oracle_state_observations NONE []
Proof
  CONV_TAC cv_eval
QED

(* Empty SOME must not activate outcome consumption in this task, and a
 * failing outcome must not change today's successful zero-value Send. *)
Theorem oracle_state_some_cv:
  oracle_state_observations (SOME []) [] /\
  oracle_state_observations (SOME [extCallOracle$failed_outcome
    <|cr_target := 0w; cr_value := 0; cr_data := []; cr_static := F;
      cr_accounts := empty_accounts; cr_tStorage := empty_transient_storage|>])
    [<|cr_target := 0w; cr_value := 0; cr_data := []; cr_static := F;
       cr_accounts := empty_accounts; cr_tStorage := empty_transient_storage|>]
Proof
  CONV_TAC cv_eval
QED
