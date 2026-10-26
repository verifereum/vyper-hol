(* Deferred callee deletions: shared adoption, source execution and rollback. *)
Theory vyperDeletionTransportTest
Ancestors
  vyperSystemHaltTest vyperInterpreter vyperSmallStep vyperCallOutcome
  extCallOracle venomCallOracleDefs asmSem callTrace
  vyperState vyperContext vyperAST vyperValue vfmState vfmExecution
  vfmContext finite_map list option pair
Libs cv_transLib wordsLib

Theorem adoption_deletion_prefix_all_stages:
  outcome.co_success /\ ~rq.cr_static /\
  take_outcome rq vs.vs_outcomes = (outcome,rest) /\
  take_outcome rq asm.as_outcomes = (outcome,rest) ==>
  (SND (adopt_call_outcome rq outcome st)).pending_deletions =
    outcome.co_toDelete ++ st.pending_deletions /\
  (SND (consume_call_outcome rq off ret_size vs)).vs_pending_deletions =
    outcome.co_toDelete ++ vs.vs_pending_deletions /\
  asm_consume_call_outcome rq off ret_size stk asm =
    AsmOK (asm_next (asm with <|
      as_stack := 1w :: stk; as_outcomes := rest;
      as_requests := record_request rq asm.as_requests;
      as_accounts := outcome.co_accounts; as_transient := outcome.co_tStorage;
      as_logs := asm.as_logs ++ outcome.co_logs;
      as_pending_deletions := outcome.co_toDelete ++ asm.as_pending_deletions;
      as_returndata := outcome.co_returnData;
      as_memory := TAKE off asm.as_memory ++ TAKE ret_size outcome.co_returnData ++
        DROP (off + LENGTH (TAKE ret_size outcome.co_returnData)) asm.as_memory |>))
Proof
  simp[adopt_call_outcome_equation, consume_call_outcome_def,
       asm_consume_call_outcome_def, adopt_outcome_def] >>
  rpt strip_tac >> simp[]
QED

Theorem static_and_failed_deletions_are_ignored:
  (rq.cr_static \/ ~outcome.co_success) /\
  take_outcome rq vs.vs_outcomes = (outcome,rest) ==>
  (SND (adopt_call_outcome rq outcome st)).pending_deletions = st.pending_deletions /\
  (SND (consume_call_outcome rq off ret_size vs)).vs_pending_deletions =
    vs.vs_pending_deletions
Proof
  rw[adopt_call_outcome_equation, consume_call_outcome_def, adopt_outcome_def]
QED

Definition deletion_outcome_def:
  deletion_outcome success =
    failed_outcome (call_outcome_request 31w [] (SOME 0) empty_state) with
      <|co_success := success; co_toDelete := [21w;22w]|>
End
val () = cv_auto_trans deletion_outcome_def;

Definition deletion_oracle_observation_def:
  deletion_oracle_observation success static =
    let e = if static then
      Call NoneT (ExtCall T T ("f",[],NoneT) []) [system_address 31w] NONE
    else Call NoneT (Send F)
      [system_address 31w; Literal (BaseT (UintT 256)) (IntL 0)] NONE in
    let st = empty_state with
      <|accounts := update_account 31w
          (empty_account_state with <|nonce := 1; code := [0w]|>) empty_accounts;
        outcomes := SOME [deletion_outcome success]; pending_deletions := [14w]|> in
    let r = system_expr_run (system_context F) e st in
    eval_expr (system_context F) e st = r /\
    (SND r).pending_deletions =
      (if success /\ ~static then [21w;22w;14w] else [14w]) /\
    (SND r).outcomes = SOME [] /\ LENGTH (SND r).requests = 1 /\
    (if success then FST r = INL (Value NoneV) else ISR (FST r))
End
val () = deletion_oracle_observation_def
  |> SRULE [eval_expr_eq_cont_cps, GSYM system_expr_run_def] |> cv_auto_trans;

Theorem source_send_and_static_call_deletion_adoption:
  deletion_oracle_observation T F /\ deletion_oracle_observation F F /\
  deletion_oracle_observation T T /\ deletion_oracle_observation F T
Proof
  CONV_TAC cv_eval
QED

(* PUSH3 initcode; MSTORE; CREATE(0,29,3). The initcode is PUSH1 13;
   SELFDESTRUCT. A reverting parent must discard the child's queued deletion. *)
Definition deletion_callee_code_def:
  deletion_callee_code reverts : byte list =
    [0x5fw;0x5fw;0xa0w;
     0x62w;0x60w;13w;0xffw;0x5fw;0x52w;
     0x60w;3w;0x60w;29w;0x5fw;0xf0w] ++
    (if reverts then [0x5fw;0x5fw;0xfdw] else [0w])
End
val () = cv_auto_trans deletion_callee_code_def;

Definition deletion_direct_state_def:
  deletion_direct_state reverts = system_state with
    accounts updated_by (update_account 42w
      (empty_account_state with
        <|balance := 5; nonce := 1; code := deletion_callee_code reverts|>))
End
val () = cv_auto_trans deletion_direct_state_def;

Definition deletion_direct_call_def:
  deletion_direct_call raw =
    if raw then
      Call NoneT (RawCallTarget
        <|rcf_max_outsize := 0; rcf_is_delegate := F;
          rcf_is_static := F; rcf_revert_on_failure := T|>)
        [system_address 42w;
         Literal (BaseT (BytesT (Dynamic 0))) (BytesL []);
         Literal (BaseT (UintT 256)) (IntL 0)] NONE
    else Call NoneT (ExtCall F T ("f",[],NoneT) [EKValue])
      [system_address 42w; Literal (BaseT (UintT 256)) (IntL 0)] NONE
End
val () = cv_auto_trans deletion_direct_call_def;

Definition deletion_direct_observation_def:
  deletion_direct_observation raw reverts =
    let e = deletion_direct_call raw in
    let r = system_expr_run (system_context F) e (deletion_direct_state reverts) in
    let st = SND r in
    let child = vfmContext$address_for_create 42w 1 in
    eval_expr (system_context F) e (deletion_direct_state reverts) = r /\
    st.pending_deletions = (if reverts then [14w] else [child;14w]) /\
    (lookup_account 42w st.accounts).nonce = (if reverts then 1 else 2) /\
    (lookup_account child st.accounts).nonce = (if reverts then 0 else 1) /\
    (if reverts then ISR (FST r) else FST r = INL (Value NoneV)) /\
    let committed = finalize_pending_deletions
      (initial_machine_state with
        <|accounts := st.accounts; pending_deletions := st.pending_deletions|>) in
    account_empty (lookup_account child committed.accounts) /\
    committed.pending_deletions = []
End
val () = deletion_direct_observation_def
  |> SRULE [eval_expr_eq_cont_cps, GSYM system_expr_run_def] |> cv_auto_trans;

Theorem direct_raw_and_external_calls_transport_constructor_deletions:
  deletion_direct_observation T F /\ deletion_direct_observation F F
Proof
  CONV_TAC cv_eval
QED

Theorem reverting_callee_discards_constructor_deletions:
  deletion_direct_observation T T /\ deletion_direct_observation F T
Proof
  CONV_TAC cv_eval
QED

(* Explicit gas is needed to run the recipient's CREATE: gas-less send
   forwards zero gas when the transferred value is zero. *)
Definition deletion_send_observation_def:
  deletion_send_observation reverts =
    let e = Call NoneT (Send T)
      [system_address 42w; Literal (BaseT (UintT 256)) (IntL 0);
       Literal (BaseT (UintT 256)) (IntL (&default_evm_gas_limit))] NONE in
    let r = system_expr_run (system_context F) e (deletion_direct_state reverts) in
    let st = SND r in
    let child = vfmContext$address_for_create 42w 1 in
    eval_expr (system_context F) e (deletion_direct_state reverts) = r /\
    st.pending_deletions = (if reverts then [14w] else [child;14w]) /\
    LENGTH st.logs = LENGTH system_state.logs + (if reverts then 0 else 1) /\
    (lookup_account 42w st.accounts).nonce = (if reverts then 1 else 2) /\
    (lookup_account child st.accounts).nonce = (if reverts then 0 else 1) /\
    FST r = (if reverts then INR (Error (RuntimeError "send failed"))
             else INL (Value NoneV))
End
val () = deletion_send_observation_def
  |> SRULE [eval_expr_eq_cont_cps, GSYM system_expr_run_def] |> cv_auto_trans;

Theorem direct_send_transports_successful_effects_and_discards_failed_effects:
  deletion_send_observation F /\ deletion_send_observation T
Proof
  CONV_TAC cv_eval
QED
