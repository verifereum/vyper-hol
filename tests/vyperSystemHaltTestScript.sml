(* Executable source/CPS regressions for raw system calls and EIP-6780. *)
Theory vyperSystemHaltTest
Ancestors
  vyperInterpreter vyperSmallStep vyperContext vyperState vyperAST vyperValue
  vfmState vfmExecution finite_map list option pair While
  vyperCallOutcome extCallOracle venomCallOracleDefs asmSem callTrace vfmContext
Libs cv_transLib wordsLib

Definition system_address_def:
  system_address a = Literal (BaseT AddressT)
    (BytesL (word_to_bytes (a:address) T))
End
val () = cv_auto_trans system_address_def;

Definition system_context_def:
  system_context created = empty_evaluation_context with txn :=
    empty_call_txn with <|target := 11w; created_in_tx := created|>
End
val () = cv_auto_trans system_context_def;

Definition system_state_def:
  system_state = empty_state with
    <|accounts := update_account 11w
        (empty_account_state with <|balance := 17; nonce := 1; code := [0w];
          storage := update_storage 7w 9w empty_storage|>)
        (update_account 12w (empty_account_state with balance := 5) empty_accounts);
      scopes := [FEMPTY]; pending_deletions := [14w]|>
End
val () = cv_auto_trans system_state_def;

Definition system_destroy_def:
  system_destroy target = Call NoneT SelfDestructTarget [system_address target] NONE
End
val () = cv_auto_trans system_destroy_def;

Definition system_expr_run_def:
  system_expr_run cx e st = fromtvk (cont (eval_expr_cps cx e st DoneK))
End
val () = cv_auto_trans system_expr_run_def;

Definition system_stmts_run_def:
  system_stmts_run cx ss st = fromk (cont (eval_stmts_cps cx ss st DoneK))
End
val () = cv_auto_trans system_stmts_run_def;

Definition system_destroy_observation_def:
  system_destroy_observation created target own_balance target_balance pending =
    let r = system_expr_run (system_context created) (system_destroy target) system_state in
    eval_expr (system_context created) (system_destroy target) system_state = r /\
    FST r = INR HaltException /\
    let st = SND r in
    (lookup_account 11w st.accounts).balance = own_balance /\
    (lookup_account target st.accounts).balance = target_balance /\
    (lookup_account 11w st.accounts).nonce = 1 /\
    (lookup_account 11w st.accounts).code = [0w] /\
    lookup_storage 7w (lookup_account 11w st.accounts).storage = 9w /\
    st.pending_deletions = pending /\ st.scopes = [FEMPTY]
End
val () = system_destroy_observation_def
  |> SRULE [eval_expr_eq_cont_cps, GSYM system_expr_run_def] |> cv_auto_trans;

Theorem selfdestruct_existing_transfers_without_deleting:
  system_destroy_observation F 12w 0 22 [14w]
Proof
  CONV_TAC cv_eval
QED

Theorem selfdestruct_created_transfers_and_defers_deletion:
  system_destroy_observation T 12w 0 22 [11w;14w]
Proof
  CONV_TAC cv_eval
QED

Theorem selfdestruct_to_self_burns_only_when_created:
  system_destroy_observation F 11w 17 17 [14w] /\
  system_destroy_observation T 11w 0 0 [11w;14w]
Proof
  CONV_TAC cv_eval
QED

(* A statement after the branch would fail if execution continued. *)
Definition system_branch_observation_def:
  system_branch_observation =
    let ss = [If (Literal (BaseT BoolT) (BoolL T))
                [Expr (system_destroy 12w)] [];
              Assert (Literal (BaseT BoolT) (BoolL F)) AssertUnreachable] in
    let r = system_stmts_run (system_context F) ss system_state in
    eval_stmts (system_context F) ss system_state = r /\
    FST r = INR HaltException /\
    (lookup_account 12w (SND r).accounts).balance = 22 /\
    (SND r).scopes = [FEMPTY]
End
val () = system_branch_observation_def
  |> SRULE [eval_stmts_eq_cont_cps, GSYM system_stmts_run_def] |> cv_auto_trans;

Theorem selfdestruct_branch_stops_following_statements:
  system_branch_observation
Proof
  CONV_TAC cv_eval
QED

Definition system_revert_observation_def:
  system_revert_observation bytes =
    let e = Call NoneT RawRevert
      [Literal (BaseT (BytesT (Dynamic (LENGTH bytes)))) (BytesL bytes)] NONE in
    let r = system_expr_run (system_context F) e system_state in
    eval_expr (system_context F) e system_state = r /\
    FST r = INR (Error (RevertData bytes)) /\
    (lookup_account 11w (SND r).accounts).balance = 17 /\
    (SND r).pending_deletions = [14w]
End
val () = system_revert_observation_def
  |> SRULE [eval_expr_eq_cont_cps, GSYM system_expr_run_def] |> cv_auto_trans;

Theorem raw_revert_keeps_exact_empty_and_nonempty_data:
  system_revert_observation [] /\ system_revert_observation [0w;0xdew;0xadw;0w]
Proof
  CONV_TAC cv_eval
QED

Definition system_set_counter_def:
  system_set_counter n = Assign (BaseTarget (TopLevelNameTarget (NONE,"counter")))
    (Literal (BaseT (UintT 256)) (IntL n))
End
val () = cv_auto_trans system_set_counter_def;

Definition system_program_def:
  system_program =
    [VariableDecl Private Storage "counter" (BaseT (UintT 256)) (SOME 7);
     FunctionDecl Internal Nonpayable F F "die" [] [] NoneT
       [system_set_counter 10; Expr (system_destroy 12w); system_set_counter 99];
     FunctionDecl External Nonpayable T F "foo" [] [] (BaseT (UintT 256))
       [Expr (Call NoneT (IntCall (NONE,"die")) [] NONE);
        system_set_counter 99;
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 7)))]]
End
val () = cv_auto_trans system_program_def;

Definition system_machine_def:
  system_machine = initial_machine_state with
    <|accounts := system_state.accounts;
      sources := [(11w, [(NONE, system_program)])];
      layouts := [(11w, ([((NONE,"counter"),7)],
                         [((NONE,"$.nonreentrant_key"),3)]))]|>
End
val () = cv_auto_trans system_machine_def;

Definition system_external_halt_observation_def:
  system_external_halt_observation orc =
    let r = call_external orc system_machine
      (empty_call_txn with <|target := 11w; function_name := "foo"|>) in
    FST r = INR HaltException /\
    let am = FST (SND r) in
    (lookup_account 11w am.accounts).balance = 0 /\
    (lookup_account 12w am.accounts).balance = 22 /\
    (lookup_account 11w am.accounts).code = [0w] /\
    lookup_storage 7w (lookup_account 11w am.accounts).storage = 10w /\
    lookup_storage 3w (lookup_transient_storage 11w am.tStorage) = 1w /\
    am.pending_deletions = [] /\ SND (SND r) = []
End
val () = cv_auto_trans system_external_halt_observation_def;

Theorem internal_selfdestruct_commits_storage_and_keeps_external_lock:
  system_external_halt_observation NONE /\
  system_external_halt_observation (SOME [])
Proof
  CONV_TAC cv_eval
QED

Definition system_constructor_observation_def:
  system_constructor_observation target own_balance target_balance =
    let prog = [FunctionDecl Deploy Payable F F "__init__" [] [] NoneT
      [Expr (system_destroy target);
       Assert (Literal (BaseT BoolT) (BoolL F)) AssertUnreachable]] in
    let am = initial_machine_state with accounts :=
      update_account 11w (empty_account_state with balance := 17)
        (update_account 12w (empty_account_state with balance := 5) empty_accounts) in
    case load_contract NONE am
      (empty_call_txn with <|target := 11w; function_name := "__init__"|>)
      [(NONE,prog)] [] of
    | INR _ => F
    | INL (final,rqs) =>
        (lookup_account 11w final.accounts).balance = own_balance /\
        (lookup_account target final.accounts).balance = target_balance /\
        account_empty (lookup_account 11w final.accounts) /\
        final.pending_deletions = [] /\ ALOOKUP final.sources 11w = NONE /\ rqs = []
End
val () = cv_auto_trans system_constructor_observation_def;

Theorem constructor_selfdestruct_deletes_without_installing_runtime_sources:
  system_constructor_observation 12w 0 22 /\
  system_constructor_observation 11w 0 0
Proof
  CONV_TAC cv_eval
QED

(* Deferred callee deletions, adoption and rollback. *)
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
