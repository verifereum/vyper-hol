(* Executable source/CPS regressions for raw system calls and EIP-6780. *)
Theory vyperSystemHaltTest
Ancestors
  vyperInterpreter vyperSmallStep vyperContext vyperState vyperAST vyperValue
  vfmState vfmExecution finite_map list option While
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
