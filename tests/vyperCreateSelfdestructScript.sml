Theory vyperCreateSelfdestruct
Ancestors
  vyperCreate vyperInterpreter vyperContext vfmExecution vfmState finite_set
Libs
  wordsLib

(* Constructor SELFDESTRUCT must see an empty original account even though the
   live account has already received its nonce-one creation prelude. *)
Definition constructor_selfdestruct_state_def:
  constructor_selfdestruct_state =
    let accounts = create_prelude_accounts (1w:address) (2w:address) 0
      empty_accounts in
    let start = make_create_state (1w:address) (2w:address) [] 0
      accounts empty_transient_storage [] (vyper_to_tx_params empty_call_txn) in
    start with contexts :=
      [(FST (HD start.contexts) with stack := [3w], SND (HD start.contexts))]
End

Theorem constructor_original_empty:
  account_empty (lookup_account (2w:address)
    (SND (HD constructor_selfdestruct_state.contexts)).accounts) /\
  (lookup_account (2w:address) constructor_selfdestruct_state.rollback.accounts).nonce = 1
Proof
  EVAL_TAC >> simp[]
QED

Theorem constructor_selfdestruct_deferred:
  case step_self_destruct constructor_selfdestruct_state of
  | (INR NONE, finished) =>
      MEM (2w:address) finished.rollback.toDelete /\
      (lookup_account (2w:address) finished.rollback.accounts).nonce = 1 /\
      account_empty (lookup_account (2w:address)
        (process_deletions finished.rollback.toDelete finished.rollback.accounts))
  | _ => F
Proof
  EVAL_TAC >> simp[MEM_fset_REP, fIN_fset_ABS] >>
  EVAL_TAC >> simp[MEM_fset_REP, fIN_fset_ABS]
QED

Theorem constructor_transaction_commit:
  case step_self_destruct constructor_selfdestruct_state of
  | (INR NONE, finished) =>
      let am = initial_machine_state with
        <|accounts := finished.rollback.accounts;
          pending_deletions := finished.rollback.toDelete|> in
      (finalize_pending_deletions am).pending_deletions = [] /\
      account_empty (lookup_account (2w:address)
        (finalize_pending_deletions am).accounts)
  | _ => F
Proof
  mp_tac constructor_selfdestruct_deferred >>
  simp[vyperInterpreterTheory.finalize_pending_deletions_def,
       AllCaseEqs()] >>
  Cases_on `step_self_destruct constructor_selfdestruct_state` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y` >> gvs[]
QED
