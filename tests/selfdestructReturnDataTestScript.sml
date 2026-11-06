Theory selfdestructReturnDataTest
Ancestors
  venomExecSemantics venomInst venomState asmSem vfmExecution vfmState list
Libs
  wordsLib

(* A funded executing account and a distinct funded beneficiary. *)
Definition selfdestruct_test_accounts_def:
  selfdestruct_test_accounts =
    update_account 1w (empty_account_state with balance := 7)
      (update_account 2w (empty_account_state with balance := 11) empty_accounts)
End

Definition selfdestruct_test_context_def:
  selfdestruct_test_context created =
    empty_call_context with <| cc_address := 1w; cc_created_in_tx := created |>
End

val selfdestruct_test_ss =
  [selfdestruct_test_accounts_def, selfdestruct_test_context_def,
   empty_call_context_def, empty_account_state_def, empty_accounts_def,
   lookup_account_def, update_account_def, transfer_value_def,
   WORD_EVAL_CONV ``(w2w (1w : bytes32) : address)``,
   WORD_EVAL_CONV ``(w2w (2w : bytes32) : address)``,
   combinTheory.APPLY_UPDATE_THM,
   WORD_EVAL_CONV ``(1w : address) = 2w``,
   WORD_EVAL_CONV ``(2w : address) = 1w``,
   mk_inst_def, eval_operand_def, halt_state_def, set_returndata_def];

Theorem venom_selfdestruct_created_self_burns_and_queues_deletion:
  !s. ?t.
    step_inst_base (mk_inst 0 SELFDESTRUCT [Lit 1w] [])
      (s with <| vs_accounts := selfdestruct_test_accounts;
                 vs_call_ctx := selfdestruct_test_context T;
                 vs_pending_deletions := [9w] |>) = Halt t /\
    (lookup_account 1w t.vs_accounts).balance = 0 /\
    (lookup_account 2w t.vs_accounts).balance = 11 /\
    t.vs_pending_deletions = [1w; 9w]
Proof
  simp ([Once step_inst_base_def] @ selfdestruct_test_ss)
QED

Theorem venom_selfdestruct_existing_self_keeps_balance:
  !s. ?t.
    step_inst_base (mk_inst 0 SELFDESTRUCT [Lit 1w] [])
      (s with <| vs_accounts := selfdestruct_test_accounts;
                 vs_call_ctx := selfdestruct_test_context F;
                 vs_pending_deletions := [9w] |>) = Halt t /\
    (lookup_account 1w t.vs_accounts).balance = 7 /\
    t.vs_pending_deletions = [9w]
Proof
  simp ([Once step_inst_base_def] @ selfdestruct_test_ss)
QED

Theorem venom_selfdestruct_existing_transfers_without_deletion:
  !s. ?t.
    step_inst_base (mk_inst 0 SELFDESTRUCT [Lit 2w] [])
      (s with <| vs_accounts := selfdestruct_test_accounts;
                 vs_call_ctx := selfdestruct_test_context F;
                 vs_pending_deletions := [9w] |>) = Halt t /\
    (lookup_account 1w t.vs_accounts).balance = 0 /\
    (lookup_account 2w t.vs_accounts).balance = 18 /\
    t.vs_pending_deletions = [9w]
Proof
  simp ([Once step_inst_base_def] @ selfdestruct_test_ss)
QED

Theorem asm_selfdestruct_created_self_burns_and_queues_deletion:
  !s. ?t.
    asm_selfdestruct
      (s with <| as_stack := [1w]; as_accounts := selfdestruct_test_accounts;
                 as_call_ctx := selfdestruct_test_context T;
                 as_pending_deletions := [9w] |>) = AsmHalt t /\
    (lookup_account 1w t.as_accounts).balance = 0 /\
    (lookup_account 2w t.as_accounts).balance = 11 /\
    t.as_pending_deletions = [1w; 9w]
Proof
  simp ([asm_selfdestruct_def] @ selfdestruct_test_ss)
QED

Theorem asm_selfdestruct_existing_self_keeps_balance:
  !s. ?t.
    asm_selfdestruct
      (s with <| as_stack := [1w]; as_accounts := selfdestruct_test_accounts;
                 as_call_ctx := selfdestruct_test_context F;
                 as_pending_deletions := [9w] |>) = AsmHalt t /\
    (lookup_account 1w t.as_accounts).balance = 7 /\
    t.as_pending_deletions = [9w]
Proof
  simp ([asm_selfdestruct_def] @ selfdestruct_test_ss)
QED

Theorem asm_selfdestruct_existing_transfers_without_deletion:
  !s. ?t.
    asm_selfdestruct
      (s with <| as_stack := [2w]; as_accounts := selfdestruct_test_accounts;
                 as_call_ctx := selfdestruct_test_context F;
                 as_pending_deletions := [9w] |>) = AsmHalt t /\
    (lookup_account 1w t.as_accounts).balance = 0 /\
    (lookup_account 2w t.as_accounts).balance = 18 /\
    t.as_pending_deletions = [9w]
Proof
  simp ([asm_selfdestruct_def] @ selfdestruct_test_ss)
QED

Theorem venom_selfdestruct_clears_old_return_data:
  !s.
    ~s.vs_call_ctx.cc_static ==>
    ?t.
      step_inst_base (mk_inst 0 SELFDESTRUCT [Lit 0w] [])
        (s with vs_returndata := [1w]) = Halt t /\
      t.vs_returndata = []
Proof
  rpt strip_tac >>
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def,
       halt_state_def, set_returndata_def]
QED

Theorem asm_selfdestruct_clears_old_return_data:
  !s.
    ?t.
      asm_selfdestruct
        (s with <|as_stack := [0w]; as_returndata := [1w]|>) = AsmHalt t /\
      t.as_returndata = []
Proof
  simp[asm_selfdestruct_def]
QED
