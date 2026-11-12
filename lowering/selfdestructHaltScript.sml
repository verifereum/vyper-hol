(* selfdestruct's balance moves keep the source and Venom accounts in
   agreement: the transfer to the beneficiary, then EIP-6780's zeroing of
   an account created in the transaction. *)
Theory selfdestructHalt
Ancestors
  loweringStateRelDefs accountsRelProps vyperInterpreter vyperState
  vyperValue venomState venomInst venomExecSemantics vfmExecution vfmState
  combin
Libs
  monadsyntax

Theorem accounts_agree_target_balance:
  !cx a1 a2.
    accounts_agree cx a1 a2 ==>
    (a1 cx.txn.target).balance = (a2 cx.txn.target).balance
Proof
  rw[accounts_agree_def] >>
  qpat_x_assum `_ with storage := _ = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem accounts_agree_lookup_balance:
  !cx a1 a2 addr.
    accounts_agree cx a1 a2 ==>
    (lookup_account addr a1).balance = (lookup_account addr a2).balance
Proof
  rw[lookup_account_def] >> Cases_on `addr = cx.txn.target`
  >- metis_tac[accounts_agree_target_balance] >>
  gvs[accounts_agree_def]
QED

(* Changing the balance of any account keeps the agreement when both
   sides change it alike. *)
Theorem accounts_agree_balance_update:
  !cx a1 a2 addr f.
    accounts_agree cx a1 a2 ==>
    accounts_agree cx
      (update_account addr (lookup_account addr a1 with balance updated_by f) a1)
      (update_account addr (lookup_account addr a2 with balance updated_by f) a2)
Proof
  rw[accounts_agree_def, update_account_def, lookup_account_def,
     APPLY_UPDATE_THM] >>
  rw[] >> gvs[] >>
  qpat_x_assum `_ with storage := _ = _` (SUBST1_TAC o SYM) >> simp[]
QED

Theorem accounts_agree_transfer_value:
  !cx a1 a2 fr to v.
    accounts_agree cx a1 a2 ==>
    accounts_agree cx (vfmExecution$transfer_value fr to v a1)
                      (vfmExecution$transfer_value fr to v a2)
Proof
  rw[vfmExecutionTheory.transfer_value_def] >> fs[] >>
  `!a. lookup_account to a =
       lookup_account to
         (update_account fr
            (lookup_account fr a with balance updated_by flip $- v) a)` by
    simp[lookup_account_def, update_account_def, APPLY_UPDATE_THM] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  rpt (irule accounts_agree_balance_update) >> simp[]
QED

(* EIP-6780's zeroing of the running account. *)
Theorem accounts_agree_zero_balance:
  !cx a1 a2 addr.
    accounts_agree cx a1 a2 ==>
    accounts_agree cx
      (update_account addr (lookup_account addr a1 with balance := 0) a1)
      (update_account addr (lookup_account addr a2 with balance := 0) a2)
Proof
  rpt strip_tac >>
  drule accounts_agree_balance_update >>
  disch_then (qspecl_then [`addr`, `K 0`] mp_tac) >> simp[]
QED

(* The value transfer moves balances only. *)
Theorem lookup_transfer_value_with_balance[simp]:
  !x fr to v a b.
    lookup_account x (vfmExecution$transfer_value fr to v a) with balance := b =
    lookup_account x a with balance := b
Proof
  rw[vfmExecutionTheory.transfer_value_def, lookup_account_def,
     update_account_def, APPLY_UPDATE_THM] >> rw[]
QED

(* ===== Source ===== *)

(* What eval_expr runs for selfdestruct once its operand is a value. *)
Definition selfdestruct_tail_def:
  selfdestruct_tail cx v = do
    target_addr <- lift_option_type (dest_AddressV v) "selfdestruct target";
    check_not_static cx;
    accounts <- get_accounts;
    self <<- cx.txn.target;
    balance <<- (lookup_account self accounts).balance;
    vyperInterpreter$transfer_value self target_addr balance;
    if cx.txn.created_in_tx then do
      update_accounts (\acc. update_account self
        (lookup_account self acc with balance := 0) acc);
      update_pending_deletions (CONS self)
    od else return ();
    raise HaltException
  od
End

Theorem eval_selfdestruct_action:
  !cx ann e dflt.
    eval_expr cx (Call ann SelfDestructTarget [e] dflt) =
    vyperState$bind (vyperState$bind (eval_expr cx e) (read_result cx))
      (selfdestruct_tail cx)
Proof
  rw[FUN_EQ_THM] >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[selfdestruct_tail_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def, vyperStateTheory.raise_def] >>
  rpt (CASE_TAC >> gvs[])
QED

(* The recipient's balance overflows: the source's only error once the
   operand is an address outside a static call. *)
Definition selfdestruct_overflows_def:
  selfdestruct_overflows cx a (accts:evm_accounts) <=>
    let bal = (lookup_account cx.txn.target accts).balance in
      bal <> 0 /\ cx.txn.target <> a /\
      2 ** 256 <= (lookup_account a accts).balance + bal
End

(* The tail never yields a value: it raises HaltException or an error. *)
Theorem selfdestruct_tail_raises:
  !cx v st. ?ex st'.
    selfdestruct_tail cx v st = (INR ex : eval_result + exception, st')
Proof
  rw[selfdestruct_tail_def,
     vyperInterpreterTheory.transfer_value_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
     vyperStateTheory.lift_option_type_def, vyperStateTheory.check_not_static_def, vyperStateTheory.check_def, vyperStateTheory.assert_def,
     vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def, vyperStateTheory.update_pending_deletions_def,
     vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Theorem selfdestruct_tail_overflow:
  !cx v a st.
    dest_AddressV v = SOME a /\ ~cx.txn.is_static /\
    selfdestruct_overflows cx a st.accounts ==>
    selfdestruct_tail cx v st =
      (INR (Error (RuntimeError "transfer_value recipient overflow")), st)
Proof
  rw[selfdestruct_tail_def, selfdestruct_overflows_def,
     vyperInterpreterTheory.transfer_value_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
     vyperStateTheory.lift_option_type_def, vyperStateTheory.check_not_static_def, vyperStateTheory.check_def, vyperStateTheory.assert_def,
     vyperStateTheory.get_accounts_def, vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

(* The source state after a selfdestruct that halts. *)
Definition selfdestruct_final_def:
  selfdestruct_final cx a (st:evaluation_state) =
    st with <|
      accounts :=
        (let tr = vfmExecution$transfer_value cx.txn.target a
                    (lookup_account cx.txn.target st.accounts).balance
                    st.accounts in
         if cx.txn.created_in_tx then
           update_account cx.txn.target
             (lookup_account cx.txn.target st.accounts with balance := 0) tr
         else tr);
      pending_deletions :=
        if cx.txn.created_in_tx then cx.txn.target :: st.pending_deletions
        else st.pending_deletions |>
End

Theorem selfdestruct_final_fields[simp]:
  (!cx a st g. selfdestruct_final cx a (st with gas_obs := g) =
               selfdestruct_final cx a st with gas_obs := g) /\
  (!cx a st. (selfdestruct_final cx a st).logs = st.logs) /\
  (!cx a st. (selfdestruct_final cx a st).requests = st.requests)
Proof
  simp[selfdestruct_final_def]
QED

Theorem selfdestruct_tail_halt:
  !cx v a st.
    dest_AddressV v = SOME a /\ ~cx.txn.is_static /\
    ~selfdestruct_overflows cx a st.accounts ==>
    selfdestruct_tail cx v st =
      (INR HaltException : eval_result + exception, selfdestruct_final cx a st)
Proof
  rw[selfdestruct_tail_def, selfdestruct_overflows_def, selfdestruct_final_def,
     vyperInterpreterTheory.transfer_value_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
     vyperStateTheory.lift_option_type_def, vyperStateTheory.check_not_static_def, vyperStateTheory.check_def, vyperStateTheory.assert_def,
     vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def, vyperStateTheory.update_pending_deletions_def,
     vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  gvs[vyperStateTheory.evaluation_state_component_equality,
      vfmExecutionTheory.transfer_value_def, update_account_def,
      lookup_account_def, FUN_EQ_THM, APPLY_UPDATE_THM] >>
  rw[] >> gvs[]
QED

Theorem eval_selfdestruct_overflow:
  !cx e es v ee a ann dflt.
    vyperState$bind (eval_expr cx e) (read_result cx) es = (INL v, ee) /\
    dest_AddressV v = SOME a /\ ~cx.txn.is_static /\
    selfdestruct_overflows cx a ee.accounts ==>
    eval_expr cx (Call ann SelfDestructTarget [e] dflt) es =
      (INR (Error (RuntimeError "transfer_value recipient overflow")), ee)
Proof
  rpt strip_tac >> rewrite_tac[eval_selfdestruct_action] >>
  ONCE_REWRITE_TAC[vyperStateTheory.bind_def] >> asm_rewrite_tac[] >> simp[] >>
  irule selfdestruct_tail_overflow >> simp[]
QED

(* ===== Agreement at the halt ===== *)

(* The source and Venom selfdestructs from halt-related states halt in
   halt-related states. *)
Theorem selfdestruct_halt_rel:
  !cx vs ss a.
    halt_rel cx vs ss /\ ss.vs_call_ctx.cc_address = cx.txn.target /\
    ss.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx ==>
    halt_rel cx (selfdestruct_final cx a vs)
      (halt_state (set_returndata []
        (ss with <|
           vs_accounts :=
             (let self = ss.vs_call_ctx.cc_address in
              let tr = vfmExecution$transfer_value self a
                         (lookup_account self ss.vs_accounts).balance
                         ss.vs_accounts in
              if ss.vs_call_ctx.cc_created_in_tx then
                update_account self
                  (lookup_account self ss.vs_accounts with balance := 0) tr
              else tr);
           vs_pending_deletions :=
             if ss.vs_call_ctx.cc_created_in_tx then
               ss.vs_call_ctx.cc_address :: ss.vs_pending_deletions
             else ss.vs_pending_deletions |>)))
Proof
  rw[selfdestruct_final_def, halt_rel_def, accounts_rel_def, halt_state_def,
     set_returndata_def] >>
  `(lookup_account cx.txn.target vs.accounts).balance =
   (lookup_account cx.txn.target ss.vs_accounts).balance` by
    metis_tac[accounts_agree_lookup_balance] >>
  pop_assum SUBST_ALL_TAC >>
  `accounts_agree cx
     (vfmExecution$transfer_value cx.txn.target a
        (lookup_account cx.txn.target ss.vs_accounts).balance vs.accounts)
     (vfmExecution$transfer_value cx.txn.target a
        (lookup_account cx.txn.target ss.vs_accounts).balance ss.vs_accounts)` by
    metis_tac[accounts_agree_transfer_value] >>
  rw[] >>
  `!x b. lookup_account x b with balance := 0 =
         lookup_account x (vfmExecution$transfer_value cx.txn.target a
           (lookup_account cx.txn.target ss.vs_accounts).balance b)
           with balance := 0` by simp[] >>
  metis_tac[accounts_agree_zero_balance]
QED

(* Venom's SELFDESTRUCT outside a static call halts with empty returndata,
   halt-related to the source's halt. *)
Theorem step_selfdestruct_halt_rel:
  !cx vs s op aw id.
    halt_rel cx vs s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    s.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
    ~s.vs_call_ctx.cc_static /\ eval_operand op s = SOME aw ==>
    ?s'. step_inst_base (mk_inst id SELFDESTRUCT [op] []) s = Halt s' /\
         s'.vs_returndata = [] /\
         halt_rel cx (selfdestruct_final cx (w2w aw) vs) s'
Proof
  rpt strip_tac >>
  drule_all selfdestruct_halt_rel >>
  disch_then (qspec_then `w2w aw` assume_tac) >>
  simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def] >>
  gvs[LET_THM, halt_state_def, set_returndata_def]
QED
