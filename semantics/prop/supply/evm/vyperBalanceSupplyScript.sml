(* TOP-LEVEL: supply_action_step_self_destruct.
 * Helpers: full-balance transfer, zeroing and deletion-queue composition.
 *)
Theory vyperBalanceSupply
Ancestors
  vyperExecutionSupply vyperPrecompileSupply vyperPrimitiveSupply
  vyperOpcodeSupply vfmStaticCalls vfmPreserves vfmExecution vfmContext
  vfmState list

Theorem cp_result_supply:
  cp action /\ action st = (result,post) /\ supply_state budget st ==>
  supply_state budget post /\ post.rollback.accounts = st.rollback.accounts
Proof
  simp[cp_def] >> strip_tac >>
  first_x_assum (qspecl_then [`st`, `result`, `post`] mp_tac) >>
  gvs[supply_state_def] >> strip_tac >>
  Cases_on `st.contexts` >> gvs[execution_supply_bound_def]
QED

Theorem supply_action_result:
  supply_action budget action /\ action st = (result,post) /\
  supply_state budget st ==>
  supply_state budget post
Proof
  rw[supply_action_def, preserves_when_def] >> first_x_assum irule >>
  qexistsl_tac [`result`, `st`] >> simp[]
QED

Theorem supply_state_full_transfer:
  supply_state budget st ==>
  supply_state budget
    (SND (vfmExecution$update_accounts
      (vfmExecution$transfer_value sender recipient
        (lookup_account sender st.rollback.accounts).balance) st))
Proof
  simp[supply_state_def, vfmExecutionTheory.update_accounts_def,
       vfmExecutionTheory.return_def, execution_supply_bound_def] >>
  strip_tac >> irule account_supply_bound_transfer >> simp[]
QED

Theorem supply_action_zero_account_balance:
  account.balance = 0 ==>
  supply_action budget
    (vfmExecution$update_accounts (update_account address account))
Proof
  rw[supply_action_def, preserves_when_def, supply_state_def,
     vfmExecutionTheory.update_accounts_def, vfmExecutionTheory.return_def] >>
  gvs[execution_supply_bound_def] >>
  irule account_supply_bound_install >> simp[]
QED

(* The prefix may consume gas or fail, but preserves the account snapshot
   whose balance determines the full transfer. *)
Theorem supply_action_full_transfer:
  (!accounts. cp (prefix accounts)) /\
  (!accounts. supply_action budget (tail accounts)) ==>
  supply_action budget
    (vfmExecution$bind get_accounts (\accounts.
      vfmExecution$ignore_bind (prefix accounts)
        (vfmExecution$ignore_bind
          (vfmExecution$update_accounts
            (vfmExecution$transfer_value sender recipient
              (lookup_account sender accounts).balance))
          (tail accounts))))
Proof
  strip_tac >>
  simp[supply_action_def, preserves_when_def, get_accounts_def,
       vfmExecutionTheory.bind_def, vfmExecutionTheory.ignore_bind_def,
       vfmExecutionTheory.return_def, vfmExecutionTheory.update_accounts_def] >>
  qx_genl_tac [`before`, `outcome`, `after`] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `!accounts. cp _`
    (qspec_then `before.rollback.accounts` assume_tac) >>
  drule_all cp_result_supply >> strip_tac >> gvs[] >>
  rename1 `prefix before.rollback.accounts before = (INL value,mid)` >>
  `supply_state budget
     (SND (vfmExecution$update_accounts
       (vfmExecution$transfer_value sender recipient
         (lookup_account sender mid.rollback.accounts).balance) mid))` by
    (irule supply_state_full_transfer >> simp[]) >>
  gvs[vfmExecutionTheory.update_accounts_def, vfmExecutionTheory.return_def] >>
  qpat_x_assum `!accounts. supply_action _ _`
    (qspec_then `before.rollback.accounts` assume_tac) >>
  drule_all supply_action_result >> simp[]
QED

Theorem supply_action_add_to_delete:
  supply_action budget (add_to_delete address)
Proof
  rw[supply_action_def, preserves_when_def, supply_state_def,
     add_to_delete_def, vfmExecutionTheory.return_def,
     execution_supply_bound_def]
QED

Theorem ignore_bind_assoc:
  vfmExecution$ignore_bind (vfmExecution$ignore_bind first second) third =
  vfmExecution$ignore_bind first (vfmExecution$ignore_bind second third)
Proof
  simp[vfmExecutionTheory.ignore_bind_def, vfmExecutionPropTheory.bind_assoc]
QED

val balance_supply_tac = rpt (FIRST [
  irule supply_action_cp >> simp[] >> NO_TAC,
  irule supply_action_bind >> conj_tac,
  irule supply_action_ignore_bind >> conj_tac,
  irule supply_action_cond >> conj_tac,
  irule supply_action_zero_account_balance >> simp[] >> NO_TAC,
  irule supply_action_add_to_delete,
  gen_tac >> BETA_TAC]);

Theorem supply_action_step_self_destruct:
  supply_action budget step_self_destruct
Proof
  simp[step_self_destruct_def] >>
  irule supply_action_bind >> reverse conj_tac
  >- (irule supply_action_cp >> simp[]) >>
  qx_gen_tac `args` >> BETA_TAC >>
  irule supply_action_bind >> reverse conj_tac
  >- (irule supply_action_cp >> simp[]) >>
  qx_gen_tac `access_cost` >> BETA_TAC >>
  irule supply_action_bind >> reverse conj_tac
  >- (irule supply_action_cp >> simp[]) >>
  qx_gen_tac `sender` >> BETA_TAC >>
  irule supply_action_ignore_bind >> conj_tac
  >- (irule supply_action_cp >> simp[]) >>
  ONCE_REWRITE_TAC [GSYM ignore_bind_assoc] >>
  ho_match_mp_tac supply_action_full_transfer >> conj_tac
  >- simp[] >>
  gen_tac >> BETA_TAC >> balance_supply_tac
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperBalanceSupply");
