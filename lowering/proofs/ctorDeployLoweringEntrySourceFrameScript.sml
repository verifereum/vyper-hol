Theory ctorDeployLoweringEntrySourceFrame
Ancestors
 ctorDeployLoweringDefs ctorDeployLoweringEntryTransport
 vyperInterpreter vyperState e2eDeployDefs finite_map list

Theorem deploy_ctor_send_value_frame:
 send_call_value mut cx s = (INL (),t) ==>
 t = (s with accounts := t.accounts)
Proof
 simp[send_call_value_def, transfer_value_def, COND_RATOR,
      bind_def, ignore_bind_def, return_def, lift_option_def,
      get_accounts_def, update_accounts_def, check_def, assert_def, raise_def] >>
 rpt strip_tac >> gvs[AllCaseEqs(), combinTheory.o_DEF,
   evaluation_state_component_equality]
QED

Theorem deploy_ctor_module_constants_frame:
 !mods am am'. evaluate_module_constants cx am addr mods = SOME am' ==>
 am' = (am with immutables := am'.immutables)
Proof
 Induct >- simp[evaluate_module_constants_def] >>
 PairCases >> rpt gen_tac >>
 simp[evaluate_module_constants_def, AllCaseEqs()] >> strip_tac >>
 first_x_assum drule >> simp[merge_constants_def] >>
 strip_tac >> gvs[]
QED

Theorem deploy_ctor_all_constants_frame:
 evaluate_all_constants cx am addr mods = SOME am' ==>
 am' = (am with immutables := am'.immutables)
Proof
 simp[evaluate_all_constants_def] >>
 metis_tac[deploy_ctor_module_constants_frame]
QED

Theorem deploy_ctor_source_start_fields:
 !tops am tx mut body am_c es0 args scope.
 deploy_ctor_start tops am tx (mut,F,body,am_c,es0) /\
 lookup_function NONE tx.function_name Deploy tops =
   SOME (mut,F,args,[],NoneT,body) /\
 bind_arguments (type_env tops) args tx.args = SOME scope ==>
 es0.scopes = [scope] /\
 es0.tStorage = am.tStorage /\ es0.logs = am.logs /\
 es0.requests = [] /\ es0.pending_deletions = am.pending_deletions /\
 es0.immutables = am_c.immutables /\ es0.outcomes = NONE /\
 send_call_value mut (deploy_evaluation_context tops am tx)
   (initial_state am_c [scope]) = (INL (),es0) /\
 am_c.accounts = am.accounts
Proof
 rpt gen_tac >> strip_tac >>
 gvs[deploy_ctor_start_def, deploy_ctor_singleton_type_env,
     lock_if_nr_def, ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
 drule deploy_ctor_send_value_frame >>
 drule deploy_ctor_all_constants_frame >>
 simp[initial_state_def] >>
 rpt strip_tac >>
 fs[evaluation_state_component_equality, abstract_machine_component_equality,
    initial_state_def]
QED

Theorem deploy_ctor_send_value_accounts:
 send_call_value mut cx s = (INL (),t) ==>
 t.accounts =
 (if cx.txn.value = 0 \/ cx.txn.sender = cx.txn.target then s.accounts
  else update_account cx.txn.sender
    (lookup_account cx.txn.sender s.accounts with
       balance updated_by (flip $- cx.txn.value))
    (update_account cx.txn.target
      (lookup_account cx.txn.target s.accounts with
         balance updated_by ($+ cx.txn.value)) s.accounts))
Proof
 simp[send_call_value_def, transfer_value_def, COND_RATOR,
      bind_def, ignore_bind_def, return_def, lift_option_def,
      get_accounts_def, update_accounts_def, check_def, assert_def, raise_def] >>
 rpt strip_tac >> gvs[AllCaseEqs(), combinTheory.o_DEF]
QED

Theorem deploy_ctor_source_start_accounts:
 !tops am tx mut body am_c es0 args scope.
 deploy_ctor_start tops am tx (mut,F,body,am_c,es0) /\
 lookup_function NONE tx.function_name Deploy tops =
   SOME (mut,F,args,[],NoneT,body) /\
 bind_arguments (type_env tops) args tx.args = SOME scope ==>
 es0.accounts =
 (if tx.value = 0 \/ tx.sender = tx.target then am.accounts
  else update_account tx.sender
    (lookup_account tx.sender am.accounts with
       balance updated_by (flip $- tx.value))
    (update_account tx.target
      (lookup_account tx.target am.accounts with
         balance updated_by ($+ tx.value)) am.accounts))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all deploy_ctor_source_start_fields >> strip_tac >>
 drule deploy_ctor_send_value_accounts >>
 simp[initial_state_def, deploy_evaluation_context_def, initial_evaluation_context_def]
QED
