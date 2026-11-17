(* Ordinary CALL-prefix operations preserve the checked-frame observation. *)
Theory stackBoundCallPrefix
Ancestors
  stackBoundCallObs vfmExecution

Theorem sb_call_prefix_get_current_context[local]:
  sb_call_prefix get_current_context
Proof
  rw[sb_call_prefix_def,get_current_context_def,return_def,fail_def] >>
  gvs[]
QED

Theorem sb_call_prefix_get_accounts[simp]:
  sb_call_prefix get_accounts
Proof
  simp[sb_call_prefix_def,get_accounts_def,return_def]
QED

Theorem sb_call_prefix_get_num_contexts[simp]:
  sb_call_prefix get_num_contexts
Proof
  simp[sb_call_prefix_def,get_num_contexts_def,return_def]
QED

Theorem sb_call_prefix_get_gas_left[simp]:
  sb_call_prefix get_gas_left
Proof
  rewrite_tac[get_gas_left_def] >> irule sb_call_prefix_bind >>
  simp[sb_call_prefix_get_current_context]
QED

Theorem sb_call_prefix_get_callee[simp]:
  sb_call_prefix get_callee
Proof
  rewrite_tac[get_callee_def] >> irule sb_call_prefix_bind >>
  simp[sb_call_prefix_get_current_context]
QED

Theorem sb_call_prefix_memory_expansion_info[simp]:
  !offset size. sb_call_prefix (memory_expansion_info offset size)
Proof
  rpt gen_tac >> rewrite_tac[memory_expansion_info_def] >>
  irule sb_call_prefix_bind >>
  simp[sb_call_prefix_get_current_context]
QED

Theorem sb_call_prefix_expand_memory[simp]:
  sb_call_prefix (expand_memory n)
Proof
  rw[sb_call_prefix_def,expand_memory_def,bind_def,
     get_current_context_def,set_current_context_def,return_def,fail_def] >>
  Cases_on `s.contexts` >>
  gvs[sb_call_obs_def,sb_call_context_obs_def,AllCaseEqs()]
QED

Theorem sb_call_prefix_consume_gas[simp]:
  sb_call_prefix (consume_gas n)
Proof
  rw[sb_call_prefix_def,consume_gas_def,bind_def,ignore_bind_def,
     get_current_context_def,set_current_context_def,assert_def,return_def,fail_def] >>
  Cases_on `s.contexts` >>
  gvs[sb_call_obs_def,sb_call_context_obs_def,AllCaseEqs()]
QED

Theorem sb_call_prefix_assert_not_static[simp]:
  sb_call_prefix assert_not_static
Proof
  rw[sb_call_prefix_def,assert_not_static_def,get_static_def,bind_def,
     get_current_context_def,assert_def,return_def,fail_def] >>
  gvs[AllCaseEqs()]
QED

Theorem sb_call_prefix_access_address[simp]:
  sb_call_prefix (access_address a)
Proof
  rw[sb_call_prefix_def,access_address_def,domain_check_def,
     set_domain_def,ignore_bind_def,bind_def,return_def,fail_def] >>
  Cases_on `s.msdomain` >>
  gvs[sb_call_obs_def,AllCaseEqs()]
QED
