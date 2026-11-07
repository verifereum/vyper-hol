Theory entryReachBodyRegistrationPrefixCaller
Ancestors
  entryReachBodyCallerResources entryReachBodyRuntimeResources
  entryReachBodyRegistrationPrefixSupport entryReachBodyRegistrationPrefixValues
  fragExec compileVyper venomWf venomInst compileEnv finite_map words list arithmetic

Theorem caller_runtime_empty_prefix_support:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  compile_entry_checks min_cds pay st = ((),last) /\
  initial_venom_state_rel tops am tx initial /\ vars_pc_only initial s /\
  fresh_vars_wrt st s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  min_cds <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  last.cs_next_var <= limit.cs_next_var ==>
  frag_exec unit.cu_context st last (\u. u = s)
    (\t. vars_pc_only s t /\ fresh_vars_wrt limit t /\
      t.vs_allocas = FEMPTY /\ t.vs_alloca_next = 0 /\
      alloca_inv t /\ abi_alloca_history (fn_insts fn) t /\
      alloca_frontier_inv unit.cu_context fn site t /\
      (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < last.cs_next_id))
    (\r. F)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all caller_runtime_entry_integrity >> strip_tac >>
  drule caller_runtime_entry >> disch_then (assume_tac o CONJUNCT1) >>
  drule_all caller_checks_empty_prefix >>
  disch_then (qspecl_then [`site`] mp_tac) >>
  disch_tac >> irule frag_exec_conseq >> goal_assum (drule_at Any) >>
  simp[]
QED
