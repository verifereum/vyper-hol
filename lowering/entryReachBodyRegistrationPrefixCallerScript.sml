Theory entryReachBodyRegistrationPrefixCaller
Ancestors
  loweringStateRelDefs entryReachBodyCallerResources entryReachBodyRuntimeResources
  entryReachBodyRegistrationPrefixSupport entryReachBodyRegistrationPrefixValues
  fragExec compileVyper venomWf venomInst compileEnv finite_map words list arithmetic

Theorem caller_runtime_empty_prefix_support_gas:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  compile_entry_checks min_cds pay st = ((),last) /\
  initial_venom_state_rel tops am tx initial /\ vars_pc_only initial s /\
  fresh_vars_wrt st s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  min_cds <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  last.cs_next_var <= limit.cs_next_var ==>
  !exec_fn. fn_has_code st last exec_fn /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. (vars_pc_only s t /\ fresh_vars_wrt limit t /\
      t.vs_allocas = FEMPTY /\ t.vs_alloca_next = 0 /\
      alloca_inv t /\ abi_alloca_history (fn_insts fn) t /\
      alloca_frontier_inv unit.cu_context fn site t /\
      (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < last.cs_next_id)) /\
    ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    (!fuel r. run_from fuel unit.cu_context exec_fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' unit.cu_context exec_fn s = r) /\
    gas_path unit.cu_context exec_fn s 0 (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  drule_all caller_runtime_entry_integrity >> strip_tac >>
  drule caller_runtime_entry >> disch_then (assume_tac o CONJUNCT1) >>
  drule caller_checks_empty_prefix_gas >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `vars_pc_only _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `lookup_function _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`site`, `limit`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[]
QED

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
  disch_then (map_every assume_tac o CONJUNCTS) >> rw[frag_exec_def] >>
  drule caller_runtime_empty_prefix_support_gas >>
  disch_then (drule_at (Pat `lookup_function _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `compile_entry_checks _ _ _ = _`)) >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `vars_pc_only _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`site`, `limit`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[] >> metis_tac[]
QED
