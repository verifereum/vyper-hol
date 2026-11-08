(* Operational registration initialization after the selected entry checks. *)
Theory entryReachBodyRegistrationInitialization
Ancestors
  loweringStateRelDefs entryReachBodyRegistrationPrefixCaller entryReachBodyRegistrationSlotWitness
  entryReachBodyExactArrayLoop stmtSimDecl moduleLoweringProps
  fragExec compileVyper compileEnv finite_map words list arithmetic

Theorem entry_checks_loop_fields[local]:
  vars_pc_only s t ==> entry_loop_fields s t
Proof
  simp[vars_pc_only_def, entry_loop_fields_def] >> strip_tac >>
  gvs[venomStateTheory.venom_state_component_equality]
QED

Theorem entry_registration_initial_endpoint:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  compile_entry_checks min_cds pay st = ((),last) /\
  initial_venom_state_rel tops am tx initial /\ vars_pc_only initial s /\
  fresh_vars_wrt st s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  min_cds <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  last.cs_next_var <= limit.cs_next_var /\
  fn_has_code st last fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ LENGTH values = LENGTH args ==>
  ?t. entry_prefix_witness fn env args values 0 ce last t /\
    fresh_vars_wrt limit t /\ alloca_inv t /\
    abi_alloca_history (fn_insts fn) t /\
    alloca_frontier_inv unit.cu_context fn site t /\
    (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < last.cs_next_id) /\
    entry_loop_fields initial t /\ ~t.vs_halted /\
    t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    (!fuel r. run_from fuel unit.cu_context fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' unit.cu_context fn s = r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all caller_runtime_empty_prefix_support >>
  disch_then (qspec_then `site` assume_tac) >>
  drule frag_exec_no_exit_run >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >> strip_tac >>
  `vars_pc_only initial t` by metis_tac[vars_pc_only_trans] >>
  drule entry_checks_loop_fields >> disch_tac >>
  qexists_tac `t` >> simp[entry_prefix_witness_empty]
QED
