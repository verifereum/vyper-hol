Theory entryBodyRegistrationComposition
Ancestors
  entryReachBodyCanonicalChecks entryReachBodyRegistrationIteration
  entryChecksProps externalEntryChecks compileVyper compileEnv
  moduleLoweringProps vyperLoweringCorrect vyperInterpreter vyperState
  e2eDefs abiDecoderCorrect abiDecoderCounters
  entryReachBodyRegistrationInitialization entryBodyEndpointStructure
  entryRegistrationOpen words list

Theorem entry_successful_value[local]:
  send_call_value mut cx st = (INL (),es) ==>
  mut = Payable \/ cx.txn.value = 0
Proof
  Cases_on `mut = Payable` >> simp[] >>
  Cases_on `cx.txn.value = 0` >> simp[] >>
  simp[send_call_value_def, check_def, assert_def,
       ignore_bind_def, bind_def, return_def]
QED

Theorem entry_selected_check_premises:
  source_typing_ok tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\ vars_pc_only vs s /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE) st = (INL (),es) /\
  set_external_package_target target
    (package_external_fn tops F keys
      (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) ==>
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  mincd <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  LENGTH tx.args = LENGTH args
Proof
  strip_tac >>
  drule entry_successful_value >>
  simp[initial_evaluation_context_def] >> strip_tac >>
  drule vars_pc_only_fields >> strip_tac >>
  `pay = (mut = Payable)` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[set_external_package_target_def, package_external_fn_def, LET_THM] >>
     rpt strip_tac >> gvs[]) >>
  `mincd <= LENGTH vs.vs_call_ctx.cc_calldata` by
    (qabbrev_tac `pkg = package_external_fn tops F keys
      (mut,F,raw,tx.function_name,args,([]:expr list),ret,fbody)` >>
     PairCases_on `pkg` >> fs[markerTheory.Abbrev_def] >>
     qpat_x_assum `(_,_,_,_,_,_,_,_,_,_,_) = package_external_fn _ _ _ _`
       (assume_tac o SYM) >>
     gvs[set_external_package_target_def] >>
     drule_all valid_vyper_call_min_calldata_size >> simp[]) >>
  drule_all initial_venom_state_calldata_length >> strip_tac >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, call_ctx_rel_def,
      valid_vyper_call_def]
QED

Theorem entry_canonical_registration_reached:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) ==>
  ?lbl ce pos mincd pay key ut iv rt fn start cenv registered final site t.
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
         tx.function_name,args,([]:expr list),ret,fbody)) =
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_inst_ids_distinct fn /\
    compile_register_positional_args ce pos 4 start = (cenv,registered) /\
    ~block_is_terminated start /\ ~block_is_terminated registered /\
    local_ptrs_reserved cenv registered /\
    compile_guarded_body cenv F key ut iv fbody rt registered = ((),final) /\
    fn_has_code start final fn /\ fn_has_code registered final fn /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts fn)) /\
    entry_prefix_witness fn (type_env tops) args tx.args (LENGTH args) cenv registered t /\
    alloca_inv t /\ alloca_frontier_inv unit.cu_context fn site t /\
    abi_alloca_history (fn_insts fn) t /\ fresh_vars_wrt final t /\
    (!id r. FLOOKUP t.vs_allocas id = SOME r ==> id < registered.cs_next_id) /\
    entry_loop_fields vs t /\ ~t.vs_halted /\
    t.vs_current_bb = registered.cs_current_bb /\
    t.vs_inst_idx = LENGTH registered.cs_current_insts /\ cenv.ce_is_ctor = F /\
    (!fuel r. run_from fuel unit.cu_context fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
  strip_tac >> drule_all entry_canonical_checks_reached >> strip_tac >>
  drule_all registration_preserves_open >> strip_tac >>
  drule_all targeted_external_entry_locals >> strip_tac >>
  drule_all entry_selected_check_premises >> strip_tac >>
  `start.cs_next_var <= body_end.cs_next_var` by
    (drule compile_register_positional_args_next_var >> strip_tac >>
     metis_tac[compile_guarded_body_vars_mono, abi_decoder_vars_mono_def,
               pairTheory.SND, arithmeticTheory.LESS_EQ_TRANS]) >>
  `?u. entry_prefix_witness func (type_env tops) args tx.args 0 ce start u /\
    fresh_vars_wrt body_end u /\ alloca_inv u /\
    abi_alloca_history (fn_insts func) u /\
    alloca_frontier_inv unit.cu_context func (ARB:instruction) u /\
    (!id r. FLOOKUP u.vs_allocas id = SOME r ==> id < start.cs_next_id) /\
    entry_loop_fields vs u /\ ~u.vs_halted /\
    u.vs_current_bb = start.cs_current_bb /\
    u.vs_inst_idx = LENGTH start.cs_current_insts /\
    (!fuel r. run_from fuel unit.cu_context func u = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' unit.cu_context func s = r)` by
    (irule entry_registration_initial_endpoint >>
     qpat_assum `compile_entry_checks _ _ _ = _` (irule_at Any) >>
     qpat_assum `lower_vyper_runtime_unit _ _ = _` (irule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all entry_registration_full_run >> strip_tac >>
  qexistsl_tac [`lbl`,`ce`,`pos`,`mincd`,`pay`,`key`,`ut`,`iv`,`rt`,`func`,
    `start`,`cenv`,`registered`,`body_end`,`ARB:instruction`,`t`] >>
  simp[] >> metis_tac[]
QED
