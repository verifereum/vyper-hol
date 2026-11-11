Theory entryReachBodyInitialResources
Ancestors
  loweringStateRelDefs vyperLoweringCorrect actualEntryAllocationFrame abiAllocationHistory
  venomMemProps allocaFrontierBound moduleLoweringProps entryChecksProps fragExec
  fcgCorrectnessProof fcgPostorder fcgDefs allocaBudgetProps venomInstProofs1
  venomWf contextCodegenRel relation pred_set venomInst venomExecProofs
  vyperCompiler arithmetic

(* vars_pc_only is equality after replacing precisely four PC/variable
   fields.  In particular the allocation frontier is not replaced. *)
Theorem entry_vars_pc_only_frontier:
  vars_pc_only s t ==> t.vs_alloca_next = s.vs_alloca_next
Proof
  rw[vars_pc_only_def] >> pop_assum (SUBST1_TAC o SYM) >> simp[]
QED

Theorem entry_initial_allocation_resources:
  initial_venom_state_rel tops am tx s ==>
  s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0 /\
  alloca_inv s /\ abi_alloca_history code s
Proof
  strip_tac >>
  `s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0` by
    fs[initial_venom_state_rel_def] >>
  simp[] >> metis_tac[alloca_inv_empty, abi_alloca_history_empty]
QED

(* This applies to the very post-dispatch state exported by
   external_entry_reaches_checks, without choosing a second endpoint. *)
Theorem entry_checks_start_allocation_resources:
  initial_venom_state_rel tops am tx s /\ vars_pc_only s t ==>
  t.vs_allocas = FEMPTY /\ t.vs_alloca_next = 0 /\
  alloca_inv t /\ abi_alloca_history code t
Proof
  strip_tac >>
  drule entry_initial_allocation_resources >>
  drule vars_pc_only_allocas >>
  drule entry_vars_pc_only_frontier >> rpt strip_tac >>
  simp[] >> metis_tac[alloca_inv_empty, abi_alloca_history_empty]
QED

Theorem entry_checks_pass_allocation_resources_gas:
  compile_entry_checks min_cds pay st = ((),st') /\
  initial_venom_state_rel tops am tx initial /\ vars_pc_only initial s /\
  fresh_vars_wrt st s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  min_cds <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  !fn. fn_has_code st st' fn /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. (vars_pc_only s t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = FEMPTY /\ t.vs_alloca_next = 0 /\
      alloca_inv t /\ abi_alloca_history code t) /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r) /\
    gas_path ctx fn s 0 (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  drule compile_entry_checks_pass_gas >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspecl_then [`ctx`, `fn`] mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  drule_all vars_pc_only_trans >> disch_tac >>
  drule_all entry_checks_start_allocation_resources >> simp[]
QED

Theorem entry_checks_pass_allocation_resources:
  compile_entry_checks min_cds pay st = ((),st') /\
  initial_venom_state_rel tops am tx initial /\ vars_pc_only initial s /\
  fresh_vars_wrt st s /\
  (pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
  min_cds <= LENGTH s.vs_call_ctx.cc_calldata /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  frag_exec ctx st st' (\u. u = s)
    (\t. vars_pc_only s t /\ fresh_vars_wrt st' t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = FEMPTY /\ t.vs_alloca_next = 0 /\
      alloca_inv t /\ abi_alloca_history code t)
    (\r. F)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rw[frag_exec_def] >>
  drule entry_checks_pass_allocation_resources_gas >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `vars_pc_only _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (qspecl_then [`ctx`, `code`, `fn`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem entry_root_zero_frontier:
  ctx_wf ctx /\ wf_invoke_targets ctx /\ reachable_call_graph_acyclic ctx /\
  ctx.ctx_entry = SOME name /\
  venomInst$lookup_function name ctx.ctx_functions = SOME fn /\
  s.vs_alloca_next = 0 ==> alloca_frontier_inv ctx fn inst s
Proof
  strip_tac >>
  `fn.fn_name = name` by metis_tac[lookup_function_result_name] >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fcg_is_reachable (fcg_analyze ctx) name` by
    (irule fcg_analyze_reachable_complete_proof >>
     simp[fcg_path_def, ctx_fn_names_def] >>
     metis_tac[lookup_function_mem]) >>
  simp[alloca_frontier_inv_def] >> conj_tac
  >- (rpt strip_tac >>
      `fcg_is_reachable (fcg_analyze ctx) g` by
        metis_tac[reachable_fcg_acyclic_tc_rank,
                  reachable_call_graph_acyclic_def] >>
      metis_tac[reachable_fcg_acyclic_no_reachable_cycle,
                reachable_call_graph_acyclic_def]) >>
  drule remaining_alloca_budget_frame >>
  disch_then (qspec_then `s` assume_tac) >>
  mp_tac (Q.INST [`a` |-> `name`] call_targets_card) >>
  simp_tac bool_ss [unit_alloca_budget_def, LET_THM] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `b * frame + r <= (1 + n) * frame` >>
  `b * frame <= n * frame` by (irule LESS_MONO_MULT >> simp[Abbr `b`, Abbr `n`]) >>
  `r <= frame` by simp[Abbr `r`, Abbr `frame`] >>
  simp_tac bool_ss [RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac
QED

Theorem entry_checks_root_frontier:
  ctx_wf ctx /\ wf_invoke_targets ctx /\ reachable_call_graph_acyclic ctx /\
  ctx.ctx_entry = SOME name /\
  venomInst$lookup_function name ctx.ctx_functions = SOME fn /\
  initial_venom_state_rel tops am tx initial /\ vars_pc_only initial t ==>
  alloca_frontier_inv ctx fn inst t
Proof
  strip_tac >> irule entry_root_zero_frontier >>
  goal_assum $ drule_at Any >> simp[] >>
  drule entry_vars_pc_only_frontier >>
  fs[initial_venom_state_rel_def]
QED
