Theory loadElimFinalIntegration
Ancestors
  loadElimFiveRoundExecution loadElimIterationReadiness loadElimResultComposition
  loadElimReachableSSA loadElimBPEmpty loadElimSentinelHelpers
  loadElimMemoryRel loadElimPaddedNoncall passSharedProps
  loadElimDefs loadElimKeyShapeInvariant loadElimRoundNames list pred_set

Theorem le_function_rounds_ready:
  le_iteration_ready fn fn [] /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
  le_iteration_ready fn (le_function_rounds fn)
    [CALLDATALOAD; DLOAD; SLOAD; TLOAD; MLOAD]
Proof
  strip_tac >>
  pure_rewrite_tac[le_function_rounds_def, le_calldata_round_def] >>
  irule le_iteration_ready_config_step >>
  simp[calldataload_config_def, le_data_round_ready] >>
  gvs[le_iteration_ready_def]
QED

Theorem le_function_padded_run:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  EVERY (\i. i.inst_opcode <> MEMTOP) (fn_insts fn) /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  (!v. bp_get_ptrs (bp_analyze (cfg_analyze fn) fn) v = []) /\
  s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  le_prefix_run_sim fuel C s fn (load_elim_function fn)
Proof
  strip_tac >>
  `le_iteration_ready fn fn []` by simp[le_iteration_ready_initial] >>
  `wf_function (le_function_rounds fn)` by
    (drule_all le_function_rounds_ready >> simp[le_iteration_ready_def]) >>
  `le_prefix_run_sim fuel C s fn (le_function_rounds fn)` by
    (irule le_function_rounds_run >> simp[]) >>
  once_rewrite_tac[le_function_rounds_expansion] >>
  irule le_prefix_run_sim_trans >> qexists `le_function_rounds fn` >>
  simp[] >> pure_rewrite_tac[le_prefix_run_sim_def] >> disj2_tac >>
  irule le_exact_result_padded >> irule clear_nops_function_correct >> simp[]
QED
