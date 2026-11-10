Theory loadElimFiveRoundExecution
Ancestors
  loadElimIterationReadiness loadElimRoundExecution loadElimResultComposition
  loadElimMemoryRel loadElimPaddedNoncall loadElimDefs
  loadElimKeyShapeInvariant loadElimRoundNames loadElimCoupledExecution list pred_set

Definition le_prefix_run_sim_def:
  le_prefix_run_sim fuel C s fn gn <=>
    (?e. run_blocks fuel C fn s = Error e) \/
    lift_result (le_padded_control {v | isPREFIX "$le_phi_" v})
      (padded_exec_equiv {v | isPREFIX "$le_phi_" v})
      (padded_exec_equiv {v | isPREFIX "$le_phi_" v})
      (run_blocks fuel C fn s) (run_blocks fuel C gn s)
End

Theorem le_prefix_run_sim_trans:
  le_prefix_run_sim fuel C s f g /\ le_prefix_run_sim fuel C s g h ==>
  le_prefix_run_sim fuel C s f h
Proof
  rewrite_tac[le_prefix_run_sim_def] >>
  MATCH_ACCEPT_TAC le_padded_result_or_error_trans
QED

Theorem le_iteration_run_step:
  wf_function original /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars original) /\
  le_iteration_ready original fn ops /\
  MEM config [memory_config; transient_config; storage_config;
              dload_config; calldataload_config] /\
  ~MEM config.lc_load ops /\
  ctx = mk_load_context bp aliases (dfg_build_function fn) config /\
  (!v. bp_get_ptrs bp v = []) /\ wf_alias_sets aliases /\
  fn_entry_label original = SOME s.vs_current_bb /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  le_prefix_run_sim fuel C s fn
    (load_elim_one ctx (cfg_analyze original) fn)
Proof
  strip_tac >>
  drule_all le_iteration_structural_requirements >> strip_tac >>
  pure_rewrite_tac[le_prefix_run_sim_def] >>
  `(?e. run_blocks fuel C fn s = Error e) \/
   lift_result
     (le_padded_control (load_elim_one_fresh ctx (cfg_analyze original) fn))
     (padded_exec_equiv (load_elim_one_fresh ctx (cfg_analyze original) fn))
     (padded_exec_equiv (load_elim_one_fresh ctx (cfg_analyze original) fn))
     (run_blocks fuel C fn s)
     (run_blocks fuel C (load_elim_one ctx (cfg_analyze original) fn) s)`
    suffices_by
      (strip_tac >- metis_tac[] >> disj2_tac >>
       irule le_padded_result_widen >> goal_assum (drule_at Any) >> simp[]) >>
  irule le_load_elim_one_run_structural >>
  simp[le_padded_control_def, padded_exec_equiv_refl] >> metis_tac[]
QED

Theorem le_iteration_config_run_step:
  wf_function original /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars original) /\
  le_iteration_ready original fn ops /\
  MEM config [memory_config; transient_config; storage_config;
              dload_config; calldataload_config] /\
  ~MEM config.lc_load ops /\
  (!v. bp_get_ptrs bp v = []) /\ wf_alias_sets aliases /\
  fn_entry_label original = SOME s.vs_current_bb /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  le_prefix_run_sim fuel C s fn
    (load_elim_one (mk_load_context bp aliases (dfg_build_function fn) config)
      (cfg_analyze original) fn)
Proof
  strip_tac >> irule le_iteration_run_step >> simp[] >>
  qexistsl [`aliases`, `bp`, `config`, `ops`] >> gvs[]
QED

Definition le_calldata_round_def:
  le_calldata_round bp ma ta sa fn = load_elim_one
    (mk_load_context bp ma (dfg_build_function (le_data_round bp ma ta sa fn))
      calldataload_config)
    (cfg_analyze fn) (le_data_round bp ma ta sa fn)
End

Theorem le_five_rounds_run:
  le_iteration_ready fn fn [] /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  (!v. bp_get_ptrs bp v = []) /\
  wf_alias_sets ma /\ wf_alias_sets ta /\ wf_alias_sets sa /\
  fn_entry_label fn = SOME s.vs_current_bb /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  le_prefix_run_sim fuel C s fn (le_calldata_round bp ma ta sa fn)
Proof
  strip_tac >> `wf_function fn` by gvs[le_iteration_ready_def] >>
  irule le_prefix_run_sim_trans >> qexists `le_memory_round bp ma fn` >> conj_tac
  >- (pure_rewrite_tac[le_memory_round_def] >>
      irule le_iteration_config_run_step >> simp[] >> qexists `[]` >>
      simp[memory_config_def]) >>
  irule le_prefix_run_sim_trans >> qexists `le_transient_round bp ma ta fn` >> conj_tac
  >- (pure_rewrite_tac[le_transient_round_def] >>
      irule le_iteration_config_run_step >> simp[] >> qexists `[MLOAD]` >>
      simp[transient_config_def, le_memory_round_ready]) >>
  irule le_prefix_run_sim_trans >> qexists `le_storage_round bp ma ta sa fn` >> conj_tac
  >- (pure_rewrite_tac[le_storage_round_def] >>
      irule le_iteration_config_run_step >> simp[] >> qexists `[TLOAD; MLOAD]` >>
      simp[storage_config_def, le_transient_round_ready]) >>
  irule le_prefix_run_sim_trans >> qexists `le_data_round bp ma ta sa fn` >> conj_tac
  >- (pure_rewrite_tac[le_data_round_def] >>
      irule le_iteration_config_run_step >> simp[] >> qexists `[SLOAD; TLOAD; MLOAD]` >>
      simp[dload_config_def, le_storage_round_ready]) >>
  pure_rewrite_tac[le_calldata_round_def] >>
  irule le_iteration_config_run_step >> simp[] >> qexists `[DLOAD; SLOAD; TLOAD; MLOAD]` >>
  simp[calldataload_config_def, le_data_round_ready]
QED

Definition le_function_rounds_def:
  le_function_rounds fn = le_calldata_round
    (bp_analyze (cfg_analyze fn) fn)
    (memory_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn)
    (transient_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn)
    (storage_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn) fn
End

Theorem le_function_rounds_expansion:
  load_elim_function fn = clear_nops_function (le_function_rounds fn)
Proof
  simp[le_function_rounds_def, le_calldata_round_def,
       le_load_elim_function_rounds]
QED

Theorem le_function_rounds_run:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  EVERY (\i. i.inst_opcode <> MEMTOP) (fn_insts fn) /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  (!v. bp_get_ptrs (bp_analyze (cfg_analyze fn) fn) v = []) /\
  fn_entry_label fn = SOME s.vs_current_bb /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  le_prefix_run_sim fuel C s fn (le_function_rounds fn)
Proof
  strip_tac >> pure_rewrite_tac[le_function_rounds_def] >>
  irule le_five_rounds_run >>
  simp[le_iteration_ready_initial, le_function_alias_maps_wf]
QED
