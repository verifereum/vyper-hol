Theory loadElimRoundExecution
Ancestors
  loadElimCoupledExecution loadElimConvergence loadElimSolverHelpers loadElimDefs

(* Public one-round boundary; convergence is an internal solver obligation. *)
Theorem le_load_elim_one_run_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s.vs_current_bb /\
  ir_cfg = cfg_analyze fn /\
  DISJOINT G (set (fn_all_vars fn)) /\
  (!pa. MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx ir_cfg
      (load_analyze ctx fn) fn) ==> pa.pa_phi_out IN G) /\
  EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts fn) /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions /\
  le_padded_control G s t ==>
  (?e. run_blocks fuel C fn s = Error e) \/
  lift_result (le_padded_control G) (padded_exec_equiv G) (padded_exec_equiv G)
    (run_blocks fuel C fn s)
    (run_blocks fuel C (load_elim_one ctx ir_cfg fn) t)
Proof
  strip_tac >> gvs[] >>
  simp[load_elim_one_def] >>
  irule le_coupled_run_initial_disjoint >>
  simp[le_round_ready_disjoint_def, le_round_ready_names_def] >>
  drule le_load_analyze_fixpoint >>
  simp[le_solver_process_def]
QED
