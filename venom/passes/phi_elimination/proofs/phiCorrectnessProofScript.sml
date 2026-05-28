(*
 * PHI Elimination Function-Level Correctness
 *
 * Uses block_sim_function_pointwise_reachable from the simulation framework
 * to lift per-block simulation (phi_elim_block_sim) to function level.
 *
 * Single top-level theorem: phi_elimination_correct.
 *)

Theory phiCorrectnessProof
Ancestors
  phiBlock passSimulationProps passSimulationDefs execEquivParamProps
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  phiWellFormed phiTransform phiDefs list

(* Helper: transform_function matches function_map_transform shape *)
Theorem transform_function_is_function_map_transform:
  !fn. transform_function fn =
       function_map_transform (transform_block (dfg_build_function fn)) fn
Proof
  simp[transform_function_def, function_map_transform_def, LET_DEF]
QED

(* TOP-LEVEL: Context-level correctness.
 *
 * For any well-formed, PHI-elim-safe function in a context, the
 * transformed context contains a same-named function with
 * equivalent execution semantics, provided execution starts at
 * a function entry point (vs_inst_idx = 0 and either the state
 * has a previous block or is at the entry block label).
 *
 * Proof: lift per-block simulation (phi_elim_run_block_lift_result)
 * to function level via block_sim_function_pointwise_reachable.
 *)
Theorem phi_elimination_correct:
  !ctx fn_name fuel (func:ir_function) s.
    MEM func ctx.ctx_functions /\
    func.fn_name = fn_name /\
    wf_ir_fn func /\
    phi_elim_safe_fn func /\
    wf_function func /\
    fn_pseudos_prefix func /\
    func.fn_blocks <> [] /\
    s.vs_inst_idx = 0 /\
    (s.vs_prev_bb <> NONE \/
     s.vs_current_bb = (HD func.fn_blocks).bb_label)
  ==>
    ?func'.
      MEM func' (transform_context ctx).ctx_functions /\
      func'.fn_name = fn_name /\
      lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
        (run_blocks fuel ctx func s)
        (run_blocks fuel ctx func' s)
Proof
  rpt gen_tac >>
  DISCH_TAC >>
  qexists_tac `transform_function func` >>
  `MEM func ctx.ctx_functions` by fs[] >>
  `func.fn_name = fn_name` by fs[] >>
  `wf_ir_fn func` by fs[] >>
  `phi_elim_safe_fn func` by fs[] >>
  `wf_function func` by fs[] >>
  `fn_pseudos_prefix func` by fs[] >>
  `func.fn_blocks <> []` by fs[] >>
  `s.vs_inst_idx = 0` by fs[] >>
  `phi_wf_fn func` by metis_tac[wf_ir_implies_phi_wf] >>
  fs[phi_wf_fn_def, LET_DEF] >>
  conj_tac >- (
    simp[transform_context_def, MEM_MAP] >>
    qexists_tac `func` >> simp[]) >>
  conj_tac >- simp[transform_function_def] >>
  simp[transform_function_is_function_map_transform] >>
  irule block_sim_function_pointwise_reachable >>
  simp[state_equiv_execution_equiv_valid_state_rel, transform_block_label,
       state_equiv_def, execution_equiv_def] >>
  (* Per-block simulation: real PHI-prefix/eval_phis simulation. *)
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rename1 `run_block fuel0 ctx0 bb st` >>
  qspecl_then [`func`, `bb`, `fuel0`, `ctx0`, `st`]
    mp_tac phi_elim_run_block_lift_result >>
  simp[] >>
  fs[wf_function_def, fn_pseudos_prefix_def] >>
  Cases_on `st.vs_prev_bb = NONE` >> fs[]
QED
