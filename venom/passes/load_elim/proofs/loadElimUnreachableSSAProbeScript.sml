Theory loadElimUnreachableSSAProbe
Ancestors
  loadElimPhiProbes loadElimDefs finite_map venomWf venomInst relation

Definition unreachable_ssa_fn_def:
  unreachable_ssa_fn = mk_raw_function "unreachable"
    [<| bb_label := "e"; bb_instructions := [probe_inst 0 STOP [] []] |>;
     <| bb_label := "u"; bb_instructions :=
       [probe_inst 1 MLOAD [Lit 0w] ["x"];
        probe_inst 2 MLOAD [Lit 0w] ["y"];
        probe_inst 3 STOP [] []] |>]
End

Definition unreachable_ssa_ctx_def:
  unreachable_ssa_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function unreachable_ssa_fn) memory_config
End

Definition unreachable_ssa_fn1_def:
  unreachable_ssa_fn1 = load_elim_one unreachable_ssa_ctx
    (cfg_analyze unreachable_ssa_fn) unreachable_ssa_fn
End

Theorem unreachable_ssa_source_wf:
  wf_function unreachable_ssa_fn /\ fn_inst_wf unreachable_ssa_fn /\
  wf_ssa unreachable_ssa_fn
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  simp[wf_ssa_def, ssa_form_def, def_dominates_uses_def,
       unreachable_ssa_fn_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, probe_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem unreachable_ssa_round:
  unreachable_ssa_fn1 = mk_raw_function "unreachable"
    [<| bb_label := "e"; bb_instructions := [probe_inst 0 STOP [] []] |>;
     <| bb_label := "u"; bb_instructions :=
       [probe_inst 1 MLOAD [Lit 0w] ["x"];
        probe_inst 2 ASSIGN [Var "x"] ["y"];
        probe_inst 3 STOP [] []] |>]
Proof
  EVAL_TAC >> simp[FUN_FMAP_EMPTY, FLOOKUP_FUNION] >> EVAL_TAC
QED

Theorem unreachable_ssa_no_edges:
  !a b. ~fn_cfg_edge unreachable_ssa_fn1 a b
Proof
  rewrite_tac[unreachable_ssa_round] >> EVAL_TAC >>
  rpt strip_tac >> gvs[] >> EVAL_TAC >> gvs[listTheory.REV_DEF]
QED

Theorem unreachable_ssa_not_reached:
  ~fn_reachable unreachable_ssa_fn1 "u"
Proof
  simp[fn_reachable_def, Once RTC_CASES1, unreachable_ssa_no_edges] >>
  rewrite_tac[unreachable_ssa_round] >> EVAL_TAC
QED

(* Auxiliary SSA closure fails; this is not execution inequivalence. *)
Theorem unreachable_ssa_target_not_wf:
  ~wf_ssa unreachable_ssa_fn1
Proof
  rewrite_tac[wf_ssa_def, def_dominates_uses_def] >>
  strip_tac >>
  qpat_x_assum `!bb inst. _` (qspecl_then
    [`<| bb_label := "u"; bb_instructions :=
       [probe_inst 1 MLOAD [Lit 0w] ["x"];
        probe_inst 2 ASSIGN [Var "x"] ["y"];
        probe_inst 3 STOP [] []] |>`,
     `probe_inst 2 ASSIGN [Var "x"] ["y"]`] mp_tac) >>
  simp[probe_inst_def, def_available_at_def, fn_dominates_def,
       unreachable_ssa_not_reached] >>
  simp[unreachable_ssa_round, mk_raw_function_def, probe_inst_def]
QED

Theorem unreachable_ssa_closure_counterexample:
  wf_function unreachable_ssa_fn /\ fn_inst_wf unreachable_ssa_fn /\
  wf_ssa unreachable_ssa_fn /\
  unreachable_ssa_ctx.lctx_dfg = dfg_build_function unreachable_ssa_fn /\
  ~wf_ssa (load_elim_one unreachable_ssa_ctx
    (cfg_analyze unreachable_ssa_fn) unreachable_ssa_fn)
Proof
  simp[GSYM unreachable_ssa_fn1_def, unreachable_ssa_source_wf,
       unreachable_ssa_target_not_wf, unreachable_ssa_ctx_def,
       mk_load_context_def]
QED
