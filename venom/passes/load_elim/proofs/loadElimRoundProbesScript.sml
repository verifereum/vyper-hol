Theory loadElimRoundProbes
Ancestors
  loadElimPhiProbes finite_map loadElimDefs venomInst

Definition round_probe_fn_def:
  round_probe_fn = mk_raw_function "rounds"
    [<| bb_label := "e"; bb_instructions :=
      [probe_inst 0 MLOAD [Lit 0w] ["x"];
       probe_inst 1 MLOAD [Lit 0w] ["y"];
       probe_inst 2 TLOAD [Var "y"] ["a"];
       probe_inst 3 TLOAD [Var "x"] ["b"];
       probe_inst 4 STOP [] []] |>]
End

Definition round_probe_mem_ctx_def:
  round_probe_mem_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function round_probe_fn) memory_config
End

Definition round_probe_fn1_def:
  round_probe_fn1 = load_elim_one round_probe_mem_ctx
    (cfg_analyze round_probe_fn) round_probe_fn
End

Theorem round_probe_memory_assign:
  round_probe_fn1 = mk_raw_function "rounds"
    [<| bb_label := "e"; bb_instructions :=
      [probe_inst 0 MLOAD [Lit 0w] ["x"];
       probe_inst 1 ASSIGN [Var "x"] ["y"];
       probe_inst 2 TLOAD [Var "y"] ["a"];
       probe_inst 3 TLOAD [Var "x"] ["b"];
       probe_inst 4 STOP [] []] |>]
Proof
  EVAL_TAC >> simp[FUN_FMAP_EMPTY] >> EVAL_TAC
QED

Theorem round_probe_rebuilt_normalize:
  normalize_operand (dfg_build_function round_probe_fn1) [] (Var "y") = Var "x"
Proof
  rewrite_tac[round_probe_memory_assign] >> EVAL_TAC
QED

Definition round_probe_trs_ctx_def:
  round_probe_trs_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function round_probe_fn1) transient_config
End

Theorem round_probe_transient_assign:
  load_elim_one round_probe_trs_ctx (cfg_analyze round_probe_fn) round_probe_fn1 =
    mk_raw_function "rounds"
    [<| bb_label := "e"; bb_instructions :=
      [probe_inst 0 MLOAD [Lit 0w] ["x"];
       probe_inst 1 ASSIGN [Var "x"] ["y"];
       probe_inst 2 TLOAD [Var "y"] ["a"];
       probe_inst 3 ASSIGN [Var "a"] ["b"];
       probe_inst 4 STOP [] []] |>]
Proof
  rewrite_tac[round_probe_trs_ctx_def, round_probe_memory_assign] >>
  EVAL_TAC >> simp[FUN_FMAP_EMPTY] >> EVAL_TAC
QED

Definition round_probe_diamond_ctx_def:
  round_probe_diamond_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function diamond_transformed_probe_fn) dload_config
End

Theorem round_probe_phi_normalize:
  normalize_operand (dfg_build_function diamond_transformed_probe_fn) [] (Var "z") =
    Var "$le_phi_6"
Proof
  EVAL_TAC
QED

