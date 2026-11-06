Theory fnLineageInvForkProbe
Ancestors fnPlanLineage fnLineageInvSpliceProbe codegenReadyCompute cfgTransform stackPlanGen stackPlanOps stackPlanTypes venomInst

Definition cleanup_fork_fn_def:
  cleanup_fork_fn = mk_raw_function "cleanup_fork"
    [<|bb_label := "P"; bb_instructions :=
       [mk_inst 0 PARAM [Lit 0w] ["d"];
        mk_inst 1 PARAM [Lit 1w] ["x"];
        mk_inst 2 JNZ [Lit 1w; Label "A"; Label "B"] []]|>;
     <|bb_label := "A"; bb_instructions :=
       [mk_inst 3 MSTORE [Lit 0w; Var "x"] []; mk_inst 4 STOP [] []]|>;
     <|bb_label := "B"; bb_instructions :=
       [mk_inst 5 MSTORE [Lit 0w; Var "d"] []; mk_inst 6 STOP [] []]|>]
End

Theorem cleanup_fork_ready:
  codegen_ready_fn cleanup_fork_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem cleanup_fork_observe:
  (cfg_preds_of (cfg_analyze cleanup_fork_fn) "A",
   cfg_succs_of (cfg_analyze cleanup_fork_fn) "P",
   live_vars_at (liveness_analyze cleanup_fork_fn) "P" 3,
   input_vars_from "P"
    (THE (lookup_block "A" cleanup_fork_fn.fn_blocks)).bb_instructions
    (live_vars_at (liveness_analyze cleanup_fork_fn) "A" 0)) = (["P"],["B";"A"],["d";"x"],["x"])
Proof
  EVAL_TAC
QED

Theorem cleanup_fork_entry_stack:
  generate_block_plan (liveness_analyze cleanup_fork_fn)
    (dfg_build_function cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn (THE (lookup_block "P" cleanup_fork_fn.fn_blocks))
    (init_cleanup_plan_state NONE [] 0 0) = SOME
    ([SOLabel "P"; SOPush (Lit 1w); SOPushLabel "A"; SOEmit "JUMPI";
      SOPushLabel "B"; SOEmit "JUMP"],
     (init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "d";Var "x"])
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem cleanup_fork_retained:
  below_all_live (Var "d") ["x"] [Var "d";Var "x"] /\
  mark_dead_stack [Var "d"] [Var "d";Var "x"] =
    [dead_stack_marker;Var "x"]
Proof
  EVAL_TAC
QED

Theorem cleanup_fork_clean:
  !promised.
  clean_stack_plan (liveness_analyze cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn (THE (lookup_block "A" cleanup_fork_fn.fn_blocks))
    ((init_cleanup_plan_state NONE [] 0 0) with
      <|ps_stack := [Var "d";Var "x"]; ps_cleanup_promised := promised|>) =
    if promised then
      ([],(init_cleanup_plan_state NONE [] 0 0) with
        <|ps_stack := [dead_stack_marker;Var "x"]; ps_cleanup_promised := T|>)
    else
      ([SOSwap 1; SOPop 1],(init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "x"])
Proof
  Cases >> EVAL_TAC
QED

Theorem cleanup_fork_store:
  !promised.
  generate_inst_plan (liveness_analyze cleanup_fork_fn)
    (dfg_build_function cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn (mk_inst 3 MSTORE [Lit 0w;Var "x"] []) [] T T "A"
    ((init_cleanup_plan_state NONE [] 0 0) with
      <|ps_stack := if promised then [dead_stack_marker;Var "x"] else [Var "x"];
        ps_cleanup_promised := promised|>) =
    SOME ([SOPush (Lit 0w); SOEmit "MSTORE"],
      (init_cleanup_plan_state NONE [] 0 0) with
       <|ps_stack := if promised then [dead_stack_marker] else [];
         ps_cleanup_promised := promised|>)
Proof
  Cases >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem cleanup_fork_block_traces:
  !promised.
  generate_block_plan (liveness_analyze cleanup_fork_fn)
    (dfg_build_function cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn (THE (lookup_block "A" cleanup_fork_fn.fn_blocks))
    ((init_cleanup_plan_state NONE [] 0 0) with
      <|ps_stack := [Var "d";Var "x"]; ps_cleanup_promised := promised|>) =
    SOME ([SOLabel "A"] ++ (if promised then [] else [SOSwap 1; SOPop 1]) ++
       [SOPush (Lit 0w); SOEmit "MSTORE"; SOEmit "STOP"],
      (init_cleanup_plan_state NONE [] 0 0) with
       <|ps_stack := if promised then [dead_stack_marker] else [];
         ps_cleanup_promised := promised|>)
Proof
  Cases >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem cleanup_fork_same_code_excluded:
  !ops ps qs.
  generate_block_plan (liveness_analyze cleanup_fork_fn)
    (dfg_build_function cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn (THE (lookup_block "A" cleanup_fork_fn.fn_blocks))
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "d";Var "x"]) =
      SOME (ops,ps) ==>
  generate_block_plan (liveness_analyze cleanup_fork_fn)
    (dfg_build_function cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn (THE (lookup_block "A" cleanup_fork_fn.fn_blocks))
    ((init_cleanup_plan_state NONE [] 0 0) with
      <|ps_stack := [Var "d";Var "x"]; ps_cleanup_promised := T|>) <>
      SOME (ops,qs)
Proof
  rpt gen_tac >>
  `~(init_cleanup_plan_state NONE [] 0 0).ps_cleanup_promised` by EVAL_TAC >>
  mp_tac (Q.SPEC `F` cleanup_fork_block_traces) >>
  mp_tac (Q.SPEC `T` cleanup_fork_block_traces) >>
  simp[] >> EVAL_TAC >> simp[]
QED

Theorem cleanup_fork_b_return:
  generate_fn_plan_aux (liveness_analyze cleanup_fork_fn)
    (dfg_build_function cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn ["B"] ["P"]
    ((init_cleanup_plan_state NONE [] 0 0) with
     <|ps_stack := [Var "d";Var "x"]; ps_spilled := FEMPTY|>) =
  SOME ([SOLabel "B"; SOPop 1; SOPush (Lit 0w); SOEmit "MSTORE"; SOEmit "STOP"],
        ["B";"P"],init_cleanup_plan_state NONE [] 0 0)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem cleanup_fork_dfs_a:
  dfs_block_state (liveness_analyze cleanup_fork_fn)
    (dfg_build_function cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn (init_cleanup_plan_state NONE [] 0 0) "A"
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "d";Var "x"])
Proof
  `fn_entry_label cleanup_fork_fn = SOME "P"` by EVAL_TAC >>
  `dfs_aux_call (liveness_analyze cleanup_fork_fn)
    (dfg_build_function cleanup_fork_fn) (cfg_analyze cleanup_fork_fn)
    cleanup_fork_fn (init_cleanup_plan_state NONE [] 0 0) ["P"] []
    (init_cleanup_plan_state NONE [] 0 0)` by
    (irule dfs_aux_call_entry >> simp[]) >>
  drule dfs_aux_call_succs >>
  disch_then (qspec_then `THE (lookup_block "P" cleanup_fork_fn.fn_blocks)` mp_tac) >>
  `lookup_block "P" cleanup_fork_fn.fn_blocks =
    SOME (THE (lookup_block "P" cleanup_fork_fn.fn_blocks))` by EVAL_TAC >>
  simp[cleanup_fork_entry_stack] >>
  `cfg_succs_of (cfg_analyze cleanup_fork_fn) "P" = ["B";"A"]` by EVAL_TAC >>
  simp[] >> strip_tac >>
  drule dfs_aux_call_sibling >> simp[cleanup_fork_b_return] >>
  simp[init_cleanup_plan_state_def, init_plan_state_def] >> strip_tac >>
  drule dfs_aux_call_branch >>
  simp[dfs_block_state_def, init_cleanup_plan_state_def, init_plan_state_def] >>
  strip_tac >> qexistsl_tac [`[]`,`["B";"P"]`] >> simp[]
QED
