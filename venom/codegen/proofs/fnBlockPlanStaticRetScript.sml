(* Small checked interfaces for the RET residual-inventory investigation. *)
Theory fnBlockPlanStaticRet
Ancestors
  fnPlanLineage stackPlanGen stackPlanTypes venomInst venomWf livenessDefs
  dfgDefs cfgDefs fnPlanPrefix
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.add_persistent_funs ["stackModel.stack_find_def"];

(* RET accepts label operands; CFG successor extraction follows those labels.
   The concrete ready function below therefore keeps x live across RET. *)
Definition ret_label_probe_fn_def:
  ret_label_probe_fn = mk_raw_function "f"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 OFFSET [Lit 0w; Label "entry"] ["x"];
          mk_inst 1 RET [Label "use"] []] |>;
     <| bb_label := "use"; bb_instructions :=
         [mk_inst 2 ASSERT [Var "x"] []; mk_inst 3 STOP [] []] |>]
End

Theorem ret_label_probe_ready_and_edge:
  codegen_ready_fn ret_label_probe_fn /\
  fn_cfg_edge ret_label_probe_fn "entry" "use"
Proof
  conj_tac
  >- (EVAL_TAC >> simp[])
  >> rewrite_tac[fn_cfg_edge_def]
  >> qexists_tac `HD ret_label_probe_fn.fn_blocks` >> EVAL_TAC
QED

Theorem ret_label_probe_function_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
    (cfg_analyze ret_label_probe_fn) NONE [] ret_label_probe_fn 0 0)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_block_result:
  ?ops ps'.
    generate_block_plan (liveness_analyze ret_label_probe_fn)
      (dfg_build_function ret_label_probe_fn) (cfg_analyze ret_label_probe_fn)
      ret_label_probe_fn (HD ret_label_probe_fn.fn_blocks)
      (init_cleanup_plan_state NONE [] 0 0) = SOME (ops, ps') /\
    ps'.ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_entry_states:
  !lv dg cg ps0.
    lineage_state lv dg cg ret_label_probe_fn ps0 "entry" ps0 /\
    dfs_block_state lv dg cg ret_label_probe_fn ps0 "entry" ps0
Proof
  rpt gen_tac >> conj_tac
  >- (irule lineage_state_entry >> EVAL_TAC)
  >> simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `[]`]
  >> simp[] >> irule dfs_aux_call_entry >> EVAL_TAC
QED

Definition ret_label_probe_before_def:
  ret_label_probe_before = SND (THE (generate_block_insts_prefix
    (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
    (cfg_analyze ret_label_probe_fn) ret_label_probe_fn "entry" F 0 2 0 1
    (HD ret_label_probe_fn.fn_blocks).bb_instructions
    (init_cleanup_plan_state NONE [] 0 0)))
End

Theorem ret_label_probe_prefix:
  ?ops.
    generate_block_insts_prefix
      (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
      (cfg_analyze ret_label_probe_fn) ret_label_probe_fn "entry" F 0 2 0 1
      (HD ret_label_probe_fn.fn_blocks).bb_instructions
      (init_cleanup_plan_state NONE [] 0 0) =
      SOME (ops, ret_label_probe_before)
Proof
  qexists_tac `[SOPushOfst "entry" 0]` >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_ret_nonempty:
  ?ops ps'.
    generate_inst_plan
      (liveness_analyze ret_label_probe_fn) (dfg_build_function ret_label_probe_fn)
      (cfg_analyze ret_label_probe_fn) ret_label_probe_fn
      (mk_inst 1 RET [Label "use"] [])
      (live_vars_at (liveness_analyze ret_label_probe_fn) "entry" 2)
      F F "entry" ret_label_probe_before = SOME (ops, ps') /\
    ps'.ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem ret_label_probe_live_and_stack:
  live_vars_at (liveness_analyze ret_label_probe_fn) "entry" 2 = ["x"] /\
  ret_label_probe_before.ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED
