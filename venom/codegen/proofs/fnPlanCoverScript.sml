(*
 * DFS coverage of the function planner, for the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation.
 *
 * The induction step at a jump needs, for the target block, the premises
 * dfs_block_state (the state the planner planned it from) and the
 * successful generate_block_plan from that state, and the target's code
 * inside the function's plan.  The function planner is a DFS over
 * cfg_succs_of from the entry label, so every block reachable in the CFG
 * is planned.
 *
 * TOP-LEVEL:
 *   dfs_block_state_reachable — CHEATED: every reachable block is planned
 *                               and its code is a slice of the plan
 *)

Theory fnPlanCover
Ancestors
  fnPlanLineage stackPlanGen stackPlanTypes venomWf cfgAnalysisProps
  dfAnalyzeProofs

Theorem ready_fn_cfg_edge:
  codegen_ready_fn fn /\ fn_cfg_edge fn a b ==>
  ?bb. lookup_block a fn.fn_blocks = SOME bb /\
       MEM b (cfg_succs_of (cfg_analyze fn) a)
Proof
  rpt strip_tac >>
  gvs[codegen_ready_fn_def, wf_function_def, fn_cfg_edge_def] >>
  `MEM bb.bb_label (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  drule dfAnalyzeProofsTheory.lookup_block_exists >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs]
QED

Theorem cleanup_plan_entry_call:
  fn_entry_label fn = SOME entry /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    spill_base lbl_ctr = SOME (ops, ps_end) ==>
  ?visited.
    generate_fn_plan_aux liveness dfg cfg fn [entry] []
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
      SOME (ops, visited, ps_end)
Proof
  simp[generate_fn_plan_with_cleanup_analyzed_def] >>
  Cases_on `canonical_param_prefix fn` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* Used at each jump of the block induction (JMP, both JNZ targets): the
   target is fn_reachable (the current block is, and the jump is a CFG
   edge), so it has a DFS state, its plan succeeds, and the plan is a
   contiguous slice of the function's plan (which fnPlanPlace places in
   prog).

   Why it should hold: generate_fn_plan_aux starts at [entry] and calls
   generate_succs_plan on cfg_succs_of of every block it plans; each call
   is a dfs_aux_call (dfs_aux_call_branch), and the plan returned SOME, so
   no call failed.  A label is only skipped as visited after it was
   planned, or as missing, which lookup_block = SOME rules out.
   cfg_succs_of (cfg_analyze fn) agrees with bb_succs (fn_cfg_edge) under
   wf_function (codegen_ready_fn), and block_ops is appended to the output
   unchanged (fnPlanDecomp$fn_plan_aux_per_block shows the asm form). *)
Theorem dfs_block_state_reachable:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_reachable fn lbl /\ lookup_block lbl fn.fn_blocks = SOME bb
    ==>
    ?ps_dfs block_ops ps_dfs_after pre post.
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb ps_dfs =
        SOME (block_ops, ps_dfs_after) /\
      fn_ops = pre ++ block_ops ++ post
Proof
  cheat
QED
