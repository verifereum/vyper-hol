Theory fnLineageInvDuplicateTargets
Ancestors
  fnPlanLineage codegenReadyCompute planWfMarked
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst cfgTransform
Libs wordsLib

Definition duplicate_targets_fn_def:
  duplicate_targets_fn = mk_raw_function "duplicate_targets"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ADD [Lit 10w; Lit 1w] ["x"];
         mk_inst 1 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [mk_inst 2 ADD [Var "x"; Var "x"] ["y"];
         mk_inst 3 MSTORE [Lit 0w; Var "y"] [];
         mk_inst 4 STOP [] []] |>]
End

Theorem duplicate_targets_ready:
  codegen_ready_fn duplicate_targets_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem duplicate_targets_live:
  live_vars_at (liveness_analyze duplicate_targets_fn) "J" 0 = ["x"; "x"]
Proof
  EVAL_TAC
QED

Theorem duplicate_targets_actual:
  join_target_ops (liveness_analyze duplicate_targets_fn) duplicate_targets_fn
    "entry" (mk_inst 1 JMP [Label "J"] []) = SOME [Var "x"; Var "x"]
Proof
  EVAL_TAC
QED

Theorem duplicate_targets_block_rejected:
  generate_block_plan
    (liveness_analyze duplicate_targets_fn) (dfg_build_function duplicate_targets_fn)
    (cfg_analyze duplicate_targets_fn) duplicate_targets_fn
    (EL 0 duplicate_targets_fn.fn_blocks) (init_cleanup_plan_state NONE [] 0 0) = NONE
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

(* Canonical-state interface probes only: these inputs are not claimed reachable. *)
Theorem duplicate_targets_marker_reorder:
  !m n. MEM (m,n) [(1,2); (0,17); (16,17)] ==>
  (SND (reorder_plan (dfg_build_function duplicate_targets_fn)
    (REPLICATE n (Var "x"))
    ((init_cleanup_plan_state NONE [] 0 0) with
      ps_stack := REPLICATE m dead_stack_marker ++ [Var "x"]))).ps_stack =
    [Var "x"] ++ REPLICATE m dead_stack_marker
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.MEM, pairTheory.PAIR_EQ] >>
  gen_tac >> gen_tac >> strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem duplicate_targets_marker_spills_guard:
  !m n. MEM (m,n) [(1,2); (0,17); (16,17)] ==>
  (SND (reorder_plan (dfg_build_function duplicate_targets_fn)
    (REPLICATE n (Var "x"))
    ((init_cleanup_plan_state NONE [] 0 0) with
      ps_stack := REPLICATE m dead_stack_marker ++ [Var "x"]))).ps_spilled = FEMPTY /\
  ~(stack_pop n ([Var "x"] ++ REPLICATE m dead_stack_marker) ++
      REPLICATE n (Var "x") = [Var "x"] ++ REPLICATE m dead_stack_marker)
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.MEM, pairTheory.PAIR_EQ] >>
  gen_tac >> gen_tac >> strip_tac >> gvs[] >> EVAL_TAC
QED
