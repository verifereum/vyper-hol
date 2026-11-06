Theory fnLineageInvDuplicateTargets
Ancestors
  fnPlanLineageMultiplicityProbe
Libs wordsLib

(* Canonical-state interface probes only: these inputs are not claimed reachable. *)
Theorem duplicate_targets_marker_reorder:
  !m n. MEM (m,n) [(1,2); (0,17); (16,17)] ==>
  (SND (reorder_plan (dfg_build_function (repeated_use_fn F))
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
  (SND (reorder_plan (dfg_build_function (repeated_use_fn F))
    (REPLICATE n (Var "x"))
    ((init_cleanup_plan_state NONE [] 0 0) with
      ps_stack := REPLICATE m dead_stack_marker ++ [Var "x"]))).ps_spilled = FEMPTY /\
  ~(stack_pop n ([Var "x"] ++ REPLICATE m dead_stack_marker) ++
      REPLICATE n (Var "x") = [Var "x"] ++ REPLICATE m dead_stack_marker)
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.MEM, pairTheory.PAIR_EQ] >>
  gen_tac >> gen_tac >> strip_tac >> gvs[] >> EVAL_TAC
QED
