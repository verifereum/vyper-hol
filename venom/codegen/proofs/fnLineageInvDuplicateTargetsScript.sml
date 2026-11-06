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

(* One enlarged actual join producer.  The ordinary ADD duplicates x, while
   the other seventeen inputs are live through it. No PHIs share inputs. *)
Definition long_duplicate_join_fn_def:
  long_duplicate_join_fn = mk_raw_function "long_duplicate_join"
    [<| bb_label := "entry"; bb_instructions :=
        MAPi (\i v. mk_inst i ADD [Lit 10w; Lit 1w] [v])
          ["x";"a";"b";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r"] ++
        [mk_inst 18 ADD [Lit 1w; Lit 0w] ["c"];
         mk_inst 19 JNZ [Var "c"; Label "left"; Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
        [mk_inst 20 JMP [Label "use"] []] |>;
     <| bb_label := "right"; bb_instructions :=
        [mk_inst 21 JMP [Label "use"] []] |>;
     <| bb_label := "use"; bb_instructions :=
        [mk_inst 22 ADD [Var "x"; Var "x"] ["y"]] ++
        MAPi (\i v. mk_inst (23+i) MSTORE [Lit 0w; Var v] [])
          ["a";"b";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r"] ++
        [mk_inst 40 STOP [] []] |>]
End

Theorem long_duplicate_join_ready:
  codegen_ready_fn long_duplicate_join_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem long_duplicate_join_target:
  join_target_ops (liveness_analyze long_duplicate_join_fn)
    long_duplicate_join_fn "left"
    (mk_inst 20 JMP [Label "use"] []) =
    SOME (MAP Var ["r";"q";"p";"o";"n";"m";"l";"k";"j";"i";"h";"g";"f";"e";"d";"b";"a";"x";"x"])
Proof
  EVAL_TAC
QED

Theorem long_duplicate_join_plan_rejected:
  generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze long_duplicate_join_fn)
    (dfg_build_function long_duplicate_join_fn)
    (cfg_analyze long_duplicate_join_fn) NONE [] long_duplicate_join_fn 0 0 = NONE
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

(* Alter only the join block's use ordering: x is now consumed last. *)
Definition late_duplicate_join_fn_def:
  late_duplicate_join_fn = long_duplicate_join_fn with fn_blocks :=
    TAKE 3 long_duplicate_join_fn.fn_blocks ++
    [<| bb_label := "use"; bb_instructions :=
        MAPi (\i v. mk_inst (22+i) MSTORE [Lit 0w; Var v] [])
          ["a";"b";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r"] ++
        [mk_inst 39 ADD [Var "x"; Var "x"] ["y"];
         mk_inst 40 STOP [] []] |>]
End

Theorem late_duplicate_join_ready:
  codegen_ready_fn late_duplicate_join_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem late_duplicate_join_target:
  join_target_ops (liveness_analyze late_duplicate_join_fn)
    late_duplicate_join_fn "left" (mk_inst 20 JMP [Label "use"] []) =
    SOME (MAP Var ["x";"x";"r";"q";"p";"o";"n";"m";"l";"k";"j";"i";"h";"g";"f";"e";"d";"b";"a"])
Proof
  EVAL_TAC
QED

Theorem late_duplicate_join_entry_fields:
  ?ops qs. generate_block_plan
    (liveness_analyze late_duplicate_join_fn) (dfg_build_function late_duplicate_join_fn)
    (cfg_analyze late_duplicate_join_fn) late_duplicate_join_fn
    (EL 0 late_duplicate_join_fn.fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0) = SOME (ops,qs) /\
    qs.ps_stack =
      MAP Var ["x";"b";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"a"] /\
    qs.ps_spilled = FEMPTY
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC) >> simp[]
QED

Theorem late_duplicate_join_symbolic_success:
  HD ([]:operand list) = Var "x" ==>
  ?ops qs. generate_block_plan
    (liveness_analyze late_duplicate_join_fn) (dfg_build_function late_duplicate_join_fn)
    (cfg_analyze late_duplicate_join_fn) late_duplicate_join_fn
    (EL 1 late_duplicate_join_fn.fn_blocks)
    (SND (THE (generate_block_plan
      (liveness_analyze late_duplicate_join_fn) (dfg_build_function late_duplicate_join_fn)
      (cfg_analyze late_duplicate_join_fn) late_duplicate_join_fn
      (EL 0 late_duplicate_join_fn.fn_blocks)
      (init_cleanup_plan_state NONE [] 0 0)))) = SOME (ops,qs) /\
    qs.ps_stack = MAP Var
      ["x";"x";"r";"q";"p";"o";"n";"m";"l";"k";"j";"i";"h";"g";"f";"e";"d";"b";"a"]
Proof
  strip_tac >>
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC) >>
  gvs[] >> EVAL_TAC
QED
