Theory fnPlanLineageInverseProbe
Ancestors fnPlanLineageSetup fnPlanLineageInventory livenessDefs venomInst
  stackPlanGen codegenReadyCompute
Libs wordsLib

(* Inverse local construction: schedule chosen from its literal exit list.
   This is not asserted to have a native DFS/lineage origin. *)
Definition inverse_fillers_def:
  inverse_fillers = ["b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";
                     "b8";"b9";"b10";"b11";"b12";"b13";"b14";"b15"]
End
Definition inverse_inst_def:
  inverse_inst = mk_inst 0 ASSIGN [Var "a"] ["y"]
End
Definition inverse_exit_def:
  inverse_exit = ["y"] ++ inverse_fillers ++ ["t";"x"]
End
Definition inverse_entry_live_def:
  inverse_entry_live = liveness_transfer [] inverse_inst inverse_exit
End
Definition inverse_core_def:
  inverse_core = [Var "a"] ++ MAP Var inverse_fillers ++ [Var "x"; Var "t"]
End
Definition inverse_start_def:
  inverse_start = (init_plan_state 0) with ps_stack := inverse_core
End
Definition inverse_pre_def:
  inverse_pre = SND (lineage_regular_prepare dfg_empty inverse_inst
    inverse_exit inverse_start)
End

Theorem inverse_literal_liveness:
  inverse_entry_live = inverse_fillers ++ ["t";"x";"a"] /\
  LAST inverse_exit = "x" /\ MEM "y" inverse_exit /\
  inst_wf inverse_inst /\ codegen_ready_inst inverse_inst
Proof
  EVAL_TAC
QED

Theorem inverse_selective_loss:
  stack_get_unfixed_depth (Var "a") 0 1 inverse_core = SOME 18 /\
  select_spill_candidate inverse_core [Var "a"] 18 1 = SOME 1 /\
  LIST_ELEM_COUNT (Var "x") inverse_core = 1 /\
  ~MEM (Var "x") (SND (do_spill_at 1 inverse_start)).ps_stack /\
  MEM (Var "x") (Var "x" :: (SND (do_spill_at 1 inverse_start)).ps_stack)
Proof
  EVAL_TAC
QED

Theorem inverse_preoptimistic_loss:
  ~MEM (Var "x") inverse_pre.ps_stack /\
  Var "x" IN FDOM inverse_pre.ps_spilled /\
  inverse_pre.ps_stack <> [] /\
  FST (optimistic_swap_plan dfg_empty inverse_inst inverse_exit F inverse_pre) = [] /\
  FST (optimistic_swap_plan dfg_empty inverse_inst inverse_exit F
    (inverse_pre with ps_stack := Var "x" :: inverse_pre.ps_stack)) <> []
Proof
  EVAL_TAC
QED

Theorem inverse_native_reduction_calls:
  FST (reduce_depth_plan (LENGTH inverse_core) [Var "a"] (Var "a") 0 1
    inverse_start) = [SOSwap 1; SOSpill 0; SOSwap 1; SOSpill 32] /\
  (SND (reduce_depth_plan (LENGTH inverse_core) [Var "a"] (Var "a") 0 1
    inverse_start)).ps_stack = [Var "a"] ++ MAP Var (TAKE 15 inverse_fillers) ++ [Var "t"] /\
  stack_peek 0 (SND (do_spill_at 1 inverse_start)).ps_stack = Var "t" /\
  select_spill_candidate (SND (do_spill_at 1 inverse_start)).ps_stack
    [Var "a"] 17 1 = SOME 1
Proof
  EVAL_TAC
QED

(* Full preparation, not an invented stack update.  The residual prefix
   survives the two actual selective spills and changes the later query. *)
Theorem inverse_prefix_preparation:
  FST (lineage_regular_prepare dfg_empty inverse_inst inverse_exit
    (inverse_start with ps_stack := Var "x" :: inverse_core)) =
  FST (lineage_regular_prepare dfg_empty inverse_inst inverse_exit inverse_start) /\
  SND (lineage_regular_prepare dfg_empty inverse_inst inverse_exit
    (inverse_start with ps_stack := Var "x" :: inverse_core)) =
  inverse_pre with ps_stack := Var "x" :: inverse_pre.ps_stack
Proof
  EVAL_TAC
QED

(* Reversed order is a second local layout, not the native join layout. *)
Theorem inverse_reversed_entry_obstruction:
  REVERSE (MAP Var inverse_entry_live) <> inverse_core /\
  stack_get_unfixed_depth (Var "a") 0 1
    (REVERSE (MAP Var inverse_entry_live)) = SOME 18 /\
  MEM (Var "x")
    (SND (lineage_regular_prepare dfg_empty inverse_inst inverse_exit
      (inverse_start with ps_stack := REVERSE (MAP Var inverse_entry_live)))).ps_stack
Proof
  EVAL_TAC
QED

Definition inverse_join_insts_def:
  inverse_join_insts = [inverse_inst] ++
    MAPi (\i v. mk_inst (100+i) ADD [Var v; Lit 1w] [STRCAT "dead_" v])
      (["x";"t"] ++ REVERSE inverse_fillers ++ ["y"]) ++
    [mk_inst 200 STOP [] []]
End
Definition inverse_fn_def:
  inverse_fn = mk_raw_function "entry"
    [<|bb_label := "entry"; bb_instructions :=
      MAPi (\i v. mk_inst (10+i) ADD [Lit 3w; Lit 4w] [v])
        (["a"] ++ inverse_fillers ++ ["x";"t"]) ++
      [mk_inst 1 JNZ [Lit 1w; Label "left"; Label "right"] []]|>;
     <|bb_label := "left"; bb_instructions := [mk_inst 2 JMP [Label "join"] []]|>;
     <|bb_label := "right"; bb_instructions := [mk_inst 3 JMP [Label "join"] []]|>;
     <|bb_label := "join"; bb_instructions := inverse_join_insts|>]
End

Theorem inverse_fn_ready:
  codegen_ready_fn inverse_fn
Proof
  rewrite_tac[codegen_ready_fn_def] >>
  rpt conj_tac >> EVAL_TAC >> simp[]
QED

Theorem inverse_fn_analyzed_lists:
  live_vars_at (liveness_analyze inverse_fn) "join" 0 = inverse_entry_live /\
  live_vars_at (liveness_analyze inverse_fn) "join" 1 = inverse_exit /\
  join_target_ops (liveness_analyze inverse_fn) inverse_fn "left"
    (mk_inst 2 JMP [Label "join"] []) = SOME (MAP Var inverse_entry_live)
Proof
  EVAL_TAC
QED

Theorem inverse_join_target_obstruction:
  MAP Var inverse_entry_live <> inverse_core /\
  stack_get_unfixed_depth (Var "a") 0 1 (MAP Var inverse_entry_live) = SOME 0 /\
  MEM (Var "x")
    (SND (lineage_regular_prepare dfg_empty inverse_inst inverse_exit
      (inverse_start with ps_stack := MAP Var inverse_entry_live))).ps_stack
Proof
  EVAL_TAC
QED

Theorem inverse_fn_markers:
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) inverse_fn.fn_blocks
Proof
  EVAL_TAC
QED

