Theory fnPlanLineageMultiplicityProbe
Ancestors
  codegenReadyCompute stackPlanGen livenessDefs stackPlanOps stackPlanTypes
  stackModel venomInst cfgTransform
Libs wordsLib

Definition repeated_use_fn_def:
  repeated_use_fn branch = mk_raw_function "repeated_use"
    ([<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ADD [Lit 10w; Lit 1w] ["x"]] ++
        (if branch then
          [mk_inst 1 ADD [Lit 1w; Lit 0w] ["c"];
           mk_inst 2 JNZ [Var "c"; Label "use"; Label "other"] []]
         else [mk_inst 2 JMP [Label "use"] []]) |>;
      <| bb_label := "use"; bb_instructions :=
        [mk_inst 3 ADD [Var "x"; Var "x"] ["y"];
         mk_inst 4 JMP [Label "exit"] []] |>;
      <| bb_label := "exit"; bb_instructions := [mk_inst 5 STOP [] []] |>] ++
     (if branch then [<| bb_label := "other"; bb_instructions :=
        [mk_inst 6 STOP [] []] |>] else []))
End

Theorem repeated_use_ready:
  codegen_ready_fn (repeated_use_fn F) /\
  codegen_ready_fn (repeated_use_fn T) /\
  EVERY (\fn. EVERY (\bb. EVERY (\inst. EVERY (\op.
    op <> dead_stack_marker) inst.inst_operands) bb.bb_instructions)
    fn.fn_blocks) [repeated_use_fn F; repeated_use_fn T]
Proof
  EVAL_TAC >> simp[]
QED

Theorem repeated_use_liveness:
  live_vars_at (liveness_analyze (repeated_use_fn F)) "use" 0 = ["x";"x"] /\
  live_vars_at (liveness_analyze (repeated_use_fn T)) "use" 0 = ["x";"x"] /\
  input_vars_from "entry" (EL 1 (repeated_use_fn F).fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze (repeated_use_fn F)) "use" 0) = ["x";"x"] /\
  input_vars_from "entry" (EL 1 (repeated_use_fn T).fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze (repeated_use_fn T)) "use" 0) = ["x";"x"]
Proof
  EVAL_TAC
QED

Theorem repeated_use_plan_results:
  generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze (repeated_use_fn F)) (dfg_build_function (repeated_use_fn F))
    (cfg_analyze (repeated_use_fn F)) NONE [] (repeated_use_fn F) 0 0 = NONE /\
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze (repeated_use_fn T)) (dfg_build_function (repeated_use_fn T))
    (cfg_analyze (repeated_use_fn T)) NONE [] (repeated_use_fn T) 0 0)
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

Theorem repeated_use_branch_entry:
  IS_SOME (generate_block_plan
    (liveness_analyze (repeated_use_fn T)) (dfg_build_function (repeated_use_fn T))
    (cfg_analyze (repeated_use_fn T)) (repeated_use_fn T)
    (EL 0 (repeated_use_fn T).fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0)) /\
  (SND (THE (generate_block_plan
    (liveness_analyze (repeated_use_fn T)) (dfg_build_function (repeated_use_fn T))
    (cfg_analyze (repeated_use_fn T)) (repeated_use_fn T)
    (EL 0 (repeated_use_fn T).fn_blocks)
    (init_cleanup_plan_state NONE [] 0 0)))).ps_stack = [Var "x"] /\
  ~ALL_DISTINCT (MAP Var (input_vars_from "entry"
    (EL 1 (repeated_use_fn T).fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze (repeated_use_fn T)) "use" 0)))
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

(* JMP rejects the repeated target suffix; single-predecessor JNZ succeeds
   with one available x although the analyzed target list requests two.
   This refutes actual-caller target distinctness, not block-plan replay. *)
