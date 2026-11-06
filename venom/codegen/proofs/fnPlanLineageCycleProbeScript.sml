Theory fnPlanLineageCycleProbe
Ancestors
  fnPlanLineageEntryProbe codegenReadyCompute stackPlanGen livenessDefs
  stackPlanOps stackPlanTypes stackModel venomInst cfgTransform list
Libs wordsLib

(* No PHIs: b is redefined on each traversal of body.  The exempt ASSIGN
   after ISZERO keeps b live at the optimistic query without violating SUE. *)
Definition cycle_probe_fn_def:
  cycle_probe_fn = mk_raw_function "cycle_probe"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [mk_inst 1 JNZ [Lit 1w; Label "body"; Label "exit"] []] |>;
     <| bb_label := "body"; bb_instructions :=
        [mk_inst 2 ADD [Lit 2w; Lit 3w] ["b"];
         mk_inst 3 ISZERO [Var "b"] ["out"];
         mk_inst 4 ASSIGN [Var "out"] ["unused_out"];
         mk_inst 5 ASSIGN [Var "b"] ["unused_b"];
         mk_inst 6 JMP [Label "H"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 7 STOP [] []] |>]
End

Theorem cycle_probe_ready:
  codegen_ready_fn cycle_probe_fn /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) cycle_probe_fn.fn_blocks
Proof
  EVAL_TAC >> simp[]
QED

Theorem cycle_probe_plan_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze cycle_probe_fn) (dfg_build_function cycle_probe_fn)
    (cfg_analyze cycle_probe_fn) NONE [] cycle_probe_fn 0 0)
Proof
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

Definition cycle_probe_step_def:
  cycle_probe_step n ps = SND (THE (generate_block_plan
    (liveness_analyze cycle_probe_fn) (dfg_build_function cycle_probe_fn)
    (cfg_analyze cycle_probe_fn) cycle_probe_fn
    (EL n cycle_probe_fn.fn_blocks) ps))
End

Definition cycle_probe_incoming_def:
  cycle_probe_incoming revisit =
    if revisit then cycle_probe_step 2 (cycle_probe_step 1
      (cycle_probe_step 0 entry_probe_start))
    else cycle_probe_step 0 entry_probe_start
End

Theorem cycle_probe_no_stale_backedge:
  (cycle_probe_incoming F).ps_stack = [] /\
  (cycle_probe_incoming T).ps_stack = [] /\
  (cycle_probe_incoming T).ps_spilled = FEMPTY
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem cycle_probe_cleanup_ledger:
  clean_stack_plan (liveness_analyze cycle_probe_fn) (cfg_analyze cycle_probe_fn)
    cycle_probe_fn (EL 1 cycle_probe_fn.fn_blocks) (cycle_probe_incoming T) =
    ([],cycle_probe_incoming T) /\
  (SND (clean_stack_plan (liveness_analyze cycle_probe_fn)
    (cfg_analyze cycle_probe_fn) cycle_probe_fn (EL 2 cycle_probe_fn.fn_blocks)
    (cycle_probe_step 1 (cycle_probe_incoming F)))).ps_stack = [] /\
  live_vars_at (liveness_analyze cycle_probe_fn) "body" 2 = ["b"; "out"]
Proof
  rpt conj_tac >> EVAL_TAC
QED
