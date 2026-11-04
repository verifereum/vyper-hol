Theory fnPlanLineagePhiLoopProbe
Ancestors
  fnPlanLineagePhiTemporalProbe codegenReadyCompute stackPlanGen livenessDefs

(* Natural loop embedding of the checked local collision; no readiness or
   planner success is built into these fixture definitions. *)
Definition phi_collision_loop_def:
  phi_collision_loop = mk_raw_function "phi_collision_loop"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 3 ADD [Lit 10w;Lit 0w] ["a0"];
         mk_inst 4 ADD [Lit 11w;Lit 0w] ["a1"];
         mk_inst 5 ADD [Lit 12w;Lit 0w] ["a2"];
         mk_inst 6 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions := temporal_collision_phis ++
        [mk_inst 7 JNZ [Lit 1w;Label "left";Label "right"] []] |>;
     <| bb_label := "left"; bb_instructions :=
        [mk_inst 8 ADD [Lit 20w;Lit 0w] ["b0"];
         mk_inst 9 ADD [Lit 22w;Lit 0w] ["b2"];
         mk_inst 10 JMP [Label "header"] []] |>;
     <| bb_label := "right"; bb_instructions :=
        [mk_inst 11 ADD [Lit 30w;Lit 0w] ["c0"];
         mk_inst 12 ADD [Lit 32w;Lit 0w] ["c2"];
         mk_inst 13 JMP [Label "header"] []] |>]
End

Definition phi_collision_loop_ready_flags_def:
  phi_collision_loop_ready_flags =
    [canonical_param_prefix phi_collision_loop;
     wf_function phi_collision_loop;
     fn_inst_wf phi_collision_loop;
     ssa_form phi_collision_loop;
     def_dominates_uses phi_collision_loop;
     single_use_form phi_collision_loop;
     cfg_is_normalized (cfg_analyze phi_collision_loop) phi_collision_loop;
     block_entries_ready (cfg_analyze phi_collision_loop) phi_collision_loop;
     phi_operands_ready phi_collision_loop;
     EVERY (\bb. EVERY codegen_ready_inst bb.bb_instructions) phi_collision_loop.fn_blocks]
End

Theorem phi_collision_loop_ready_flags:
  phi_collision_loop_ready_flags = [T;T;T;T;T;T;T;T;F;T]
Proof
  EVAL_TAC >> simp[]
QED

Theorem phi_collision_loop_not_ready:
  ~codegen_ready_fn phi_collision_loop /\
  ~phi_operands_ready phi_collision_loop /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) phi_collision_loop.fn_blocks
Proof
  EVAL_TAC >> simp[]
QED

Theorem phi_collision_loop_liveness:
  MAP (live_vars_at (liveness_analyze phi_collision_loop) "header")
    [0;1;2;3] =
    [["a2";"b2";"c2";"a1";"x2";"a0";"b0";"c0"];
     ["x0";"a2";"b2";"c2";"a1";"x2"];
     ["x0";"a2";"b2";"c2"];
     ["x0";"x2"]]
Proof
  EVAL_TAC
QED

Theorem phi_collision_loop_header_obstruction:
  phi_uses_disjoint temporal_collision_phis /\
  MEM "x0" (inst_uses (EL 1 temporal_collision_phis)) /\
  MEM "x2" (inst_uses (EL 1 temporal_collision_phis)) /\
  MEM "x0" (live_vars_at (liveness_analyze phi_collision_loop) "header" 3) /\
  MEM "x2" (live_vars_at (liveness_analyze phi_collision_loop) "header" 3)
Proof
  EVAL_TAC
QED

(* All readiness conjuncts except phi_operands_ready hold.  The backedge
   uses force x0,x2 to stay live after the prefix, precisely the premise
   excluded by phi_block_ready.  Per the probe's stopping rule no function
   planner success, DFS/lineage witness, or frozen-task falsehood is claimed.
   Stop here for strategy review rather than altering the fixture. *)
