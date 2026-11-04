Theory fnPlanLineageResidualProbe
Ancestors
  fnPlanLineageStageAudit codegenReadyCompute

Theorem residual_empty_list[compute]:
  SET_TO_LIST (EMPTY : operand set) = []
Proof
  simp[]
QED

Definition residual_fn_def:
  residual_fn = mk_raw_function "residual"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 PARAM [Lit 0w] ["c"];
         mk_inst 1 PARAM [Lit 1w] ["v"];
         mk_inst 2 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [mk_inst 3 OFFSET [Lit 0w; Label "J"] ["r"];
         mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 5 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [mk_inst 6 RETURN [Var "v"; Lit 0w] []] |>]
End

Theorem residual_ready:
  codegen_ready_fn residual_fn
Proof
  EVAL_TAC >> simp[]
QED

Definition residual_step_def:
  residual_step lbl ps = generate_block_plan
    (liveness_analyze residual_fn) (dfg_build_function residual_fn)
    (cfg_analyze residual_fn) residual_fn
    (THE (lookup_block lbl residual_fn.fn_blocks)) ps
End

Definition residual_entry_def:
  residual_entry = SND (THE (residual_step "E"
    (init_cleanup_plan_state NONE [] 0 0)))
End

Definition residual_a_def:
  residual_a = SND (THE (residual_step "A" residual_entry))
End

Definition residual_b_def:
  residual_b = SND (THE (residual_step "B" residual_entry))
End

Theorem residual_join_replay:
  FST (THE (residual_step "J" residual_a)) =
  FST (THE (residual_step "J" residual_b))
Proof
  EVAL_TAC >> simp[]
QED

Theorem residual_whole_some:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze residual_fn) (dfg_build_function residual_fn)
    (cfg_analyze residual_fn) NONE [] residual_fn 0 0)
Proof
  EVAL_TAC >> simp[]
QED

Definition residual_matrix_fn_def:
  residual_matrix_fn rev n local_offset = mk_raw_function "matrix"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 PARAM [Lit 0w] ["c"]] ++
        MAPi (\i v. mk_inst (i+1) PARAM [Lit (n2w (i+1))] [v])
          (TAKE n ["v"; "w"]) ++
        [mk_inst 3 JNZ (if rev then [Var "c"; Label "B"; Label "A"]
                       else [Var "c"; Label "A"; Label "B"]) []] |>;
     <| bb_label := "A"; bb_instructions :=
        [mk_inst 4 OFFSET [Lit 0w; Label "J"] ["r"];
         mk_inst 5 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 6 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        (if local_offset then
          [mk_inst 7 OFFSET [Lit 0w; Label "J"] ["q"];
           mk_inst 8 MSTORE [Lit 0w; Var "q"] []] else []) ++
        [mk_inst 9 RETURN
          [if n = 0 then Lit 0w else Var "v";
           if n < 2 then Lit 0w else Var "w"] []] |>]
End

Definition residual_matrix_step_def:
  residual_matrix_step fn lbl ps = generate_block_plan
    (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn (THE (lookup_block lbl fn.fn_blocks)) ps
End

Definition residual_matrix_check_def:
  residual_matrix_check rev n local_offset =
    (\fn.
      (\ps.
        FST (THE (residual_matrix_step fn "J"
          (SND (THE (residual_matrix_step fn "A" ps))))) =
        FST (THE (residual_matrix_step fn "J"
          (SND (THE (residual_matrix_step fn "B" ps))))))
       (SND (THE (residual_matrix_step fn "E"
         (init_cleanup_plan_state NONE [] 0 0)))))
      (residual_matrix_fn rev n local_offset)
End

Theorem residual_matrix_ready:
  EVERY (\rev. EVERY (\n. EVERY (\local_offset.
    codegen_ready_fn (residual_matrix_fn rev n local_offset)) [F; T])
      [0; 1; 2]) [F; T]
Proof
  EVAL_TAC
QED

Theorem residual_matrix_replays:
  EVERY (\rev. EVERY (\n. EVERY (\local_offset.
    residual_matrix_check rev n local_offset) [F; T]) [0; 1; 2]) [F; T]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem residual_join_entries:
  residual_a.ps_stack = [Var "r"; Var "v"] /\
  residual_b.ps_stack = [Var "v"] /\
  residual_a.ps_spilled = FEMPTY /\ residual_b.ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Theorem residual_matrix_marker_free:
  EVERY (\rev. EVERY (\n. EVERY (\local_offset.
    EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb.bb_instructions)
      (residual_matrix_fn rev n local_offset).fn_blocks) [F; T])
    [0; 1; 2]) [F; T]
Proof
  EVAL_TAC
QED

Theorem residual_matrix_whole_some:
  EVERY (\rev. EVERY (\n. EVERY (\local_offset.
    IS_SOME (generate_fn_plan_with_cleanup_analyzed
      (liveness_analyze (residual_matrix_fn rev n local_offset))
      (dfg_build_function (residual_matrix_fn rev n local_offset))
      (cfg_analyze (residual_matrix_fn rev n local_offset)) NONE []
      (residual_matrix_fn rev n local_offset) 0 0)) [F; T]) [0; 1; 2]) [F; T]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

(* Bounded negative probe result: all twelve combinations of successor order,
   zero/one/two live targets and a join-local OFFSET consumer are ready,
   marker-free and whole-plan SOME, and the directly computed A/B join replays
   emit the same operations. The base example nevertheless has an unmarked r
   prefix on A, absent on B, with empty spills on both sides. Thus this family
   refutes exact-liveness inventory but does NOT refute the frozen theorem.
   These checks do not assert the frozen dfs_block_state/lineage_state predicates
   or universal cleanup-field replay. Those would be required for falsehood,
   but no distinguishing operations were found in the authorized matrix.
   Stop the bounded search here for strategist review, not further variants.
*)

(* A backedge revisits the same static OFFSET output; no dynamic freshness
   assumption is justified by SSA. *)
Definition residual_loop_fn_def:
  residual_loop_fn = mk_raw_function "loop"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 PARAM [Lit 0w] ["c"];
         mk_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 3 OFFSET [Lit 0w; Label "H"] ["r"];
         mk_inst 4 JMP [Label "H"] []] |>;
     <| bb_label := "X"; bb_instructions :=
        [mk_inst 5 STOP [] []] |>]
End

Theorem residual_loop_ready:
  codegen_ready_fn residual_loop_fn
Proof
  EVAL_TAC >> simp[]
QED

Definition residual_loop_step_def:
  residual_loop_step = residual_matrix_step residual_loop_fn
End

Definition residual_loop_entry_def:
  residual_loop_entry = SND (THE (residual_loop_step "E"
    (init_cleanup_plan_state NONE [] 0 0)))
End

Definition residual_loop_lap_def:
  residual_loop_lap ps = SND (THE (residual_loop_step "B"
    (SND (THE (residual_loop_step "H" ps)))))
End

Theorem residual_loop_whole_some:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze residual_loop_fn) (dfg_build_function residual_loop_fn)
    (cfg_analyze residual_loop_fn) NONE [] residual_loop_fn 0 0)
Proof
  EVAL_TAC >> simp[]
QED

Theorem residual_loop_laps:
  residual_loop_entry.ps_stack = [Var "c"] /\
  (residual_loop_lap residual_loop_entry).ps_stack = [Var "r"; Var "c"] /\
  (residual_loop_lap (residual_loop_lap residual_loop_entry)).ps_stack =
    [Var "r"; Var "r"; Var "c"]
Proof
  EVAL_TAC
QED

Theorem residual_loop_replay:
  FST (THE (residual_loop_step "H" residual_loop_entry)) =
  FST (THE (residual_loop_step "H" (residual_loop_lap residual_loop_entry))) /\
  FST (THE (residual_loop_step "B"
    (SND (THE (residual_loop_step "H" residual_loop_entry))))) =
  FST (THE (residual_loop_step "B"
    (SND (THE (residual_loop_step "H"
      (residual_loop_lap residual_loop_entry)))))) /\
  residual_loop_lap residual_loop_entry =
    residual_loop_entry with ps_stack := [Var "r"; Var "c"] /\
  residual_loop_lap (residual_loop_lap residual_loop_entry) =
    residual_loop_entry with ps_stack := [Var "r"; Var "r"; Var "c"]
Proof
  EVAL_TAC
QED

Theorem residual_loop_cleanup_spills:
  residual_loop_entry.ps_cleanup_height = NONE /\
  residual_loop_entry.ps_cleanup_promised = F /\
  residual_loop_entry.ps_spilled = FEMPTY /\
  residual_a.ps_alloc = residual_b.ps_alloc /\
  (SND (THE (residual_step "J" residual_a))).ps_alloc =
  (SND (THE (residual_step "J" residual_b))).ps_alloc /\
  (SND (THE (residual_step "J" residual_a))).ps_spilled = FEMPTY /\
  (SND (THE (residual_step "J" residual_b))).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Theorem residual_join_exit_stacks:
  (SND (THE (residual_step "J" residual_a))).ps_stack = [Var "r"] /\
  (SND (THE (residual_step "J" residual_b))).ps_stack = []
Proof
  EVAL_TAC
QED

(* Compatibility boundary of the bounded loop test:
   H is first visited from E; its DFS input has residual_loop_entry's stack.
   B is first visited from H; its backedge has residual_loop_lap's stack.
   The record equalities in residual_loop_replay show the non-stack fields
   are unchanged, so the lineage step's splice from H's DFS record is exactly
   that lap state. Repeating the lap uses the same static OFFSET definition
   and obtains a second r, not a fresh variable. The equal H/B operation
   lists are the replay premises, NOT a proof of general reachability.
   Cleanup is disabled (height NONE); the JMP reset retains arbitrary dead
   bottom cells. In particular neither diamond nor loop justifies erasing
   r, replacing it by dead_stack_marker, or assuming residual distinctness.
*)
