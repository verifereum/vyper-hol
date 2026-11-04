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
