Theory fnPlanLineageResidualProbe
Ancestors
  fnPlanLineageStageAudit codegenReadyCompute fnPlanLineageStages
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst cfgTransform

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


(* Closed queries: do not expand whole analyses in symbolic stage proofs. *)
Theorem residual_loop_header_queries:
  lookup_block "H" residual_loop_fn.fn_blocks =
    SOME <|bb_label := "H"; bb_instructions :=
      [mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []]|> /\
  (<|bb_label := "H"; bb_instructions :=
      [mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []]|> <>
    HD residual_loop_fn.fn_blocks) /\
  cfg_preds_of (cfg_analyze residual_loop_fn) "H" = ["E"; "B"] /\
  live_vars_at (liveness_analyze residual_loop_fn) "H" 1 = ["c"]
Proof
  EVAL_TAC
QED

Theorem residual_loop_header_base:
  residual_loop_step "H" residual_loop_entry = SOME
    ([SOLabel "H"; SODup 1; SOPushLabel "B"; SOEmit "JUMPI";
      SOPushLabel "X"; SOEmit "JUMP"], residual_loop_entry)
Proof
  EVAL_TAC
QED

Theorem residual_loop_header_inst:
  (mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []).inst_opcode = JNZ /\
  (mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []).inst_operands =
    [Var "c"; Label "B"; Label "X"] /\
  (mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []).inst_outputs = []
Proof
  EVAL_TAC
QED

Definition residual_loop_state_def:
  residual_loop_state n = residual_loop_entry with
    ps_stack := REPLICATE n (Var "r") ++ [Var "c"]
End

Theorem residual_loop_entry_fields:
  residual_loop_entry.ps_spilled = FEMPTY /\
  residual_loop_entry.ps_cleanup_height = NONE
Proof
  EVAL_TAC
QED

Theorem residual_loop_input_symbolic:
  emit_input_plan JNZ [Var "c"] ["c"] (residual_loop_state n) =
    ([SODup 1], residual_loop_state n with ps_stack :=
      REPLICATE n (Var "r") ++ [Var "c"; Var "c"])
Proof
  simp[emit_input_plan_one, emit_one_input_def, residual_loop_state_def,
    residual_loop_entry_fields, is_var_operand_def, stack_get_depth_def,
    listTheory.REVERSE_APPEND, stack_find_def, do_dup_def,
    stack_dup_def, stack_peek_def, stack_push_def,
    listTheory.EL_APPEND_EQN, listTheory.SNOC_APPEND,
    listTheory.APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> REFL_TAC
QED

Theorem residual_loop_pre_codegen:
  ~is_pre_codegen_opcode JNZ
Proof
  EVAL_TAC
QED

Theorem residual_loop_header_operands:
  get_non_label_operands (mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []) =
    [Var "c"] /\ ~is_commutative JNZ
Proof
  EVAL_TAC
QED

Theorem residual_loop_header_reorder:
  reorder_plan dfg [Var "c"]
    (residual_loop_state n with ps_stack := REPLICATE n (Var "r") ++
      [Var "c"; Var "c"]) =
    ([], residual_loop_state n with ps_stack := REPLICATE n (Var "r") ++
      [Var "c"; Var "c"])
Proof
  simp[reorder_plan_def, reorder_one_def,
    stack_get_unfixed_depth_def, stack_get_depth_def,
    listTheory.REVERSE_APPEND, stack_find_def]
QED

Theorem residual_loop_header_emit:
  generate_emit_ops (mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []) 0 ps =
    ([SOPushLabel "B"; SOEmit "JUMPI"; SOPushLabel "X"; SOEmit "JUMP"], ps)
Proof
  EVAL_TAC
QED

Theorem residual_loop_regular_header:
  generate_regular_inst_plan (liveness_analyze residual_loop_fn)
    (dfg_build_function residual_loop_fn) (cfg_analyze residual_loop_fn)
    residual_loop_fn (mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] [])
    ["c"] F F "H" (residual_loop_state n) =
  ([SODup 1; SOPushLabel "B"; SOEmit "JUMPI"; SOPushLabel "X"; SOEmit "JUMP"],
    residual_loop_state n)
Proof
  simp[generate_regular_inst_plan_def, residual_loop_header_inst,
    compute_operands_def, residual_loop_header_operands,
    residual_loop_input_symbolic, residual_loop_header_reorder] >>
  simp[residual_loop_header_emit, stack_pop_def,
    release_dead_spills_def, residual_loop_state_def, residual_loop_entry_fields] >>
  simp[listTheory.TAKE_APPEND2]
QED

Theorem residual_loop_header_symbolic:
  residual_loop_step "H" (residual_loop_state n) =
    SOME (FST (THE (residual_loop_step "H" residual_loop_entry)),
      residual_loop_state n)
Proof
  rewrite_tac[residual_loop_header_base] >>
  rewrite_tac[residual_loop_step_def, residual_matrix_step_def,
    residual_loop_header_queries, generate_block_plan_def] >>
  simp[residual_loop_header_queries, non_param_insts_def, get_params_def,
    bb_is_halting_def, is_halting_opcode_def, is_param_opcode_def,
    residual_loop_header_inst] >>
  simp[Once generate_block_insts_plan_def] >>
  simp[generate_inst_plan_def, residual_loop_header_queries,
    residual_loop_header_inst, residual_loop_pre_codegen, is_param_opcode_def,
    residual_loop_regular_header, Once generate_block_insts_plan_def]
QED

Theorem residual_loop_body_queries:
  lookup_block "B" residual_loop_fn.fn_blocks =
    SOME <|bb_label := "B"; bb_instructions :=
      [mk_inst 3 OFFSET [Lit 0w; Label "H"] ["r"];
       mk_inst 4 JMP [Label "H"] []]|> /\
  (<|bb_label := "B"; bb_instructions :=
      [mk_inst 3 OFFSET [Lit 0w; Label "H"] ["r"];
       mk_inst 4 JMP [Label "H"] []]|> <> HD residual_loop_fn.fn_blocks) /\
  cfg_preds_of (cfg_analyze residual_loop_fn) "B" = ["H"] /\
  live_vars_at (liveness_analyze residual_loop_fn) "B" 1 = ["c"] /\
  live_vars_at (liveness_analyze residual_loop_fn) "B" 2 = ["c"] /\
  join_target_ops (liveness_analyze residual_loop_fn) residual_loop_fn "B"
    (mk_inst 4 JMP [Label "H"] []) = SOME [Var "c"]
Proof
  EVAL_TAC
QED

Theorem residual_loop_cleanup_queries:
  lookup_block "H" residual_loop_fn.fn_blocks =
    SOME <|bb_label := "H"; bb_instructions :=
      [mk_inst 2 JNZ [Var "c"; Label "B"; Label "X"] []]|> /\
  live_vars_at (liveness_analyze residual_loop_fn) "B" 0 = ["c"] /\
  input_vars_from "H"
    [mk_inst 3 OFFSET [Lit 0w; Label "H"] ["r"];
     mk_inst 4 JMP [Label "H"] []] ["c"] = ["c"] /\
  cfg_succs_of (cfg_analyze residual_loop_fn) "H" = ["X"; "B"]
Proof
  EVAL_TAC
QED

Theorem residual_loop_body_cleanup:
  clean_stack_plan (liveness_analyze residual_loop_fn) (cfg_analyze residual_loop_fn)
    residual_loop_fn <|bb_label := "B"; bb_instructions :=
      [mk_inst 3 OFFSET [Lit 0w; Label "H"] ["r"];
       mk_inst 4 JMP [Label "H"] []]|> (residual_loop_state n) =
    ([], residual_loop_state n)
Proof
  simp[clean_stack_plan_def, residual_loop_body_queries,
    residual_loop_cleanup_queries, residual_loop_header_queries,
    residual_loop_state_def, residual_loop_entry_fields] >>
  simp[residual_loop_cleanup_spills, popmany_plan_def]
QED

Theorem residual_loop_body_inst:
  (mk_inst 3 OFFSET [Lit 0w; Label "H"] ["r"]).inst_opcode = OFFSET /\
  (mk_inst 3 OFFSET [Lit 0w; Label "H"] ["r"]).inst_operands = [Lit 0w; Label "H"] /\
  (mk_inst 3 OFFSET [Lit 0w; Label "H"] ["r"]).inst_outputs = ["r"] /\
  (mk_inst 4 JMP [Label "H"] []).inst_opcode = JMP /\
  (mk_inst 4 JMP [Label "H"] []).inst_operands = [Label "H"] /\
  (mk_inst 4 JMP [Label "H"] []).inst_outputs = [] /\
  ~is_pre_codegen_opcode OFFSET /\ ~is_pre_codegen_opcode JMP
Proof
  EVAL_TAC
QED


Theorem residual_loop_jmp_queries:
  get_non_label_operands (mk_inst 4 JMP [Label "H"] []) = [] /\
  ~is_commutative JMP /\
  ~operand_equiv (dfg_build_function residual_loop_fn) (Var "c") (Var "r") /\
  generate_emit_ops (mk_inst 4 JMP [Label "H"] []) 0 ps =
    ([SOPushLabel "H"; SOEmit "JUMP"], ps)
Proof
  EVAL_TAC
QED

Theorem residual_loop_regular_jmp:
  generate_regular_inst_plan (liveness_analyze residual_loop_fn)
    (dfg_build_function residual_loop_fn) (cfg_analyze residual_loop_fn)
    residual_loop_fn (mk_inst 4 JMP [Label "H"] []) ["c"] F F "B"
    (residual_loop_state n with ps_stack :=
      (residual_loop_state n).ps_stack ++ [Var "r"]) =
    ([SOSwap 1; SOPushLabel "H"; SOEmit "JUMP"], residual_loop_state (SUC n))
Proof
  simp[generate_regular_inst_plan_def, residual_loop_body_inst,
    compute_operands_def,
    residual_loop_jmp_queries, emit_input_plan_def, residual_loop_body_queries] >>
  simp[restore_spilled_plan_def, do_restore_def,
    residual_loop_state_def, residual_loop_entry_fields] >>
  simp[reorder_plan_def, reorder_one_def, stack_get_unfixed_depth_def,
    stack_get_depth_def, listTheory.REVERSE_APPEND, stack_find_def,
    stack_peek_def, listTheory.EL_APPEND_EQN, residual_loop_jmp_queries,
    do_swap_def] >>
  simp[release_dead_spills_def, residual_loop_entry_fields, stack_pop_def,
    stack_swap_def, listTheory.EL_APPEND_EQN, rich_listTheory.LUPDATE_APPEND2] >>
  simp[listTheory.LUPDATE_def, rich_listTheory.LUPDATE_APPEND2,
    rich_listTheory.LUPDATE_APPEND1, listTheory.TAKE_APPEND2] >>
  simp[GSYM listTheory.SNOC_APPEND, rich_listTheory.SNOC_REPLICATE]
QED

Theorem residual_loop_body_symbolic:
  residual_loop_step "B" (residual_loop_state n) =
    SOME ([SOLabel "B"; SOPushOfst "H" 0; SOSwap 1;
      SOPushLabel "H"; SOEmit "JUMP"], residual_loop_state (SUC n))
Proof
  rewrite_tac[residual_loop_step_def, residual_matrix_step_def,
    residual_loop_body_queries, generate_block_plan_def] >>
  simp[residual_loop_body_queries, non_param_insts_def, get_params_def,
    bb_is_halting_def, residual_loop_body_inst, is_halting_opcode_def,
    is_param_opcode_def, residual_loop_body_cleanup] >>
  simp[Once generate_block_insts_plan_def, generate_inst_plan_def,
    residual_loop_body_inst] >>
  simp[generate_offset_plan_def, residual_loop_body_inst,
    stack_push_def, listTheory.SNOC_APPEND] >>
  simp[Once generate_block_insts_plan_def, generate_inst_plan_def,
    residual_loop_body_inst, residual_loop_body_queries,
    is_param_opcode_def, residual_loop_regular_jmp] >>
  simp[join_reached_def, residual_loop_body_queries, residual_loop_state_def,
    listTheory.DROP_APPEND, Once generate_block_insts_plan_def] >>
  simp[stack_pop_def, listTheory.TAKE_APPEND2, listTheory.TAKE_APPEND1]
QED

Theorem residual_loop_state_zero:
  residual_loop_state 0 = residual_loop_entry
Proof
  simp[residual_loop_state_def] >>
  once_rewrite_tac[GSYM (cj 1 residual_loop_laps)] >> simp[]
QED

Theorem residual_loop_lap_symbolic:
  residual_loop_lap (residual_loop_state n) = residual_loop_state (SUC n)
Proof
  simp[residual_loop_lap_def, residual_loop_header_symbolic,
    residual_loop_body_symbolic]
QED

Theorem residual_loop_unbounded:
  FUNPOW residual_loop_lap n residual_loop_entry = residual_loop_state n
Proof
  Induct_on `n` >> simp[arithmeticTheory.FUNPOW_SUC,
    residual_loop_state_zero, residual_loop_lap_symbolic]
QED

Theorem residual_loop_splice:
  residual_loop_state m with
    <|ps_stack := (residual_loop_state n).ps_stack;
      ps_spilled := (residual_loop_state n).ps_spilled|> = residual_loop_state n
Proof
  simp[residual_loop_state_def]
QED

(* These universal equations validate physical residual introduction and replay
   for this no-spill loop only. They do not establish frozen lineage/DFS
   reachability or general cleanup, PHI, temporal coverage or spill producers. *)

(* Physical-boundary diagnostics (abstract stacks, not reachability claims).
   generate_block_plan cleans only BEFORE instructions, with one predecessor;
   clean_stack_plan additionally requires that predecessor to branch.
   generate_block_insts_plan has no cleanup between PHIs and regular ops.
   Regular ops remove consumed inputs and dead OUTPUTS only (not all dead
   cells); JMP restores/reorders its target and join_reached checks the suffix.
   Thus a multi-predecessor join has no implicit post-PHI normalization. *)
Definition physical_probe_def:
  physical_probe stk requests =
    (FST (popmany_plan requests
       ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := stk)),
     (SND (popmany_plan requests
       ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := stk))).ps_stack)
End

Theorem physical_probe_bulk_order:
  physical_probe [Var "a"; Var "d"; Var "e"; Var "b"] [Var "d"; Var "e"] =
    ([SOSwap 2; SOPop 2], [Var "a"; Var "b"]) /\
  physical_probe [Var "a"; Var "e"; Var "d"; Var "b"] [Var "d"; Var "e"] =
    ([SOSwap 2; SOPop 2], [Var "a"; Var "b"]) /\
  physical_probe [Var "a"; Var "d"; Var "e"; Var "b"] [Var "e"; Var "d"] =
    ([SOSwap 2; SOPop 2], [Var "a"; Var "b"])
Proof
  EVAL_TAC
QED

Theorem physical_probe_dead_position:
  FILTER (\op. MEM op [Var "a"; Var "b"])
    [Var "a"; Var "d"; Var "b"; Var "e"] = [Var "a"; Var "b"] /\
  physical_probe [Var "a"; Var "d"; Var "b"; Var "e"] [Var "d"; Var "e"] =
    ([SOPop 1; SOSwap 1; SOPop 1], [Var "a"; Var "b"]) /\
  physical_probe [Var "a"; Var "d"; Var "b"; Var "e"] [Var "e"; Var "d"] =
    ([SOPop 1; SOSwap 1; SOPop 1], [Var "a"; Var "b"])
Proof
  EVAL_TAC
QED

Theorem physical_probe_dead_identity:
  physical_probe [Var "a"; Var "x"; Var "b"] [Var "d"] =
    ([], [Var "a"; Var "x"; Var "b"]) /\
  physical_probe [Var "a"; Var "d"; Var "b"] [Var "d"] =
    ([SOSwap 1; SOPop 1], [Var "a"; Var "b"])
Proof
  EVAL_TAC
QED

Theorem physical_probe_prefix:
  physical_probe [dead_stack_marker; Var "a"; Var "d"; Var "b"] [Var "d"] =
    ([SOSwap 1; SOPop 1], [dead_stack_marker; Var "a"; Var "b"]) /\
  physical_probe [Var "x"; Var "a"; Var "d"; Var "b"] [Var "d"] =
    ([SOSwap 1; SOPop 1], [Var "x"; Var "a"; Var "b"])
Proof
  EVAL_TAC
QED

Definition physical_cleanup_fn_def:
  physical_cleanup_fn = mk_raw_function "physical-cleanup"
    [<| bb_label := "E"; bb_instructions :=
      [mk_inst 0 PARAM [Lit 0w] ["a"];
       mk_inst 1 PARAM [Lit 1w] ["b"];
       mk_inst 2 PARAM [Lit 2w] ["c"];
       mk_inst 3 PARAM [Lit 3w] ["d"];
       mk_inst 4 PARAM [Lit 4w] ["e"];
       mk_inst 5 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
       [mk_inst 6 RETURN [Var "a"; Var "b"] []] |>;
     <| bb_label := "B"; bb_instructions :=
       [mk_inst 7 RETURN [Var "d"; Var "e"] []] |>]
End

(* Exactly the physical/retained/to_cleanup filters of clean_stack_plan. *)
Theorem physical_cleanup_filters:
  FILTER (\op. IS_SOME (stack_get_depth op
      [Var "d"; Var "a"; Var "e"; Var "b"]))
      [Var "d"; Var "e"] = [Var "d"; Var "e"] /\
  FILTER (\op. below_all_live op ["a"; "b"]
      [Var "d"; Var "a"; Var "e"; Var "b"])
      [Var "d"; Var "e"] = [Var "d"] /\
  FILTER (\op. ~MEM op [Var "d"]) [Var "d"; Var "e"] = [Var "e"]
Proof
  EVAL_TAC
QED

Theorem physical_cleanup_actual:
  FST (clean_stack_plan (liveness_analyze physical_cleanup_fn)
    (cfg_analyze physical_cleanup_fn) physical_cleanup_fn
    (THE (lookup_block "A" physical_cleanup_fn.fn_blocks))
    ((init_cleanup_plan_state NONE [] 0 0) with
      <|ps_stack := [Var "d"; Var "a"; Var "e"; Var "b"];
        ps_cleanup_promised := T|>)) = [SOSwap 1; SOPop 1] /\
  (SND (clean_stack_plan (liveness_analyze physical_cleanup_fn)
    (cfg_analyze physical_cleanup_fn) physical_cleanup_fn
    (THE (lookup_block "A" physical_cleanup_fn.fn_blocks))
    ((init_cleanup_plan_state NONE [] 0 0) with
      <|ps_stack := [Var "d"; Var "a"; Var "e"; Var "b"];
        ps_cleanup_promised := T|>))).ps_stack =
      [dead_stack_marker; Var "a"; Var "b"]
Proof
  EVAL_TAC
QED

Theorem physical_probe_duplicate:
  physical_probe [Var "a"; Var "d"; Var "d"; Var "b"] [Var "d"] =
    ([SOSwap 1; SOPop 1], [Var "a"; Var "d"; Var "b"]) /\
  physical_probe [Var "a"; Var "d"; Var "d"; Var "b"] [Var "d"; Var "d"] =
    ([SOSwap 1; SOPop 1; SOSwap 1; SOPop 1], [Var "a"; Var "b"])
Proof
  EVAL_TAC
QED

(* Boundary decision: FILTER equality alone loses depths, multiplicity and
   request membership (physical_probe_dead_position/dead_identity/duplicate).
   A candidate for the REAL regular/JMP consumers is a common suffix of paired
   positions, modulo independently sized bottom prefixes, with equal identities
   at every future queried operand and paired but possibly different dead cells
   elsewhere. This is stronger than FILTER equality, weaker than raw equality.
   Its native producer must prove: every live operand's last-occurrence depth
   agrees; all queried identities are absent from both arbitrary prefixes;
   unequal paired identities cannot become later requests (including PHI retire,
   emit_input, and dead-output pops); relevant duplicates agree; equal spill
   maps/allocator and enough depth-window/cleanup bounds. Consumer preservation
   must include reorder/optimistic swap, not merely popmany.
   These are PROPOSED obligations, not facts certified by these examples.

   cleanup_retained_prefix_replay (fnPlanLineageInventory) is not directly
   applicable: lineage_core requires a common raw core and marker-only bottom
   prefixes; ALL_DISTINCT core, equal allocators, and exact physical coverage
   are also required. Endpoint marked/FILTER projection equality establishes
   none of those raw-core/prefix/coverage facts. For the next actual branch
   cleanup one must either establish that stronger reachable common core or
   prove cleanup respects the weaker paired relation. There is no cleanup
   at the join PHI endpoint that could supply it automatically. *)

(* Actual consumer probes: abstract states unless explicitly stated otherwise. *)
Definition physical_regular_def:
  physical_regular dfg stk = generate_regular_inst_plan
    (liveness_analyze physical_cleanup_fn) dfg (cfg_analyze physical_cleanup_fn)
    physical_cleanup_fn (mk_inst 90 MSTORE [Var "a"; Lit 0w] [])
    [] F F "A" ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := stk)
End

Definition physical_deep_def:
  physical_deep dead = [Var "a"] ++ REPLICATE 16 (Var "z") ++ [dead]
End

Theorem physical_select_tag:
  select_spill_candidate (physical_deep (Var "d")) [Var "a"] 17 1 = SOME 1 /\
  select_spill_candidate ([Var "a"] ++ REPLICATE 16 (Lit 0w) ++ [Var "d"])
    [Var "a"] 17 1 = NONE
Proof
  EVAL_TAC
QED

Theorem physical_deep_regular_dead_names:
  FST (physical_regular dfg_empty (physical_deep (Var "d"))) =
  FST (physical_regular dfg_empty (physical_deep (Var "e"))) /\
  (SND (physical_regular dfg_empty (physical_deep (Var "d")))).ps_alloc =
  (SND (physical_regular dfg_empty (physical_deep (Var "e")))).ps_alloc /\
  FLOOKUP (SND (physical_regular dfg_empty (physical_deep (Var "d")))).ps_spilled
    (Var "a") = NONE /\
  FLOOKUP (SND (physical_regular dfg_empty (physical_deep (Var "e")))).ps_spilled
    (Var "a") = NONE
Proof
  EVAL_TAC
QED

Definition physical_alias_dfg_def:
  physical_alias_dfg = dfg_build_function (mk_raw_function "alias"
    [<|bb_label := "E"; bb_instructions :=
      [mk_inst 0 ASSIGN [Var "a"] ["d"]]|>])
End

Theorem physical_equiv_observation:
  operand_equiv physical_alias_dfg (Var "a") (Var "d") /\
  ~operand_equiv physical_alias_dfg (Var "a") (Var "e") /\
  FST (reorder_one physical_alias_dfg [Var "a"] 0 (Var "a")
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "a"; Var "d"])) = [] /\
  FST (reorder_one physical_alias_dfg [Var "a"] 0 (Var "a")
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "a"; Var "e"])) =
      [SOSwap 1]
Proof
  EVAL_TAC
QED

Theorem physical_equiv_regular:
  FST (physical_regular physical_alias_dfg [Var "a"; Var "d"]) <>
  FST (physical_regular physical_alias_dfg [Var "a"; Var "e"])
Proof
  EVAL_TAC
QED

Theorem physical_deep_regular_tag:
  FST (physical_regular dfg_empty (physical_deep (Var "d"))) =
  FST (physical_regular dfg_empty
    ([Var "a"] ++ REPLICATE 16 (Lit 0w) ++ [Var "d"]))
Proof
  EVAL_TAC
QED

Definition physical_jmp_def:
  physical_jmp stk = generate_regular_inst_plan
    (liveness_analyze physical_cleanup_fn) dfg_empty (cfg_analyze physical_cleanup_fn)
    physical_cleanup_fn (mk_inst 91 JMP [Label "A"] [])
    ["a"; "b"] F F "E"
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack := stk)
End

Theorem physical_deep_jmp_names:
  FST (physical_jmp (physical_deep (Var "d") ++ [Var "b"])) =
  FST (physical_jmp (physical_deep (Var "e") ++ [Var "b"])) /\
  (SND (physical_jmp (physical_deep (Var "d") ++ [Var "b"]))).ps_alloc =
  (SND (physical_jmp (physical_deep (Var "e") ++ [Var "b"]))).ps_alloc /\
  FLOOKUP (SND (physical_jmp (physical_deep (Var "d") ++ [Var "b"]))).ps_spilled
    (Var "a") = NONE /\
  FLOOKUP (SND (physical_jmp (physical_deep (Var "e") ++ [Var "b"]))).ps_spilled
    (Var "a") = NONE
Proof
  EVAL_TAC
QED

Theorem physical_deep_prefix_ops:
  FST (physical_regular dfg_empty (physical_deep (Var "d"))) =
  FST (physical_regular dfg_empty ([Var "unqueried"] ++ physical_deep (Var "d")))
Proof
  EVAL_TAC
QED

(* Consumer premise audit: physical_equiv_regular REFUTES the candidate with
   only equal demand occurrences/depths and paired dead positions. First
   differing branch is operand_equiv in reorder_one, not cleanup. ASSIGN-root
   normalization, not PHI-class/name equality, decides that branch. Existing
   name-alias exclusions do not by their statements rule out ASSIGN roots.
   physical_select_tag shows the candidate-search tag observation differs,
   although physical_deep_regular_tag shows this particular MSTORE does not
   expose it (input emission first duplicates its demand). Preservation still
   needs matching candidate tags and forbidden membership when reduction runs. The equal-name-variant
   tests certify ops, allocator and demand lookup only; they do NOT assert
   native production, exact dead-key maps or arbitrary-prefix shielding.
   No universal relation is introduced on the basis of these equations. *)

Definition physical_native_fn_def:
  physical_native_fn = mk_raw_function "physical-native"
    [<|bb_label := "E"; bb_instructions :=
      [mk_inst 0 PARAM [Lit 0w] ["c"];
       mk_inst 1 PARAM [Lit 1w] ["a"];
       mk_inst 2 PARAM [Lit 2w] ["b"];
       mk_inst 11 PARAM [Lit 3w] ["k"];
       mk_inst 3 JNZ [Var "c"; Label "A"; Label "B"] []]|>;
     <|bb_label := "A"; bb_instructions := [mk_inst 4 JMP [Label "J"] []]|>;
     <|bb_label := "B"; bb_instructions := [mk_inst 5 JMP [Label "J"] []]|>;
     <|bb_label := "J"; bb_instructions :=
       [mk_inst 6 PHI [Label "A"; Var "a"; Label "B"; Var "b"] ["x"];
        mk_inst 7 MSTORE [Var "x"; Lit 0w] [];
        mk_inst 8 JNZ [Var "k"; Label "C"; Label "D"] []]|>;
     <|bb_label := "C"; bb_instructions := [mk_inst 9 STOP [] []]|>;
     <|bb_label := "D"; bb_instructions := [mk_inst 10 STOP [] []]|>]
End

Definition physical_native_edge_def:
  physical_native_edge edge = SND (THE (residual_matrix_step physical_native_fn edge
    (SND (THE (residual_matrix_step physical_native_fn "E"
      (init_cleanup_plan_state NONE [] 0 0))))))
End

Theorem physical_native_success:
  codegen_ready_fn physical_native_fn /\
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze physical_native_fn) (dfg_build_function physical_native_fn)
    (cfg_analyze physical_native_fn) NONE [] physical_native_fn 0 0) /\
  IS_SOME (residual_matrix_step physical_native_fn "J" (physical_native_edge "A")) /\
  IS_SOME (residual_matrix_step physical_native_fn "J" (physical_native_edge "B")) /\
  FST (THE (residual_matrix_step physical_native_fn "J" (physical_native_edge "A"))) =
  FST (THE (residual_matrix_step physical_native_fn "J" (physical_native_edge "B")))
Proof
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem physical_native_next_cleanup:
  EVERY (\edge.
    FST (clean_stack_plan (liveness_analyze physical_native_fn)
      (cfg_analyze physical_native_fn) physical_native_fn
      (THE (lookup_block "C" physical_native_fn.fn_blocks))
      (SND (THE (residual_matrix_step physical_native_fn "J"
        (physical_native_edge edge))))) = []) ["A"; "B"]
Proof
  EVAL_TAC
QED

(* The native fixture supplies successful analyzed calls from both arms and
   PHI+MSTORE+JNZ replay plus the next real branch cleanup. It does not certify
   the general frozen lineage/DFS relations. Its depths are shallow and its DFG
   has no ASSIGN alias at mismatched cells: those additional premises, not
   success alone, distinguish it from physical_equiv_regular. *)

Definition physical_reduce_def:
  physical_reduce dead = reduce_depth_plan 18 [Var "a"] (Var "a") 0 1
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
      [Var "a"] ++ REPLICATE 15 (Var "z") ++ [dead; Var "b"])
End

Theorem physical_reduce_dead_keys:
  FST (physical_reduce (Var "d")) = FST (physical_reduce (Var "e")) /\
  (SND (physical_reduce (Var "d"))).ps_alloc =
    (SND (physical_reduce (Var "e"))).ps_alloc /\
  FLOOKUP (SND (physical_reduce (Var "d"))).ps_spilled (Var "d") = SOME 0 /\
  FLOOKUP (SND (physical_reduce (Var "e"))).ps_spilled (Var "d") = NONE /\
  FLOOKUP (SND (physical_reduce (Var "e"))).ps_spilled (Var "e") = SOME 0
Proof
  EVAL_TAC
QED
