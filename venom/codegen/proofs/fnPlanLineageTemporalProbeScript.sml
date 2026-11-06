Theory fnPlanLineageTemporalProbe
Ancestors
  fnPlanLineageCycleProbe fnPlanLineageStageAudit fnPlanLineageNativePhases
  codegenReadyCompute stackPlanGen livenessDefs
Libs wordsLib

(* One bounded family, with both PHI-result x and ordinary-result b revisited.
   All incoming states below will come from actual native block calls. *)
Definition temporal_pressure_fn_def:
  temporal_pressure_fn n = mk_raw_function "temporal_pressure"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["seed"];
         mk_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [mk_inst 2 PHI [Label "entry"; Var "seed"; Label "latch"; Var "back"] ["x"];
         mk_inst 3 JNZ [Lit 1w; Label "body"; Label "exit"] []] |>;
     <| bb_label := "body"; bb_instructions :=
        MAPi (\i v. mk_inst (100+i) ASSIGN [Lit 1w] [v]) (TAKE n cycle_deep_names) ++
        [mk_inst 4 ADD [Lit 2w; Lit 3w] ["b"];
         mk_inst 5 ASSIGN [Lit 0w] ["padding"];
         mk_inst 6 ISZERO [Var "t0"] ["deep_out"];
         mk_inst 7 ISZERO [Var "x"] ["phi_out"];
         mk_inst 8 ISZERO [Var "b"] ["out"];
         mk_inst 9 ASSIGN [Var "out"] ["unused_out"];
         mk_inst 10 ASSIGN [Var "deep_out"] ["unused_deep"];
         mk_inst 11 ASSIGN [Var "phi_out"] ["unused_phi"];
         mk_inst 12 ASSIGN [Var "b"] ["unused_b"];
         mk_inst 13 ASSIGN [Var "padding"] ["unused_padding"]] ++
        MAPi (\i v. mk_inst (200+i) ASSIGN [Var v] [STRCAT "u" v])
          (TL (TAKE n cycle_deep_names)) ++
        [mk_inst 14 JMP [Label "latch"] []] |>;
     <| bb_label := "latch"; bb_instructions :=
        [mk_inst 15 ASSIGN [Lit 1w] ["back"];
         mk_inst 16 JMP [Label "H"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 17 STOP [] []] |>]
End

Theorem temporal_pressure_ready:
  EVERY (\n. codegen_ready_fn (temporal_pressure_fn n) /\
    EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb.bb_instructions) (temporal_pressure_fn n).fn_blocks)
    [1;16;17]
Proof
  EVAL_TAC >> simp[]
QED

val _ = computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY, listTheory.SET_TO_LIST_SING,
  finite_mapTheory.DRESTRICT_FUPDATE,
  finite_mapTheory.DRESTRICT_FEMPTY, pred_setTheory.IN_COMPL,
  pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY];

Definition temporal_call_def:
  temporal_call n i ps = generate_block_plan
    (liveness_analyze (temporal_pressure_fn n))
    (dfg_build_function (temporal_pressure_fn n))
    (cfg_analyze (temporal_pressure_fn n)) (temporal_pressure_fn n)
    (EL i (temporal_pressure_fn n).fn_blocks) ps
End

Definition temporal_step_def:
  temporal_step n i ps = SND (THE (temporal_call n i ps))
End

Theorem temporal_entry_one:
  temporal_call 1 0 entry_probe_start =
    SOME ([SOLabel "entry"; SOPush (Lit 1w); SOPushLabel "H"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "seed"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [temporal_entry_one];

Theorem temporal_header_one:
  temporal_call 1 1 (entry_probe_start with ps_stack := [Var "seed"]) =
    SOME ([SOLabel "H"; SOPoke 0 (Var "x"); SOPush (Lit 1w);
      SOPushLabel "body"; SOEmit "JUMPI"; SOPushLabel "exit"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "x"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [temporal_header_one];

Theorem temporal_body_one:
  temporal_call 1 2 (entry_probe_start with ps_stack := [Var "x"]) =
    SOME ([SOLabel "body"; SOPush (Lit 1w); SOPush (Lit 3w); SOPush (Lit 2w);
      SOEmit "ADD"; SOSwap 1; SOPush (Lit 0w); SOSwap 1; SOEmit "ISZERO";
      SOSwap 3; SOEmit "ISZERO"; SOSwap 3; SODup 3; SOEmit "ISZERO";
      SOPop 1; SOPop 1; SOSwap 2; SOPop 1; SOPop 1; SOPop 1;
      SOPushLabel "latch"; SOEmit "JUMP"], entry_probe_start)
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [temporal_body_one];

Theorem temporal_latch_one:
  temporal_call 1 3 entry_probe_start =
    SOME ([SOLabel "latch"; SOPush (Lit 1w); SOPushLabel "H"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "back"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [temporal_latch_one];

Theorem temporal_header_one_revisit:
  temporal_call 1 1 (temporal_step 1 3 entry_probe_start) =
    temporal_call 1 1 (temporal_step 1 0 entry_probe_start)
Proof
  EVAL_TAC
QED

(* Normalize the arguments of the already checked block equations, so the
   evaluator can match them after evaluating the DFS call arguments. *)
val _ = computeLib.add_funs (map
  (CONV_RULE (LAND_CONV
     (computeLib.RESTR_EVAL_CONV [``generate_block_plan``])) o
   REWRITE_RULE [temporal_call_def])
  [temporal_entry_one, temporal_header_one, temporal_body_one, temporal_latch_one]);

Definition temporal_aux_def:
  temporal_aux n labels visited ps = generate_fn_plan_aux
    (liveness_analyze (temporal_pressure_fn n))
    (dfg_build_function (temporal_pressure_fn n))
    (cfg_analyze (temporal_pressure_fn n)) (temporal_pressure_fn n)
    labels visited ps
End

Theorem temporal_aux_latch_one:
  temporal_aux 1 ["latch"] ["body";"H";"entry"] entry_probe_start =
    SOME ([SOLabel "latch"; SOPush (Lit 1w); SOPushLabel "H"; SOEmit "JUMP"],
      ["latch";"body";"H";"entry"], entry_probe_start with ps_stack := [Var "back"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [CONV_RULE (LAND_CONV
  (computeLib.RESTR_EVAL_CONV [``generate_fn_plan_aux``]))
  (REWRITE_RULE [temporal_aux_def] temporal_aux_latch_one)];

Theorem temporal_aux_body_one:
  temporal_aux 1 ["body"] ["H";"entry"]
    (entry_probe_start with ps_stack := [Var "x"]) =
  SOME (FST (THE (temporal_call 1 2
      (entry_probe_start with ps_stack := [Var "x"]))) ++
    FST (THE (temporal_call 1 3 entry_probe_start)),
    ["latch";"body";"H";"entry"], entry_probe_start)
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [CONV_RULE (LAND_CONV
  (computeLib.RESTR_EVAL_CONV [``generate_fn_plan_aux``]))
  (REWRITE_RULE [temporal_aux_def] temporal_aux_body_one)];

Theorem temporal_exit_one:
  temporal_call 1 4 (entry_probe_start with ps_stack := [Var "x"]) =
    SOME ([SOLabel "exit"; SOPop 1; SOEmit "STOP"], entry_probe_start)
Proof
  EVAL_TAC
QED

Theorem temporal_aux_header_one:
  temporal_aux 1 ["H"] ["entry"]
    (entry_probe_start with ps_stack := [Var "seed"]) =
  SOME (FST (THE (temporal_call 1 1
      (entry_probe_start with ps_stack := [Var "seed"]))) ++
    [SOLabel "exit"; SOPop 1; SOEmit "STOP"] ++
    FST (THE (temporal_aux 1 ["body"] ["H";"entry"]
      (entry_probe_start with ps_stack := [Var "x"]))),
    ["latch";"body";"exit";"H";"entry"],
    entry_probe_start with ps_stack := [Var "x"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [CONV_RULE (LAND_CONV
  (computeLib.RESTR_EVAL_CONV [``generate_fn_plan_aux``]))
  (REWRITE_RULE [temporal_aux_def] temporal_aux_header_one)];

Theorem temporal_plan_one_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze (temporal_pressure_fn 1))
    (dfg_build_function (temporal_pressure_fn 1))
    (cfg_analyze (temporal_pressure_fn 1)) NONE [] (temporal_pressure_fn 1) 0 0)
Proof
  EVAL_TAC
QED

Theorem temporal_pressure_entry_calls:
  EVERY (\n. temporal_call n 0 entry_probe_start =
    SOME ([SOLabel "entry"; SOPush (Lit 1w); SOPushLabel "H"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "seed"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem temporal_pressure_header_calls:
  EVERY (\n. temporal_call n 1
      (entry_probe_start with ps_stack := [Var "seed"]) =
    SOME ([SOLabel "H"; SOPoke 0 (Var "x"); SOPush (Lit 1w);
      SOPushLabel "body"; SOEmit "JUMPI"; SOPushLabel "exit"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "x"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED


(* Prefixes retain both emitted chunks and the full native state.  The flags
   and next-live query are always those of the original, untruncated body. *)
Definition temporal_prefix_def:
  temporal_prefix n 0 = SOME (clean_stack_plan
    (liveness_analyze (temporal_pressure_fn n))
    (cfg_analyze (temporal_pressure_fn n)) (temporal_pressure_fn n)
    (EL 2 (temporal_pressure_fn n).fn_blocks)
    (entry_probe_start with ps_stack := [Var "x"])) /\
  temporal_prefix n (SUC k) =
    case temporal_prefix n k of NONE => NONE | SOME (ops,ps) =>
      case generate_inst_plan
        (liveness_analyze (temporal_pressure_fn n))
        (dfg_build_function (temporal_pressure_fn n))
        (cfg_analyze (temporal_pressure_fn n)) (temporal_pressure_fn n)
        (EL k (EL 2 (temporal_pressure_fn n).fn_blocks).bb_instructions)
        (live_vars_at (liveness_analyze (temporal_pressure_fn n)) "body" (SUC k)) F
        (is_terminator
          (EL (SUC k) (EL 2 (temporal_pressure_fn n).fn_blocks).bb_instructions).inst_opcode)
        "body" ps of NONE => NONE | SOME (chunk,ps') => SOME (ops ++ chunk,ps')
End

Theorem temporal_prefix_zero:
  EVERY (\n. temporal_prefix n 0 = SOME ([],
    entry_probe_start with ps_stack := [Var "x"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED

val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] temporal_prefix_zero));

Theorem temporal_prefix_one:
  EVERY (\n. temporal_prefix n 1 =
    SOME ([SOPush (Lit 1w)],
      entry_probe_start with ps_stack := [Var "x";Var "t0"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED

val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] temporal_prefix_one));


Definition temporal_header_input_def:
  temporal_header_input n 0 = temporal_step n 0 entry_probe_start /\
  temporal_header_input n (SUC k) =
    entry_probe_start with <|
      ps_stack := (temporal_step n 3 (temporal_step n 2
        (temporal_step n 1 (temporal_header_input n k)))).ps_stack;
      ps_spilled := (temporal_step n 3 (temporal_step n 2
        (temporal_step n 1 (temporal_header_input n k)))).ps_spilled |>
End

Theorem temporal_header_one_back:
  temporal_call 1 1 (entry_probe_start with ps_stack := [Var "back"]) =
    temporal_call 1 1 (entry_probe_start with ps_stack := [Var "seed"])
Proof
  EVAL_TAC
QED

(* Width one makes no allocations: every DFS input's non-resource fields
   equal entry_probe_start, so the resource splice is the native edge rebase.
   All three component calls, not just their THE projections, are checked. *)
Theorem temporal_three_visits_one:
  EVERY (\k.
    temporal_header_input 1 k =
      (entry_probe_start with ps_stack := [Var (if k = 0 then "seed" else "back")]) /\
    temporal_call 1 1 (temporal_header_input 1 k) =
      SOME ([SOLabel "H"; SOPoke 0 (Var "x"); SOPush (Lit 1w);
        SOPushLabel "body"; SOEmit "JUMPI"; SOPushLabel "exit"; SOEmit "JUMP"],
        entry_probe_start with ps_stack := [Var "x"]) /\
    temporal_call 1 2 (temporal_step 1 1 (temporal_header_input 1 k)) =
      temporal_call 1 2 (entry_probe_start with ps_stack := [Var "x"]) /\
    temporal_call 1 3 (temporal_step 1 2
      (temporal_step 1 1 (temporal_header_input 1 k))) =
      SOME ([SOLabel "latch"; SOPush (Lit 1w); SOPushLabel "H"; SOEmit "JUMP"],
        entry_probe_start with ps_stack := [Var "back"])) [0;1;2]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``1:num``, numLib.num_CONV ``2:num``,
    temporal_header_input_def] >>
  simp[temporal_step_def, temporal_entry_one, temporal_header_one,
    temporal_header_one_back, temporal_body_one, temporal_latch_one]
QED
