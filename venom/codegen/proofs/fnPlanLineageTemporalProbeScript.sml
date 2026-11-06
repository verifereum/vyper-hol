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
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  BETA_TAC >>
  conj_tac >- suspend "width_one" >>
  conj_tac >- suspend "width_sixteen" >> suspend "width_seventeen"
QED

Resume temporal_pressure_ready[width_one]:
  EVAL_TAC >> simp[]
QED
Resume temporal_pressure_ready[width_sixteen]:
  EVAL_TAC >> simp[]
QED
Resume temporal_pressure_ready[width_seventeen]:
  EVAL_TAC >> simp[]
QED
Finalise temporal_pressure_ready

val _ = computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY, listTheory.SET_TO_LIST_SING,
  finite_mapTheory.DRESTRICT_FUPDATE,
  finite_mapTheory.DRESTRICT_FEMPTY, pred_setTheory.IN_COMPL,
  pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY];

(* Normalize probe analysis definitions once and register the concrete native
   calls with CBV; the cached RHSs are full analysis records. *)
Definition temporal_live_def:
  temporal_live n = liveness_analyze (temporal_pressure_fn n)
End
Definition temporal_dfg_def:
  temporal_dfg n = dfg_build_function (temporal_pressure_fn n)
End
Definition temporal_cfg_def:
  temporal_cfg n = cfg_analyze (temporal_pressure_fn n)
End

val _ = app (fn n => app (fn d => computeLib.add_funs
  [CONV_RULE (LAND_CONV (computeLib.RESTR_EVAL_CONV
    [``liveness_analyze``, ``dfg_build_function``, ``cfg_analyze``]))
    (REWRITE_RULE [d] (CONV_RULE (RAND_CONV EVAL) (Q.SPEC n d)))])
  [temporal_live_def, temporal_dfg_def, temporal_cfg_def]) [`16`, `17`];

Definition temporal_body_live_def:
  temporal_body_live n k = live_vars_at (temporal_live n) "body" k
End

val _ = app (fn n => app (fn k => computeLib.add_funs
  [CONV_RULE (LAND_CONV (computeLib.RESTR_EVAL_CONV [``live_vars_at``]))
    (REWRITE_RULE [temporal_body_live_def, temporal_live_def]
      (CONV_RULE (RAND_CONV EVAL)
        (SPEC (numSyntax.term_of_int k)
          (Q.SPEC n temporal_body_live_def))))])
  (List.tabulate (45, fn k => k))) [`16`, `17`];

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

Theorem temporal_prefix_two:
  EVERY (\n. temporal_prefix n 2 =
    SOME (REPLICATE 2 (SOPush (Lit 1w)),
      entry_probe_start with ps_stack := [Var "x";Var "t0";Var "t1"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED

val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] temporal_prefix_two));
Theorem temporal_prefix_four:
  EVERY (\n. temporal_prefix n 4 =
    SOME (REPLICATE 4 (SOPush (Lit 1w)),
      entry_probe_start with ps_stack :=
        [Var "x";Var "t0";Var "t1";Var "t2";Var "t3"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED

val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] temporal_prefix_four));


Theorem temporal_prefix_eight:
  EVERY (\n. temporal_prefix n 8 =
    SOME (REPLICATE 8 (SOPush (Lit 1w)),
      entry_probe_start with ps_stack :=
        Var "x" :: MAP Var (TAKE 8 cycle_deep_names))) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED

val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] temporal_prefix_eight));



Theorem temporal_prefix_sixteen:
  EVERY (\n. temporal_prefix n 16 =
    SOME (REPLICATE 16 (SOPush (Lit 1w)),
      entry_probe_start with ps_stack :=
        Var "x" :: MAP Var (TAKE 16 cycle_deep_names))) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED

val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] temporal_prefix_sixteen));
Theorem temporal_pressure_add_sixteen:
  temporal_prefix 16 17 =
    SOME (REPLICATE 16 (SOPush (Lit 1w)) ++
      [SOPush (Lit 3w); SOPush (Lit 2w); SOEmit "ADD"; SOSwap 16],
      entry_probe_start with ps_stack :=
        [Var "x";Var "b"] ++ MAP Var (TAKE 15 (TL cycle_deep_names)) ++ [Var "t0"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [temporal_pressure_add_sixteen];

Theorem temporal_pressure_add_seventeen:
  temporal_prefix 17 18 =
    SOME (REPLICATE 17 (SOPush (Lit 1w)) ++
      [SOPush (Lit 3w); SOPush (Lit 2w); SOEmit "ADD"] ++
      MAP SOSpill (GENLIST (\i. 32*i) 18) ++
      MAP SORestore ([0] ++ REVERSE (GENLIST (\i. 32*(i+1)) 16) ++ [544]),
      entry_probe_start with <|
        ps_stack := [Var "x";Var "b"] ++ MAP Var (TL cycle_deep_names) ++ [Var "t0"];
        ps_alloc := <| sa_free_slots := GENLIST (\i. 32*i) 18;
          sa_next_offset := 576; sa_spill_base := 0 |> |>)
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [temporal_pressure_add_seventeen];

Definition temporal_tail_def:
  temporal_tail n k = generate_block_insts_plan
    (temporal_live n) (temporal_dfg n) (temporal_cfg n) (temporal_pressure_fn n)
    "body" F 0 (LENGTH (EL 2 (temporal_pressure_fn n).fn_blocks).bb_instructions)
    k (DROP k (EL 2 (temporal_pressure_fn n).fn_blocks).bb_instructions)
    (SND (THE (temporal_prefix n k)))
End

(* The first unresolved computation is enumeration of a two-element spill
   domain at the release after instruction 11 (the phi_out consumer).  Both
   names remain live.  This equation records the native residual, not NONE. *)
Definition temporal_release_input_def:
  temporal_release_input = entry_probe_start with <|
    ps_stack := [Var "padding";Var "b"] ++ MAP Var (TAKE 14 (TL cycle_deep_names));
    ps_spilled := FEMPTY |+ (Var "t16",480) |+ (Var "t15",512);
    ps_alloc := <| sa_free_slots := [608;576] ++ GENLIST (\i. 32*i) 15 ++ [544];
      sa_next_offset := 640; sa_spill_base := 0 |> |>
End

Theorem temporal_pressure_release_residual:
  IS_SOME (temporal_prefix 17 25) /\
  SND (THE (temporal_prefix 17 25)) =
    release_dead_spills (temporal_body_live 17 25) temporal_release_input
Proof
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Definition temporal_body_end_sixteen_def:
  temporal_body_end_sixteen = entry_probe_start with ps_alloc :=
    <| sa_free_slots := REVERSE (GENLIST (\i. 32*(i+2)) 17) ++ [0;32];
       sa_next_offset := 608; sa_spill_base := 0 |>
End

Theorem temporal_tail_sixteen:
  temporal_tail 16 17 = SOME (FST (THE (temporal_tail 16 17)), temporal_body_end_sixteen)
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [CONV_RULE
  (LAND_CONV (computeLib.RESTR_EVAL_CONV [``generate_block_insts_plan``]))
  (REWRITE_RULE [temporal_tail_def]
    (CONV_RULE (RAND_CONV EVAL) temporal_tail_sixteen))];

Theorem temporal_body_sixteen:
  temporal_call 16 2 (entry_probe_start with ps_stack := [Var "x"]) =
    SOME ([SOLabel "body"] ++ FST (THE (temporal_prefix 16 17)) ++
      FST (THE (temporal_tail 16 17)), temporal_body_end_sixteen)
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs (map
  (CONV_RULE (LAND_CONV
      (computeLib.RESTR_EVAL_CONV [``generate_block_plan``])) o
   REWRITE_RULE [temporal_call_def] o CONV_RULE (RAND_CONV EVAL))
  (temporal_body_sixteen ::
    CONJUNCTS (SRULE [listTheory.EVERY_DEF] temporal_pressure_entry_calls) @
    CONJUNCTS (SRULE [listTheory.EVERY_DEF] temporal_pressure_header_calls)));

Theorem temporal_plan_sixteen_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (temporal_live 16) (temporal_dfg 16) (temporal_cfg 16)
    NONE [] (temporal_pressure_fn 16) 0 0)
Proof
  EVAL_TAC
QED



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

Theorem temporal_latch_sixteen:
  temporal_call 16 3 temporal_body_end_sixteen =
    SOME ([SOLabel "latch"; SOPush (Lit 1w); SOPushLabel "H"; SOEmit "JUMP"],
      temporal_body_end_sixteen with ps_stack := [Var "back"])
Proof
  EVAL_TAC
QED

Theorem temporal_header_sixteen_back:
  temporal_call 16 1 (entry_probe_start with ps_stack := [Var "back"]) =
    temporal_call 16 1 (entry_probe_start with ps_stack := [Var "seed"])
Proof
  EVAL_TAC
QED

Theorem temporal_three_visits_sixteen:
  EVERY (\k.
    temporal_header_input 16 k =
      (entry_probe_start with ps_stack := [Var (if k = 0 then "seed" else "back")]) /\
    temporal_call 16 1 (temporal_header_input 16 k) =
      temporal_call 16 1 (entry_probe_start with ps_stack := [Var "seed"]) /\
    temporal_call 16 2 (temporal_step 16 1 (temporal_header_input 16 k)) =
      SOME ([SOLabel "body"] ++ FST (THE (temporal_prefix 16 17)) ++
        FST (THE (temporal_tail 16 17)), temporal_body_end_sixteen) /\
    temporal_call 16 3 (temporal_step 16 2
      (temporal_step 16 1 (temporal_header_input 16 k))) =
      SOME ([SOLabel "latch"; SOPush (Lit 1w); SOPushLabel "H"; SOEmit "JUMP"],
        temporal_body_end_sixteen with ps_stack := [Var "back"])) [0;1;2]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``1:num``, numLib.num_CONV ``2:num``,
    temporal_header_input_def] >>
  `temporal_body_end_sixteen.ps_spilled = entry_probe_start.ps_spilled` by EVAL_TAC >>
  simp[temporal_step_def, temporal_pressure_entry_calls |> SRULE [listTheory.EVERY_DEF],
    temporal_pressure_header_calls |> SRULE [listTheory.EVERY_DEF],
    temporal_header_sixteen_back, temporal_body_sixteen, temporal_latch_sixteen]
QED
