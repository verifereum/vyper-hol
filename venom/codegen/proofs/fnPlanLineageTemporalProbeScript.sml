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

(* A genuine skipped-use return: S does not execute any use of x, b or ti.
   The entry and latch remain JMP predecessors of H. *)
Definition bypass_pressure_fn_def:
  bypass_pressure_fn n = mk_raw_function "bypass_pressure"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["seed"];
         mk_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [mk_inst 2 PHI [Label "entry"; Var "seed"; Label "latch"; Var "back"] ["x"];
         mk_inst 3 JNZ [Lit 1w; Label "D"; Label "exit"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        MAPi (\i v. mk_inst (100+i) ASSIGN [Lit 1w] [v]) (TAKE n cycle_deep_names) ++
        [mk_inst 4 ADD [Lit 2w; Lit 3w] ["b"];
         mk_inst 15 ASSIGN [Lit 1w] ["carry"];
         mk_inst 5 JNZ [Lit 1w; Label "U"; Label "S"] []] |>;
     <| bb_label := "U"; bb_instructions :=
        [mk_inst 6 ISZERO [Var "x"] ["phi_out"];
         mk_inst 7 ISZERO [Var "b"] ["out"];
         mk_inst 8 ASSIGN [Var "phi_out"] ["unused_phi"];
         mk_inst 9 ASSIGN [Var "out"] ["unused_out"]] ++
        MAPi (\i v. mk_inst (200+i) ASSIGN [Var v] [STRCAT "u" v])
          (TAKE n cycle_deep_names) ++
        [mk_inst 10 JMP [Label "latch"] []] |>;
     <| bb_label := "S"; bb_instructions :=
        [mk_inst 11 JMP [Label "latch"] []] |>;
     <| bb_label := "latch"; bb_instructions :=
        [mk_inst 12 ASSIGN [Var "carry"] ["back"];
         mk_inst 13 JMP [Label "H"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 14 STOP [] []] |>]
End

Theorem bypass_pressure_ready:
  EVERY (\n. codegen_ready_fn (bypass_pressure_fn n) /\
    EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb.bb_instructions) (bypass_pressure_fn n).fn_blocks)
    [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  BETA_TAC >>
  conj_tac >- suspend "one" >>
  conj_tac >- suspend "sixteen" >> suspend "seventeen"
QED
Resume bypass_pressure_ready[one]:
  EVAL_TAC >> simp[]
QED
Resume bypass_pressure_ready[sixteen]:
  EVAL_TAC >> simp[]
QED
Resume bypass_pressure_ready[seventeen]:
  EVAL_TAC >> simp[]
QED
Finalise bypass_pressure_ready

Definition bypass_live_def:
  bypass_live n = liveness_analyze (bypass_pressure_fn n)
End
Definition bypass_dfg_def:
  bypass_dfg n = dfg_build_function (bypass_pressure_fn n)
End
Definition bypass_cfg_def:
  bypass_cfg n = cfg_analyze (bypass_pressure_fn n)
End
val _ = app (fn n => app (fn d => computeLib.add_funs
  [CONV_RULE (LAND_CONV (computeLib.RESTR_EVAL_CONV
    [``liveness_analyze``, ``dfg_build_function``, ``cfg_analyze``]))
    (REWRITE_RULE [d] (CONV_RULE (RAND_CONV EVAL) (Q.SPEC n d)))])
  [bypass_live_def, bypass_dfg_def, bypass_cfg_def]) [`1`, `16`, `17`];

Definition bypass_call_def:
  bypass_call n i ps = generate_block_plan
    (bypass_live n) (bypass_dfg n) (bypass_cfg n) (bypass_pressure_fn n)
    (EL i (bypass_pressure_fn n).fn_blocks) ps
End
Definition bypass_step_def:
  bypass_step n i ps = SND (THE (bypass_call n i ps))
End

Theorem bypass_entry_calls:
  EVERY (\n. bypass_call n 0 entry_probe_start =
    SOME ([SOLabel "entry"; SOPush (Lit 1w); SOPushLabel "H"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "seed"])) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED
val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] bypass_entry_calls));

Theorem bypass_header_calls:
  EVERY (\n. bypass_call n 1 (bypass_step n 0 entry_probe_start) =
    SOME ([SOLabel "H"; SOPoke 0 (Var "x"); SOPush (Lit 1w);
      SOPushLabel "D"; SOEmit "JUMPI"; SOPushLabel "exit"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "x"])) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  rpt conj_tac >> EVAL_TAC
QED
val _ = computeLib.add_funs (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL))) (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] bypass_header_calls)));

Theorem bypass_define_one:
  bypass_call 1 2 (bypass_step 1 1 (bypass_step 1 0 entry_probe_start)) =
    SOME ([SOLabel "D"; SOPush (Lit 1w); SOSwap 1; SOPush (Lit 3w);
      SOPush (Lit 2w); SOEmit "ADD"; SOSwap 1; SOPush (Lit 1w);
      SOPush (Lit 1w); SOPushLabel "U"; SOEmit "JUMPI";
      SOPushLabel "S"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "t0";Var "b";Var "x";Var "carry"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [CONV_RULE (LAND_CONV (RAND_CONV EVAL)) bypass_define_one];

Theorem bypass_skip_one:
  bypass_call 1 4 (bypass_step 1 2
    (bypass_step 1 1 (bypass_step 1 0 entry_probe_start))) =
    SOME ([SOLabel "S"; SOSwap 3; SOPop 3; SOPushLabel "latch"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "carry"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [CONV_RULE (LAND_CONV (RAND_CONV EVAL)) bypass_skip_one];

Definition bypass_defined_def:
  bypass_defined n = bypass_step n 2
    (bypass_step n 1 (bypass_step n 0 entry_probe_start))
End

Theorem bypass_consume_one:
  bypass_call 1 3 (bypass_defined 1) =
    SOME ([SOLabel "U"; SOSwap 1; SOEmit "ISZERO"; SOSwap 2; SOEmit "ISZERO";
      SOSwap 2; SOPop 1; SOSwap 1; SOPop 1; SOPop 1;
      SOPushLabel "latch"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "carry"])
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [CONV_RULE (LAND_CONV (RAND_CONV EVAL)) bypass_consume_one];

Theorem bypass_latch_one:
  bypass_call 1 5 (bypass_step 1 4 (bypass_defined 1)) =
    SOME ([SOLabel "latch"; SOPushLabel "H"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "back"])
Proof
  EVAL_TAC
QED

Theorem bypass_define_wide:
  EVERY (\n. bypass_call n 2 (bypass_step n 1 (bypass_step n 0 entry_probe_start)) =
    SOME ([SOLabel "D"] ++ FLAT (REPLICATE n [SOPush (Lit 1w); SOSwap 1]) ++
      [SOPush (Lit 3w); SOPush (Lit 2w); SOEmit "ADD"; SOSwap 1;
       SOPush (Lit 1w); SOPush (Lit 1w); SOPushLabel "U"; SOEmit "JUMPI";
       SOPushLabel "S"; SOEmit "JUMP"],
      entry_probe_start with ps_stack :=
        MAP Var (TAKE n cycle_deep_names) ++ [Var "b";Var "x";Var "carry"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
val _ = computeLib.add_funs (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL))) (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] bypass_define_wide)));

Theorem bypass_skip_wide:
  EVERY (\n. bypass_call n 4 (bypass_defined n) =
    SOME ([SOLabel "S"] ++ FLAT (REPLICATE (n+2) [SOSwap 1; SOPop 1]) ++
      [SOPushLabel "latch"; SOEmit "JUMP"],
      entry_probe_start with ps_stack := [Var "carry"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
val _ = computeLib.add_funs (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL))) (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] bypass_skip_wide)));

Theorem bypass_consume_wide:
  EVERY (\n. bypass_call n 3 (bypass_defined n) =
    SOME ([SOLabel "U"; SOSwap 1; SOEmit "ISZERO"; SOSwap 2; SOEmit "ISZERO";
      SOSwap 2; SOPop 1; SOSwap 1] ++
      (if n = 17 then [SOPop 1; SOSwap 1; SOSpill 0] ++
        REPLICATE 16 (SOPop 1) ++ [SORestore 0; SOPop 1]
       else REPLICATE (n+1) (SOPop 1)) ++
      [SOPushLabel "latch"; SOEmit "JUMP"],
      entry_probe_start with <| ps_stack := [Var "carry"];
        ps_alloc := if n = 17 then
          <| sa_free_slots := [0]; sa_next_offset := 32; sa_spill_base := 0 |>
          else entry_probe_start.ps_alloc |>)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
val _ = computeLib.add_funs (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL))) (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] bypass_consume_wide)));

Theorem bypass_returns:
  EVERY (\n. EVERY (\i.
    bypass_call n 5 (bypass_step n i (bypass_defined n)) =
      SOME ([SOLabel "latch"; SOPushLabel "H"; SOEmit "JUMP"],
        (bypass_step n i (bypass_defined n)) with ps_stack := [Var "back"]) /\
    bypass_call n 1 (entry_probe_start with <|
      ps_stack := (bypass_step n 5 (bypass_step n i (bypass_defined n))).ps_stack;
      ps_spilled := (bypass_step n 5 (bypass_step n i (bypass_defined n))).ps_spilled |>) =
      bypass_call n 1 (bypass_step n 0 entry_probe_start)) [3;4]) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  BETA_TAC >>
  conj_tac >- suspend "one" >>
  conj_tac >- suspend "sixteen" >> suspend "seventeen"
QED

Resume bypass_returns[one]:
  simp[bypass_step_def, bypass_consume_one,
    bypass_skip_one |> SRULE [GSYM bypass_defined_def]] >>
  conj_asm1_tac >- EVAL_TAC >> simp[] >> EVAL_TAC
QED
Resume bypass_returns[sixteen]:
  simp[bypass_step_def,
    bypass_consume_wide |> SRULE [listTheory.EVERY_DEF],
    bypass_skip_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_asm1_tac >- EVAL_TAC >> simp[] >> EVAL_TAC
QED
Resume bypass_returns[seventeen]:
  simp[bypass_step_def,
    bypass_consume_wide |> SRULE [listTheory.EVERY_DEF],
    bypass_skip_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- (conj_asm1_tac >- EVAL_TAC >> simp[] >> EVAL_TAC) >>
  conj_asm1_tac >- EVAL_TAC >> simp[] >> EVAL_TAC
QED
Finalise bypass_returns

Definition bypass_use_live_def:
  bypass_use_live n k = live_vars_at (bypass_live n) "U" k
End
val _ = app (fn n => app (fn k => computeLib.add_funs
  [CONV_RULE (LAND_CONV (computeLib.RESTR_EVAL_CONV [``live_vars_at``]))
    (REWRITE_RULE [bypass_use_live_def, bypass_live_def]
      (CONV_RULE (RAND_CONV EVAL)
        (SPEC (numSyntax.term_of_int k) (Q.SPEC n bypass_use_live_def))))])
  (List.tabulate (23, fn k => k))) [`16`, `17`];

(* Expose a native instruction prefix, including the block-entry cleanup.
   No input stack is manufactured: callers use the successful paths above. *)
Definition bypass_prefix_def:
  bypass_prefix n i 0 ps = SOME (clean_stack_plan
    (bypass_live n) (bypass_cfg n) (bypass_pressure_fn n)
    (EL i (bypass_pressure_fn n).fn_blocks) ps) /\
  bypass_prefix n i (SUC k) ps =
    case bypass_prefix n i k ps of NONE => NONE | SOME (ops,qs) =>
      case generate_inst_plan
        (bypass_live n) (bypass_dfg n) (bypass_cfg n) (bypass_pressure_fn n)
        (EL k (EL i (bypass_pressure_fn n).fn_blocks).bb_instructions)
        (live_vars_at (bypass_live n) (EL i (bypass_pressure_fn n).fn_blocks).bb_label (SUC k))
        (bb_is_halting (EL i (bypass_pressure_fn n).fn_blocks))
        (SUC k < LENGTH (EL i (bypass_pressure_fn n).fn_blocks).bb_instructions /\
          is_terminator (EL (SUC k)
            (EL i (bypass_pressure_fn n).fn_blocks).bb_instructions).inst_opcode)
        (EL i (bypass_pressure_fn n).fn_blocks).bb_label qs of
        NONE => NONE | SOME (chunk,rs) => SOME (ops ++ chunk,rs)
End

Theorem bypass_skip_prejmp:
  EVERY (\n. bypass_prefix n 4 0 (bypass_defined n) =
    SOME (if n = 1 then [SOSwap 3; SOPop 3]
      else FLAT (REPLICATE (n+2) [SOSwap 1; SOPop 1]),
      entry_probe_start with ps_stack := [Var "carry"])) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  BETA_TAC >> conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_four_wide:
  EVERY (\n. bypass_prefix n 3 4 (bypass_defined n) =
    SOME ([SOSwap 1; SOEmit "ISZERO"; SOSwap 2; SOEmit "ISZERO";
      SOSwap 2; SOPop 1; SOSwap 1; SOPop 1],
      entry_probe_start with ps_stack :=
        MAP Var (TAKE n cycle_deep_names) ++ [Var "carry"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  BETA_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED
val _ = computeLib.add_funs (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL)))
  (CONJUNCTS (SRULE [listTheory.EVERY_DEF] bypass_consume_four_wide)));

(* Bounded result and first-event ledger (not a universal producer):
   E0 entry, E1 H/PHI(seed->x), E2 D/ti definitions, E3 D/b,
   E4 D/carry, E5 D/JNZ, E6 S/cleanup OR U/consumers,
   E7 S-or-U/JMP(latch), E8 latch/carry->back, E9 latch/JMP(H),
   E10 rebase from successful latch stack/spills, E11 H/PHI(back->x).

   Checked whole-state table, all widths 1/16/17:
     E5: stack = ti ++ [b;x;carry], spills empty, each name once.
     E6 S after cleanup, before its successful JMP: [carry], spills empty.
     E7 either path: [carry], spills empty.
     E9: [back], spills empty. E11 finishes with [x], spills empty.
   Thus this bypass really skips every tracked use, but it does NOT retain
   a residual tracked resource: clean_stack_plan performs the reset at E6.
   Width17 U additionally spills/restores t16; its allocator has free=[0],
   next=32, unlike S's unchanged allocator. Reentry uses the actual E9 stack
   and spill projections with the destination's fields, not the source alloc.
   Whole stacks above give exact name counts (1 for listed names, 0 otherwise)
   and empty spills, not merely suffix counts.

   At a candidate first bad live-coverage event, coverage of its operands
   must come from a strictly earlier stable phase; these computations only
   supply that fact for this fixture. At a first bad unit-count definition,
   predefinition output absence must precede that definition, not follow from
   its proposed upper bound. The skipped path's absence is produced at E6
   here; an arbitrary residual-only path still lacks a universal producer.
   E11 selected back extinction can use E9's single occurrence and empty
   spill, together with output x<>back and back dead after PHI, all earlier
   than the result write. For a universal ordinary or PHI output freshness
   argument, the first-event premise must likewise precede the write; using
   the new output's unit bound there would be circular.

   Subsequent equations below now check U's exact immediate pre-JMP phase
   at all three widths, including the width17 restore/pop of spilled t16.
   They also check the explicit E11 PHI phase and rebased header state.
   Whole-function SOME is now checked separately at widths1/16/17 below,
   after caching the exact block equations at generate_block_plan's native
   interface. Repeated D tracked definitions and b/carry writes are also
   checked from the normalized reentry header, shared by both incoming paths.
   All results here remain bounded diagnostics, not universal freshness.
*)

Theorem bypass_consume_five_wide:
  EVERY (\n. bypass_prefix n 3 5 (bypass_defined n) =
    SOME ([SOSwap 1; SOEmit "ISZERO"; SOSwap 2; SOEmit "ISZERO";
      SOSwap 2; SOPop 1; SOSwap 1; SOPop 1] ++
      (if n = 17 then [SOSwap 1; SOSpill 0] else []) ++ [SOPop 1],
      entry_probe_start with <|
        ps_stack := Var "carry" :: MAP Var (TAKE 15 (TL cycle_deep_names));
        ps_spilled := if n = 17 then FEMPTY |+ (Var "t16",0) else FEMPTY;
        ps_alloc := <| sa_free_slots := []; sa_next_offset := if n = 17 then 32 else 0;
          sa_spill_base := 0 |> |>)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  simp[Once bypass_prefix_def,
    bypass_consume_four_wide |> SRULE [listTheory.EVERY_DEF]] >> EVAL_TAC
QED

val _ = computeLib.add_funs (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL)))
  (CONJUNCTS (SRULE [listTheory.EVERY_DEF] bypass_consume_five_wide)));

Theorem bypass_consume_six_wide:
  EVERY (\n. bypass_prefix n 3 6 (bypass_defined n) =
    SOME ([SOSwap 1; SOEmit "ISZERO"; SOSwap 2; SOEmit "ISZERO";
      SOSwap 2; SOPop 1; SOSwap 1; SOPop 1] ++
      (if n = 17 then [SOSwap 1; SOSpill 0] else []) ++ REPLICATE 2 (SOPop 1),
      entry_probe_start with <|
        ps_stack := [Var "carry";Var "t15"] ++ MAP Var (TAKE 13 (DROP 2 cycle_deep_names));
        ps_spilled := if n = 17 then FEMPTY |+ (Var "t16",0) else FEMPTY;
        ps_alloc := <| sa_free_slots := []; sa_next_offset := if n = 17 then 32 else 0;
          sa_spill_base := 0 |> |>)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  simp[Once bypass_prefix_def,
    bypass_consume_five_wide |> SRULE [listTheory.EVERY_DEF]] >> EVAL_TAC
QED

val _ = computeLib.add_funs (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL)))
  (CONJUNCTS (SRULE [listTheory.EVERY_DEF] bypass_consume_six_wide)));

(* Concrete audit notation only: j is the number of tracked POPs. The
   two list segments record the swap-last permutation, not a stable DROP. *)
Definition bypass_consumed_result_def:
  bypass_consumed_result (n:num) j =
    ([SOSwap 1; SOEmit "ISZERO"; SOSwap 2; SOEmit "ISZERO";
      SOSwap 2; SOPop 1; SOSwap 1; SOPop 1] ++
      (if n = 17 then [SOSwap 1; SOSpill 0] else []) ++ REPLICATE j (SOPop 1),
      entry_probe_start with <|
        ps_stack := [Var "carry"] ++
          MAP Var (if j <= 8 then
            REVERSE (DROP (17-j) (TAKE 16 cycle_deep_names)) ++
            TAKE (17-2*j) (DROP j cycle_deep_names)
            else REVERSE (TAKE (16-j) (DROP j cycle_deep_names)));
        ps_spilled := if n = 17 then FEMPTY |+ (Var "t16",0) else FEMPTY;
        ps_alloc := <| sa_free_slots := []; sa_next_offset := if n = 17 then 32 else 0;
          sa_spill_base := 0 |> |>)
End

Theorem bypass_consume_seven_wide:
  EVERY (\n. bypass_prefix n 3 7 (bypass_defined n) =
    SOME (bypass_consumed_result n 3)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``7:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_six_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_eight_wide:
  EVERY (\n. bypass_prefix n 3 8 (bypass_defined n) =
    SOME (bypass_consumed_result n 4)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``8:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_seven_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_nine_wide:
  EVERY (\n. bypass_prefix n 3 9 (bypass_defined n) =
    SOME (bypass_consumed_result n 5)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``9:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_eight_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_ten_wide:
  EVERY (\n. bypass_prefix n 3 10 (bypass_defined n) =
    SOME (bypass_consumed_result n 6)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``10:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_nine_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_eleven_wide:
  EVERY (\n. bypass_prefix n 3 11 (bypass_defined n) =
    SOME (bypass_consumed_result n 7)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``11:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_ten_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_twelve_wide:
  EVERY (\n. bypass_prefix n 3 12 (bypass_defined n) =
    SOME (bypass_consumed_result n 8)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``12:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_eleven_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_thirteen_wide:
  EVERY (\n. bypass_prefix n 3 13 (bypass_defined n) =
    SOME (bypass_consumed_result n 9)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``13:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_twelve_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_fourteen_wide:
  EVERY (\n. bypass_prefix n 3 14 (bypass_defined n) =
    SOME (bypass_consumed_result n 10)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``14:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_thirteen_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_fifteen_wide:
  EVERY (\n. bypass_prefix n 3 15 (bypass_defined n) =
    SOME (bypass_consumed_result n 11)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``15:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_fourteen_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_sixteen_wide:
  EVERY (\n. bypass_prefix n 3 16 (bypass_defined n) =
    SOME (bypass_consumed_result n 12)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``16:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_fifteen_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_seventeen_wide:
  EVERY (\n. bypass_prefix n 3 17 (bypass_defined n) =
    SOME (bypass_consumed_result n 13)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``17:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_sixteen_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_eighteen_wide:
  EVERY (\n. bypass_prefix n 3 18 (bypass_defined n) =
    SOME (bypass_consumed_result n 14)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``18:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_seventeen_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_nineteen_wide:
  EVERY (\n. bypass_prefix n 3 19 (bypass_defined n) =
    SOME (bypass_consumed_result n 15)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``19:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_eighteen_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_twenty_wide:
  EVERY (\n. bypass_prefix n 3 20 (bypass_defined n) =
    SOME (bypass_consumed_result n 16)) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``20:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_nineteen_wide |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_consume_prejmp_seventeen:
  bypass_prefix 17 3 21 (bypass_defined 17) =
    SOME ([SOSwap 1; SOEmit "ISZERO"; SOSwap 2; SOEmit "ISZERO";
      SOSwap 2; SOPop 1; SOSwap 1; SOPop 1; SOSwap 1; SOSpill 0] ++
      REPLICATE 16 (SOPop 1) ++ [SORestore 0; SOPop 1],
      entry_probe_start with <| ps_stack := [Var "carry"];
        ps_alloc := <| sa_free_slots := [0]; sa_next_offset := 32;
          sa_spill_base := 0 |> |>)
Proof
  pure_rewrite_tac [numLib.num_CONV ``21:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_consume_twenty_wide |> SRULE [listTheory.EVERY_DEF]] >> EVAL_TAC
QED

Theorem bypass_consume_prejmp_one:
  bypass_prefix 1 3 5 (bypass_defined 1) =
    SOME ([SOSwap 1; SOEmit "ISZERO"; SOSwap 2; SOEmit "ISZERO";
      SOSwap 2; SOPop 1; SOSwap 1; SOPop 1; SOPop 1],
      entry_probe_start with ps_stack := [Var "carry"])
Proof
  EVAL_TAC
QED

(* Cache the concrete native prefix calls, with original start states. *)
val _ = app (fn th => computeLib.add_funs
  (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL)))
    (CONJUNCTS (SRULE [listTheory.EVERY_DEF] th))))
  [bypass_consume_seven_wide, bypass_consume_eight_wide,
   bypass_consume_nine_wide, bypass_consume_ten_wide,
   bypass_consume_eleven_wide, bypass_consume_twelve_wide,
   bypass_consume_thirteen_wide, bypass_consume_fourteen_wide,
   bypass_consume_fifteen_wide, bypass_consume_sixteen_wide,
   bypass_consume_seventeen_wide, bypass_consume_eighteen_wide,
   bypass_consume_nineteen_wide, bypass_consume_twenty_wide];

Definition bypass_return_input_def:
  bypass_return_input n i = entry_probe_start with <|
    ps_stack := (bypass_step n 5 (bypass_step n i (bypass_defined n))).ps_stack;
    ps_spilled := (bypass_step n 5 (bypass_step n i (bypass_defined n))).ps_spilled |>
End

Theorem bypass_return_inputs:
  EVERY (\n. EVERY (\i. bypass_return_input n i =
    (entry_probe_start with ps_stack := [Var "back"])) [3;4]) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [bypass_return_input_def] >>
  pure_once_rewrite_tac [bypass_step_def] >>
  simp[bypass_returns |> SRULE [listTheory.EVERY_DEF]] >> EVAL_TAC
QED

val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] bypass_return_inputs));

Theorem bypass_return_phi_phase:
  EVERY (\n. EVERY (\i.
    bypass_prefix n 1 1 (bypass_return_input n i) =
      SOME ([SOPoke 0 (Var "x")], entry_probe_start with ps_stack := [Var "x"]))
    [3;4]) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >>
  BETA_TAC >> rpt conj_tac >> EVAL_TAC
QED

Theorem bypass_repeated_header_states:
  EVERY (\n. EVERY (\i. bypass_step n 1 (bypass_return_input n i) =
    (entry_probe_start with ps_stack := [Var "x"])) [3;4]) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  simp[bypass_return_inputs |> SRULE [listTheory.EVERY_DEF]] >>
  rpt conj_tac >> EVAL_TAC
QED
val _ = computeLib.add_funs (CONJUNCTS
  (SRULE [listTheory.EVERY_DEF] bypass_repeated_header_states));


Theorem bypass_redefine_one:
  bypass_prefix 1 2 1 (entry_probe_start with ps_stack := [Var "x"]) =
    SOME ([SOPush (Lit 1w); SOSwap 1],
      entry_probe_start with ps_stack := [Var "t0";Var "x"])
Proof
  EVAL_TAC
QED

Theorem bypass_redefine_four:
  EVERY (\n. bypass_prefix n 2 4 (entry_probe_start with ps_stack := [Var "x"]) =
    SOME (FLAT (REPLICATE 4 [SOPush (Lit 1w); SOSwap 1]),
      entry_probe_start with ps_stack :=
        MAP Var (TAKE 4 cycle_deep_names) ++ [Var "x"])) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
val _ = computeLib.add_funs (map (CONV_RULE (LAND_CONV (RAND_CONV EVAL)))
  (CONJUNCTS (SRULE [listTheory.EVERY_DEF] bypass_redefine_four)));

Definition bypass_redefine_result_def:
  bypass_redefine_result k = SOME
    (FLAT (REPLICATE k [SOPush (Lit 1w); SOSwap 1]),
      entry_probe_start with ps_stack := MAP Var (TAKE k cycle_deep_names) ++ [Var "x"])
End

Theorem bypass_redefine_five:
  EVERY (\n. bypass_prefix n 2 5 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 5) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``5:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_four |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_six:
  EVERY (\n. bypass_prefix n 2 6 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 6) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``6:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_five |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_seven:
  EVERY (\n. bypass_prefix n 2 7 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 7) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``7:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_six |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_eight:
  EVERY (\n. bypass_prefix n 2 8 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 8) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``8:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_seven |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_nine:
  EVERY (\n. bypass_prefix n 2 9 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 9) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``9:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_eight |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_ten:
  EVERY (\n. bypass_prefix n 2 10 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 10) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``10:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_nine |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_eleven:
  EVERY (\n. bypass_prefix n 2 11 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 11) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``11:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_ten |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_twelve:
  EVERY (\n. bypass_prefix n 2 12 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 12) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``12:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_eleven |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_thirteen:
  EVERY (\n. bypass_prefix n 2 13 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 13) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``13:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_twelve |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_fourteen:
  EVERY (\n. bypass_prefix n 2 14 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 14) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``14:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_thirteen |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_fifteen:
  EVERY (\n. bypass_prefix n 2 15 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 15) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``15:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_fourteen |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_sixteen_wide:
  EVERY (\n. bypass_prefix n 2 16 (entry_probe_start with ps_stack := [Var "x"]) =
    bypass_redefine_result 16) [16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_rewrite_tac [numLib.num_CONV ``16:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_fifteen |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_seventeen:
  bypass_prefix 17 2 17 (entry_probe_start with ps_stack := [Var "x"]) =
    SOME (FLAT (REPLICATE 17 [SOPush (Lit 1w); SOSwap 1]),
      entry_probe_start with ps_stack :=
        MAP Var (TAKE 17 cycle_deep_names) ++ [Var "x"])
Proof
  pure_rewrite_tac [numLib.num_CONV ``17:num``] >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_sixteen_wide |> SRULE [listTheory.EVERY_DEF]] >> EVAL_TAC
QED

Theorem bypass_repeated_definitions:
  EVERY (\n. EVERY (\i.
    bypass_prefix n 2 n (bypass_step n 1 (bypass_return_input n i)) =
      SOME (FLAT (REPLICATE n [SOPush (Lit 1w); SOSwap 1]),
        entry_probe_start with ps_stack :=
          MAP Var (TAKE n cycle_deep_names) ++ [Var "x"])) [3;4]) [1;16;17]
Proof
  simp[listTheory.EVERY_DEF,
    bypass_repeated_header_states |> SRULE [listTheory.EVERY_DEF],
    bypass_redefine_one, bypass_redefine_seventeen,
    bypass_redefine_sixteen_wide |> SRULE [listTheory.EVERY_DEF, bypass_redefine_result_def]] >> EVAL_TAC
QED

(* Reuse the certified block equations at the native DFS interface. *)
val _ = app (fn th => computeLib.add_funs
  (map (CONV_RULE (LAND_CONV
    (computeLib.RESTR_EVAL_CONV [``generate_block_plan``])))
    (CONJUNCTS (SRULE [listTheory.EVERY_DEF] th))))
  [bypass_entry_calls, bypass_header_calls, bypass_define_one,
   bypass_define_wide, bypass_consume_one, bypass_consume_wide,
   bypass_skip_one, bypass_skip_wide];

Theorem bypass_whole_one:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (bypass_live 1) (bypass_dfg 1) (bypass_cfg 1) NONE []
    (bypass_pressure_fn 1) 0 0)
Proof
  EVAL_TAC
QED

Theorem bypass_whole_sixteen:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (bypass_live 16) (bypass_dfg 16) (bypass_cfg 16) NONE []
    (bypass_pressure_fn 16) 0 0)
Proof
  EVAL_TAC
QED

Theorem bypass_whole_seventeen:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (bypass_live 17) (bypass_dfg 17) (bypass_cfg 17) NONE []
    (bypass_pressure_fn 17) 0 0)
Proof
  EVAL_TAC
QED

Theorem bypass_redefine_b:
  EVERY (\n. bypass_prefix n 2 (SUC n)
    (entry_probe_start with ps_stack := [Var "x"]) =
    SOME (FLAT (REPLICATE n [SOPush (Lit 1w); SOSwap 1]) ++
      [SOPush (Lit 3w); SOPush (Lit 2w); SOEmit "ADD"; SOSwap 1],
      entry_probe_start with ps_stack :=
        MAP Var (TAKE n cycle_deep_names) ++ [Var "b";Var "x"])) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_one, bypass_redefine_seventeen,
    bypass_redefine_sixteen_wide |> SRULE [listTheory.EVERY_DEF, bypass_redefine_result_def]] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_redefine_carry:
  EVERY (\n. bypass_prefix n 2 (SUC (SUC n))
    (entry_probe_start with ps_stack := [Var "x"]) =
    SOME (FLAT (REPLICATE n [SOPush (Lit 1w); SOSwap 1]) ++
      [SOPush (Lit 3w); SOPush (Lit 2w); SOEmit "ADD"; SOSwap 1; SOPush (Lit 1w)],
      entry_probe_start with ps_stack :=
        MAP Var (TAKE n cycle_deep_names) ++ [Var "b";Var "x";Var "carry"])) [1;16;17]
Proof
  pure_rewrite_tac [listTheory.EVERY_DEF, boolTheory.AND_CLAUSES] >> BETA_TAC >>
  pure_once_rewrite_tac [bypass_prefix_def] >>
  simp[bypass_redefine_b |> SRULE [listTheory.EVERY_DEF]] >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem bypass_repeated_last_definitions:
  EVERY (\n. EVERY (\i. EVERY (\k.
    bypass_prefix n 2 k (bypass_step n 1 (bypass_return_input n i)) =
      bypass_prefix n 2 k (entry_probe_start with ps_stack := [Var "x"]))
    [SUC n;SUC (SUC n)]) [3;4]) [1;16;17]
Proof
  simp[listTheory.EVERY_DEF,
    bypass_repeated_header_states |> SRULE [listTheory.EVERY_DEF]]
QED
