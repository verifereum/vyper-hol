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

(* Bounded deep variant: seventeen t names build stack pressure before
   ISZERO consumes t0; b is queried before its final exempt use.  The
   producer's optimistic swap actually lifts t0 above the other names,
   preventing the intended selective spill.  Unlike a local arbitrary-prefix
   probe, every incoming resource is produced by this loop. *)
Definition cycle_deep_names_def:
  cycle_deep_names = ["t0";"t1";"t2";"t3";"t4";"t5";"t6";"t7";
    "t8";"t9";"t10";"t11";"t12";"t13";"t14";"t15";"t16"]
End

Definition cycle_deep_fn_def:
  cycle_deep_fn = mk_raw_function "cycle_deep"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [mk_inst 1 JNZ [Lit 1w; Label "body"; Label "exit"] []] |>;
     <| bb_label := "body"; bb_instructions :=
        MAPi (\i v. mk_inst (100+i) ASSIGN [Lit 1w] [v]) cycle_deep_names ++
        [mk_inst 2 ADD [Lit 2w; Lit 3w] ["b"];
         mk_inst 10 ASSIGN [Lit 0w] ["padding"];
         mk_inst 3 ISZERO [Var "t0"] ["deep_out"];
         mk_inst 4 ISZERO [Var "b"] ["out"];
         mk_inst 5 ASSIGN [Var "out"] ["unused_out"];
         mk_inst 6 ASSIGN [Var "deep_out"] ["unused_deep"];
         mk_inst 7 ASSIGN [Var "b"] ["unused_b"];
         mk_inst 11 ASSIGN [Var "padding"] ["unused_padding"]] ++
        MAPi (\i v. mk_inst (200+i) ASSIGN [Var v] [STRCAT "u" v]) (TL cycle_deep_names) ++
        [mk_inst 8 JMP [Label "H"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 9 STOP [] []] |>]
End

Theorem cycle_deep_ready:
  codegen_ready_fn cycle_deep_fn /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) cycle_deep_fn.fn_blocks
Proof
  EVAL_TAC >> simp[]
QED

val _ = computeLib.add_funs [listTheory.SET_TO_LIST_SING,
  finite_mapTheory.DRESTRICT_FUPDATE,
  finite_mapTheory.DRESTRICT_FEMPTY, pred_setTheory.IN_COMPL,
  pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY];

Theorem cycle_deep_plan_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze cycle_deep_fn) (dfg_build_function cycle_deep_fn)
    (cfg_analyze cycle_deep_fn) NONE [] cycle_deep_fn 0 0)
Proof
  EVAL_TAC
QED

Definition cycle_deep_step_def:
  cycle_deep_step n ps = SND (THE (generate_block_plan
    (liveness_analyze cycle_deep_fn) (dfg_build_function cycle_deep_fn)
    (cfg_analyze cycle_deep_fn) cycle_deep_fn
    (EL n cycle_deep_fn.fn_blocks) ps))
End

Theorem cycle_deep_entry_header:
  cycle_deep_step 0 entry_probe_start = entry_probe_start /\
  cycle_deep_step 1 entry_probe_start = entry_probe_start
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem cycle_deep_no_stale_backedge:
  (cycle_deep_step 2 entry_probe_start).ps_stack = [] /\
  (cycle_deep_step 2 entry_probe_start).ps_spilled = FEMPTY
Proof
  rpt conj_tac >> EVAL_TAC
QED

(* Exact body prefix observer: next-live and next opcode are always read
   from the original full block, never from a truncated instruction list. *)
Definition cycle_deep_prefix_def:
  cycle_deep_prefix 0 = SND (clean_stack_plan
    (liveness_analyze cycle_deep_fn) (cfg_analyze cycle_deep_fn)
    cycle_deep_fn (EL 2 cycle_deep_fn.fn_blocks) entry_probe_start) /\
  cycle_deep_prefix (SUC n) = SND (THE (generate_inst_plan
    (liveness_analyze cycle_deep_fn) (dfg_build_function cycle_deep_fn)
    (cfg_analyze cycle_deep_fn) cycle_deep_fn
    (EL n (EL 2 cycle_deep_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze cycle_deep_fn) "body" (SUC n)) F
    (is_terminator (EL (SUC n) (EL 2 cycle_deep_fn.fn_blocks).bb_instructions).inst_opcode)
    "body" (cycle_deep_prefix n)))
End

Theorem cycle_deep_prefix_eight:
  cycle_deep_prefix 8 = entry_probe_start with ps_stack := MAP Var (TAKE 8 cycle_deep_names)
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [cycle_deep_prefix_eight];
Theorem cycle_deep_prefix_assigns:
  cycle_deep_prefix 17 = entry_probe_start with ps_stack := MAP Var cycle_deep_names
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [cycle_deep_prefix_assigns];

Theorem cycle_deep_prefix_before_deep:
  (cycle_deep_prefix 18).ps_stack =
    [Var "b"] ++ MAP Var (TL cycle_deep_names) ++ [Var "t0"]
Proof
  EVAL_TAC
QED

Theorem cycle_deep_prefix_after_deep:
  ~ (Var "b" IN FDOM (cycle_deep_prefix 20).ps_spilled) /\
  MEM (Var "b") (cycle_deep_prefix 20).ps_stack
Proof
  EVAL_TAC
QED

(* The first-visit entry/header states are exactly the initial DFS state.
   Splicing the checked backedge resources into those DFS fields erases
   all allocator history: the next header and body inputs are identical
   to their first-visit inputs, so this bounded family cannot witness the
   stale-prefix obstruction.  No arbitrary resources are added. *)
Theorem cycle_deep_backedge_splice:
  (entry_probe_start with <|
    ps_stack := (cycle_deep_step 2 entry_probe_start).ps_stack;
    ps_spilled := (cycle_deep_step 2 entry_probe_start).ps_spilled |>) =
  entry_probe_start
Proof
  simp[cycle_deep_no_stale_backedge] >> EVAL_TAC
QED

Theorem cycle_deep_cleanup_ledger:
  clean_stack_plan (liveness_analyze cycle_deep_fn) (cfg_analyze cycle_deep_fn)
    cycle_deep_fn (EL 1 cycle_deep_fn.fn_blocks) entry_probe_start =
    ([],entry_probe_start) /\
  clean_stack_plan (liveness_analyze cycle_deep_fn) (cfg_analyze cycle_deep_fn)
    cycle_deep_fn (EL 2 cycle_deep_fn.fn_blocks) entry_probe_start =
    ([],entry_probe_start)
Proof
  rpt conj_tac >> EVAL_TAC
QED
