Theory fnPlanLineageCycleResources
Ancestors
  fnPlanLineageCycleProbe fnPlanLineageReturnCut codegenReadyCompute
Libs wordsLib

(* A PHI consumes the previous iteration's b before b is redefined. *)
Definition resource_cycle_fn_def:
  resource_cycle_fn = mk_raw_function "resource_cycle"
    [<| bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["a"];
         mk_inst 1 JMP [Label "H"] []] |>;
     <| bb_label := "H"; bb_instructions :=
        [mk_inst 2 PHI [Label "entry"; Var "a"; Label "H"; Var "b"] ["x"];
         mk_inst 3 ADD [Var "x"; Lit 1w] ["b"];
         mk_inst 4 JMP [Label "H"] []] |>]
End

Theorem resource_cycle_ready:
  codegen_ready_fn resource_cycle_fn /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) resource_cycle_fn.fn_blocks
Proof
  EVAL_TAC >> simp[]
QED

val _ = computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY,
  listTheory.SET_TO_LIST_SING, finite_mapTheory.DRESTRICT_FUPDATE,
  finite_mapTheory.DRESTRICT_FEMPTY, pred_setTheory.IN_COMPL,
  pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY];

Theorem resource_cycle_plan_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze resource_cycle_fn) (dfg_build_function resource_cycle_fn)
    (cfg_analyze resource_cycle_fn) NONE [] resource_cycle_fn 0 0)
Proof
  EVAL_TAC >> simp[]
QED

Definition resource_cycle_block_def:
  resource_cycle_block n ps = generate_block_plan
    (liveness_analyze resource_cycle_fn) (dfg_build_function resource_cycle_fn)
    (cfg_analyze resource_cycle_fn) resource_cycle_fn
    (EL n resource_cycle_fn.fn_blocks) ps
End

Definition resource_cycle_dfs_header_def:
  resource_cycle_dfs_header = SND (THE (resource_cycle_block 0 entry_probe_start))
End

Definition resource_cycle_input_def:
  resource_cycle_input 0 = resource_cycle_dfs_header /\
  resource_cycle_input (SUC n) = resource_cycle_dfs_header with <|
    ps_stack := (SND (THE (resource_cycle_block 1 (resource_cycle_input n)))).ps_stack;
    ps_spilled := (SND (THE (resource_cycle_block 1 (resource_cycle_input n)))).ps_spilled |>
End

Theorem resource_cycle_dfs_header:
  resource_cycle_dfs_header = entry_probe_start with ps_stack := [Var "a"]
Proof
  EVAL_TAC
QED

Theorem resource_cycle_traversals:
  resource_cycle_input 1 = entry_probe_start with ps_stack := [Var "b"] /\
  resource_cycle_input 2 = resource_cycle_input 1 /\
  FST (THE (resource_cycle_block 1 (resource_cycle_input 0))) =
    FST (THE (resource_cycle_block 1 (resource_cycle_input 1))) /\
  IS_SOME (resource_cycle_block 1 (resource_cycle_input 0)) /\
  IS_SOME (resource_cycle_block 1 (resource_cycle_input 1))
Proof
  rpt conj_tac >> EVAL_TAC
QED

(* Exact instruction observations use next-live and next-terminator from
   the original block.  They are not plans of truncated blocks. *)
Definition resource_cycle_prefix_def:
  resource_cycle_prefix visit 0 = SND (clean_stack_plan
    (liveness_analyze resource_cycle_fn) (cfg_analyze resource_cycle_fn)
    resource_cycle_fn (EL 1 resource_cycle_fn.fn_blocks) (resource_cycle_input visit)) /\
  resource_cycle_prefix visit (SUC n) = SND (THE (generate_inst_plan
    (liveness_analyze resource_cycle_fn) (dfg_build_function resource_cycle_fn)
    (cfg_analyze resource_cycle_fn) resource_cycle_fn
    (EL n (EL 1 resource_cycle_fn.fn_blocks).bb_instructions)
    (live_vars_at (liveness_analyze resource_cycle_fn) "H" (SUC n)) F
    (is_terminator (EL (SUC n) (EL 1 resource_cycle_fn.fn_blocks).bb_instructions).inst_opcode)
    "H" (resource_cycle_prefix visit n)))
End

Theorem resource_cycle_ledger:
  MAP (live_vars_at (liveness_analyze resource_cycle_fn) "H") [0;1;2;3] =
    [["a";"b"];["x"];["b"];["b"]] /\
  MAP (\n. (resource_cycle_prefix 0 n).ps_stack) [0;1;2;3] =
    [[Var "a"];[Var "x"];[Var "b"];[Var "b"]] /\
  MAP (\n. (resource_cycle_prefix 1 n).ps_stack) [0;1;2;3] =
    [[Var "b"];[Var "x"];[Var "b"];[Var "b"]]
Proof
  rpt conj_tac >> EVAL_TAC
QED

val _ = computeLib.add_funs [resource_cycle_dfs_header,
  CONJUNCT1 resource_cycle_traversals];

Theorem resource_cycle_prefix_one:
  resource_cycle_prefix 1 1 = entry_probe_start with ps_stack := [Var "x"]
Proof
  EVAL_TAC
QED

Theorem resource_cycle_prefix_two:
  resource_cycle_prefix 1 2 = entry_probe_start with ps_stack := [Var "b"]
Proof
  EVAL_TAC
QED

val _ = computeLib.add_funs [resource_cycle_prefix_one, resource_cycle_prefix_two];

(* Join cleanup is identity, not an erasure mechanism.  The PHI itself
   renames the carried slot; the subsequent ADD consumes x and produces b.
   Raw union live-in coverage fails at the PHI boundary (one alternative is
   absent), while ordinary-position coverage and unit multiplicity hold. *)
Theorem resource_cycle_observations:
  clean_stack_plan (liveness_analyze resource_cycle_fn) (cfg_analyze resource_cycle_fn)
    resource_cycle_fn (EL 1 resource_cycle_fn.fn_blocks) (resource_cycle_input 1) =
    ([],resource_cycle_input 1) /\
  ~EVERY (\v. MEM (Var v) (resource_cycle_input 1).ps_stack \/
       Var v IN FDOM (resource_cycle_input 1).ps_spilled)
    (live_vars_at (liveness_analyze resource_cycle_fn) "H" 0) /\
  EVERY (\i. EVERY (\v.
      MEM (Var v) (resource_cycle_prefix 1 i).ps_stack /\
      LIST_ELEM_COUNT (Var v) (resource_cycle_prefix 1 i).ps_stack = 1)
    (live_vars_at (liveness_analyze resource_cycle_fn) "H" i)) [1;2;3] /\
  EVERY (\i. (resource_cycle_prefix 1 i).ps_spilled = FEMPTY) [0;1;2;3] /\
  EVERY (\i. TAKE (LENGTH (resource_cycle_prefix 1 i).ps_stack - 1)
       (resource_cycle_prefix 1 i).ps_stack = []) [0;1;2;3] /\
  ~MEM (Var "b") (resource_cycle_prefix 1 1).ps_stack
Proof
  rpt conj_tac >> EVAL_TAC
QED

(* The one bounded variation tries to retain a dead definition by copying
   the carried b immediately before the backedge.  Native post-processing
   removes the dead output; it does not retain an older b in a prefix. *)
Definition resource_dead_cycle_fn_def:
  resource_dead_cycle_fn = resource_cycle_fn with fn_blocks :=
    [HD resource_cycle_fn.fn_blocks;
     <|bb_label := "H"; bb_instructions :=
       TAKE 2 (EL 1 resource_cycle_fn.fn_blocks).bb_instructions ++
       [mk_inst 5 ASSIGN [Var "b"] ["dead"];
        mk_inst 4 JMP [Label "H"] []]|>]
End

Theorem resource_dead_cycle_ready_success:
  codegen_ready_fn resource_dead_cycle_fn /\
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze resource_dead_cycle_fn) (dfg_build_function resource_dead_cycle_fn)
    (cfg_analyze resource_dead_cycle_fn) NONE [] resource_dead_cycle_fn 0 0)
Proof
  conj_tac >- (EVAL_TAC >> simp[]) >> EVAL_TAC
QED

Definition resource_dead_cycle_block_def:
  resource_dead_cycle_block ps = generate_block_plan
    (liveness_analyze resource_dead_cycle_fn) (dfg_build_function resource_dead_cycle_fn)
    (cfg_analyze resource_dead_cycle_fn) resource_dead_cycle_fn
    (EL 1 resource_dead_cycle_fn.fn_blocks) ps
End

Theorem resource_dead_cycle_two_visits:
  IS_SOME (resource_dead_cycle_block (entry_probe_start with ps_stack := [Var "a"])) /\
  IS_SOME (resource_dead_cycle_block (entry_probe_start with ps_stack := [Var "b"])) /\
  FST (THE (resource_dead_cycle_block (entry_probe_start with ps_stack := [Var "a"]))) =
    FST (THE (resource_dead_cycle_block (entry_probe_start with ps_stack := [Var "b"]))) /\
  SND (THE (resource_dead_cycle_block (entry_probe_start with ps_stack := [Var "a"]))) =
    (entry_probe_start with ps_stack := [Var "b"]) /\
  SND (THE (resource_dead_cycle_block (entry_probe_start with ps_stack := [Var "b"]))) =
    (entry_probe_start with ps_stack := [Var "b"])
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem resource_dead_cycle_erasure:
  generate_inst_plan
    (liveness_analyze resource_dead_cycle_fn) (dfg_build_function resource_dead_cycle_fn)
    (cfg_analyze resource_dead_cycle_fn) resource_dead_cycle_fn
    (mk_inst 5 ASSIGN [Var "b"] ["dead"]) ["b"] F T "H"
    (entry_probe_start with ps_stack := [Var "b"]) =
    SOME ([SODup 1; SOPop 1],entry_probe_start with ps_stack := [Var "b"])
Proof
  EVAL_TAC
QED

(* The entry fixture uses the actual initial state.  Its sole successor is
   H, so the native DFS enters H with exactly the entry block's result. *)
Theorem resource_cycle_entry_source:
  entry_probe_start = init_cleanup_plan_state NONE [] 0 0 /\
  cfg_succs_of (cfg_analyze resource_cycle_fn) "entry" = ["H"] /\
  resource_cycle_block 0 entry_probe_start =
    SOME (FST (THE (resource_cycle_block 0 entry_probe_start)),
          resource_cycle_dfs_header)
Proof
  rpt conj_tac >> EVAL_TAC
QED
