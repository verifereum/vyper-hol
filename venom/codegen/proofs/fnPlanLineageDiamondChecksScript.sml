(* Concrete reachable-spill candidate. No dependency on the admitted target. *)
Theory fnPlanLineageDiamondChecks
Ancestors
  stackPlanGen venomWf callLayoutDefs passSharedDefs codegenReadyCompute
  fnPlanLineageReplay
Libs finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY]);

Definition diamond_vars_def:
  diamond_vars = ["x0"; "x1"; "x2"; "x3"; "x4"; "x5"; "x6"; "x7";
    "x8"; "x9"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"]
End

Definition diamond_fn_def:
  diamond_fn = mk_raw_function "diamond_spill"
    [<| bb_label := "E"; bb_instructions :=
        MAPi (\i v. mk_inst i PARAM [Lit (n2w i)] [v])
          (["z"] ++ diamond_vars ++ ["c"]) ++
        [mk_inst 19 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [mk_inst 20 MSTORE [Lit 0w; Var "z"] [];
         mk_inst 21 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 22 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        MAPi (\i v. mk_inst (23+i) MSTORE [Lit 0w; Var v] []) diamond_vars ++
        [mk_inst 40 STOP [] []] |>]
End

Theorem diamond_static_ready:
  codegen_ready_fn diamond_fn
Proof
  EVAL_TAC
QED

Theorem diamond_no_marker:
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) diamond_fn.fn_blocks
Proof
  EVAL_TAC
QED

Definition diamond_live_def:
  diamond_live = liveness_analyze diamond_fn
End
Definition diamond_dfg_def:
  diamond_dfg = dfg_build_function diamond_fn
End
Definition diamond_cfg_def:
  diamond_cfg = cfg_analyze diamond_fn
End

Theorem diamond_operand_order:
  compute_operands (mk_inst 20 MSTORE [Lit 0w; Var "z"] []) =
    [Var "z"; Lit 0w]
Proof
  EVAL_TAC
QED

Theorem diamond_live_J:
  live_vars_at diamond_live "J" 0 = REVERSE diamond_vars
Proof
  EVAL_TAC
QED

Theorem diamond_cfg_edges:
  cfg_succs_of diamond_cfg "E" = ["B"; "A"] /\
  cfg_succs_of diamond_cfg "A" = ["J"] /\
  cfg_succs_of diamond_cfg "B" = ["J"] /\
  cfg_succs_of diamond_cfg "J" = [] /\
  cfg_preds_of diamond_cfg "J" = ["A"; "B"]
Proof
  EVAL_TAC
QED

Theorem diamond_live_edges:
  live_vars_at diamond_live "A" 0 = REVERSE diamond_vars ++ ["z"] /\
  live_vars_at diamond_live "B" 0 = REVERSE diamond_vars /\
  live_vars_at diamond_live "A" 1 = REVERSE diamond_vars /\
  live_vars_at diamond_live "E" 20 = REVERSE diamond_vars ++ ["z"]
Proof
  EVAL_TAC
QED

Definition diamond_initial_def:
  diamond_initial = init_cleanup_plan_state NONE [] 0 0
End

Definition diamond_entry_result_def:
  diamond_entry_result = THE (generate_block_plan diamond_live diamond_dfg diamond_cfg
    diamond_fn (EL 0 diamond_fn.fn_blocks) diamond_initial)
End

Theorem diamond_entry_success:
  generate_block_plan diamond_live diamond_dfg diamond_cfg diamond_fn
    (EL 0 diamond_fn.fn_blocks) diamond_initial = SOME diamond_entry_result
Proof
  EVAL_TAC
QED

Theorem diamond_entry_stack:
  (SND diamond_entry_result).ps_stack = MAP Var (["z"] ++ diamond_vars)
Proof
  EVAL_TAC
QED

Theorem diamond_entry_value[compute]:
  diamond_entry_result =
    ([SOLabel "E"; SOPushLabel "A"; SOEmit "JUMPI"; SOPushLabel "B"; SOEmit "JUMP"],
     diamond_initial with ps_stack := MAP Var (["z"] ++ diamond_vars))
Proof
  EVAL_TAC
QED

Definition diamond_B_result_def:
  diamond_B_result = THE (generate_block_plan diamond_live diamond_dfg diamond_cfg
    diamond_fn (EL 2 diamond_fn.fn_blocks) (SND diamond_entry_result))
End

Theorem diamond_B_success:
  generate_block_plan diamond_live diamond_dfg diamond_cfg diamond_fn
    (EL 2 diamond_fn.fn_blocks) (SND diamond_entry_result) = SOME diamond_B_result
Proof
  EVAL_TAC
QED

Theorem diamond_B_stack:
  (SND diamond_B_result).ps_stack = MAP Var (REVERSE diamond_vars) /\
  (SND diamond_B_result).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

Theorem diamond_B_after_value[compute]:
  SND diamond_B_result = diamond_initial with <|
    ps_stack := MAP Var (REVERSE diamond_vars);
    ps_alloc := <|sa_free_slots := GENLIST (\i. 32*i) 18;
      sa_next_offset := 576; sa_spill_base := 0|> |>
Proof
  EVAL_TAC
QED

Definition diamond_J_result_def:
  diamond_J_result = THE (generate_block_plan diamond_live diamond_dfg diamond_cfg
    diamond_fn (EL 3 diamond_fn.fn_blocks) (SND diamond_B_result))
End

Theorem diamond_J_success:
  generate_block_plan diamond_live diamond_dfg diamond_cfg diamond_fn
    (EL 3 diamond_fn.fn_blocks) (SND diamond_B_result) = SOME diamond_J_result
Proof
  CONV_TAC (LAND_CONV EVAL) >> EVAL_TAC
QED

Theorem diamond_J_after_value[compute]:
  SND diamond_J_result = SND diamond_B_result with ps_stack := []
Proof
  CONV_TAC (LAND_CONV EVAL) >> EVAL_TAC
QED

Definition diamond_A_input_def:
  diamond_A_input = (SND diamond_entry_result) with <|
    ps_alloc := (SND diamond_J_result).ps_alloc with
      sa_free_slots := (SND diamond_entry_result).ps_alloc.sa_free_slots;
    ps_label_counter := (SND diamond_J_result).ps_label_counter |>
End

Definition diamond_A_result_def:
  diamond_A_result = THE (generate_block_plan diamond_live diamond_dfg diamond_cfg
    diamond_fn (EL 1 diamond_fn.fn_blocks) diamond_A_input)
End

Theorem diamond_A_input_value[compute]:
  diamond_A_input = diamond_initial with <|
    ps_stack := MAP Var (["z"] ++ diamond_vars);
    ps_alloc := <|sa_free_slots := []; sa_next_offset := 576; sa_spill_base := 0|> |>
Proof
  simp[diamond_A_input_def, diamond_J_after_value, diamond_B_after_value,
       diamond_entry_value, diamond_initial_def, init_cleanup_plan_state_def,
       stackPlanTypesTheory.init_plan_state_def, stackPlanTypesTheory.init_spill_alloc_def]
QED


Theorem diamond_A_clean:
  clean_stack_plan diamond_live diamond_cfg diamond_fn
    (EL 1 diamond_fn.fn_blocks) diamond_A_input = ([], diamond_A_input)
Proof
  EVAL_TAC
QED

Definition diamond_A_first_state_def:
  diamond_A_first_state = diamond_initial with <|
    ps_stack := MAP Var (["x16"] ++ TAKE 14 diamond_vars);
    ps_spilled := FEMPTY |+ (Var "x15",576) |+ (Var "x14",608);
    ps_alloc := <|sa_free_slots := []; sa_next_offset := 640; sa_spill_base := 0|> |>
End

Definition diamond_A_first_ops_def:
  diamond_A_first_ops =
    [SOPush (Lit 0w); SOSwap 2; SOSpill 576; SOSwap 2; SOSpill 608;
     SOSwap 16; SOSwap 1; SOSwap 16; SOEmit "MSTORE"]
End

Theorem diamond_A_first_value[compute]:
  generate_inst_plan diamond_live diamond_dfg diamond_cfg diamond_fn
    (mk_inst 20 MSTORE [Lit 0w; Var "z"] [])
    (REVERSE diamond_vars) F T "A" diamond_A_input =
      SOME (diamond_A_first_ops,diamond_A_first_state)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``release_dead_spills``]) >>
  simp[] >> irule release_dead_spills_live_domain >>
  simp[finite_mapTheory.FDOM_FUPDATE, finite_mapTheory.FDOM_FEMPTY] >>
  rpt strip_tac >> gvs[]
QED

Definition diamond_A_after_def:
  diamond_A_after = diamond_initial with <|
    ps_stack := MAP Var (["x15"; "x0"] ++ REVERSE (TAKE 14 (DROP 1 diamond_vars)) ++ ["x16"]);
    ps_alloc := <|sa_free_slots := [576;608]; sa_next_offset := 640; sa_spill_base := 0|> |>
End

Definition diamond_A_jump_ops_def:
  diamond_A_jump_ops =
    [SOSwap 14; SOSwap 16; SORestore 576; SOSwap 15; SORestore 608; SOSwap 14;
     SOSwap 2; SOSwap 13; SOSwap 3; SOSwap 12; SOSwap 4; SOSwap 11; SOSwap 5;
     SOSwap 10; SOSwap 6; SOSwap 9; SOSwap 7; SOSwap 8; SOSwap 7; SOSwap 6;
     SOSwap 5; SOSwap 4; SOSwap 3; SOSwap 2; SOSwap 1; SOPushLabel "J"; SOEmit "JUMP"]
End

Theorem diamond_A_jump_value[compute]:
  generate_inst_plan diamond_live diamond_dfg diamond_cfg diamond_fn
    (mk_inst 21 JMP [Label "J"] [])
    (live_vars_at diamond_live "A" 2) F F "A" diamond_A_first_state =
      SOME (diamond_A_jump_ops,diamond_A_after)
Proof
  EVAL_TAC
QED

Theorem diamond_A_structure:
  EL 1 diamond_fn.fn_blocks <> HD diamond_fn.fn_blocks /\
  (EL 1 diamond_fn.fn_blocks).bb_label = "A" /\
  non_param_insts (EL 1 diamond_fn.fn_blocks) =
    [mk_inst 20 MSTORE [Lit 0w; Var "z"] []; mk_inst 21 JMP [Label "J"] []] /\
  ~bb_is_halting (EL 1 diamond_fn.fn_blocks) /\
  get_params (EL 1 diamond_fn.fn_blocks).bb_instructions = [] /\
  LENGTH (EL 1 diamond_fn.fn_blocks).bb_instructions = 2 /\
  LENGTH (cfg_preds_of diamond_cfg "A") = 1 /\
  live_vars_at diamond_live "A" 1 = REVERSE diamond_vars /\
  is_terminator (mk_inst 21 JMP [Label "J"] []).inst_opcode
Proof
  EVAL_TAC
QED

Theorem diamond_A_success:
  generate_block_plan diamond_live diamond_dfg diamond_cfg diamond_fn
    (EL 1 diamond_fn.fn_blocks) diamond_A_input =
    SOME ([SOLabel "A"] ++ diamond_A_first_ops ++ diamond_A_jump_ops, diamond_A_after)
Proof
  simp[generate_block_plan_def, diamond_A_structure, diamond_A_clean,
       generate_block_insts_plan_def, diamond_A_first_value, diamond_A_jump_value]
QED

Theorem diamond_lookup:
  lookup_block "E" diamond_fn.fn_blocks = SOME (EL 0 diamond_fn.fn_blocks) /\
  lookup_block "A" diamond_fn.fn_blocks = SOME (EL 1 diamond_fn.fn_blocks) /\
  lookup_block "B" diamond_fn.fn_blocks = SOME (EL 2 diamond_fn.fn_blocks) /\
  lookup_block "J" diamond_fn.fn_blocks = SOME (EL 3 diamond_fn.fn_blocks) /\
  canonical_param_prefix diamond_fn /\ fn_entry_label diamond_fn = SOME "E"
Proof
  EVAL_TAC
QED

Theorem diamond_dfs_J:
  generate_fn_plan_aux diamond_live diamond_dfg diamond_cfg diamond_fn
    ["J"] ["B";"E"] (SND diamond_B_result) =
    SOME (FST diamond_J_result,["J";"B";"E"],SND diamond_J_result)
Proof
  simp[generate_fn_plan_aux_def, diamond_lookup, diamond_J_success, diamond_cfg_edges] >>
  Cases_on `diamond_J_result` >> simp[]
QED

Theorem diamond_dfs_A:
  generate_fn_plan_aux diamond_live diamond_dfg diamond_cfg diamond_fn
    ["A"] ["J";"B";"E"] diamond_A_input =
    SOME ([SOLabel "A"] ++ diamond_A_first_ops ++ diamond_A_jump_ops,
          ["A";"J";"B";"E"],diamond_A_after)
Proof
  simp[generate_fn_plan_aux_def, diamond_lookup, diamond_A_success, diamond_cfg_edges]
QED

Theorem diamond_dfs_B:
  generate_fn_plan_aux diamond_live diamond_dfg diamond_cfg diamond_fn
    ["B"] ["E"] (SND diamond_entry_result) =
    SOME (FST diamond_B_result ++ FST diamond_J_result,
          ["J";"B";"E"],SND diamond_B_result)
Proof
  simp[Once generate_fn_plan_aux_def, diamond_lookup, diamond_B_success,
       diamond_cfg_edges] >>
  simp[pairTheory.pair_CASE_def, pairTheory.UNCURRY] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[diamond_dfs_J, diamond_J_after_value] >>
  simp[diamond_B_after_value, diamond_initial_def, init_cleanup_plan_state_def,
       stackPlanTypesTheory.init_plan_state_def] >>
  simp[generate_fn_plan_aux_def]
QED

Definition diamond_final_def:
  diamond_final = diamond_initial with <|
    ps_stack := MAP Var (["z"] ++ diamond_vars);
    ps_alloc := <|sa_free_slots := []; sa_next_offset := 640; sa_spill_base := 0|> |>
End

Theorem diamond_sibling_states:
  (SND diamond_entry_result) with <|
    ps_alloc := (SND diamond_B_result).ps_alloc with
      sa_free_slots := (SND diamond_entry_result).ps_alloc.sa_free_slots;
    ps_label_counter := (SND diamond_B_result).ps_label_counter |> = diamond_A_input /\
  diamond_A_input with <|ps_alloc := diamond_A_after.ps_alloc with
      sa_free_slots := diamond_A_input.ps_alloc.sa_free_slots;
    ps_label_counter := diamond_A_after.ps_label_counter |> = diamond_final /\
  diamond_A_input with <|
    ps_stack := (SND diamond_entry_result).ps_stack;
    ps_spilled := (SND diamond_entry_result).ps_spilled |> = diamond_A_input
Proof
  simp[diamond_entry_value, diamond_B_after_value, diamond_A_input_value,
       diamond_A_after_def, diamond_final_def, diamond_initial_def,
       init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def,
       stackPlanTypesTheory.init_spill_alloc_def]
QED

Theorem diamond_succs_E:
  generate_succs_plan diamond_live diamond_dfg diamond_cfg diamond_fn
    (SND diamond_entry_result).ps_stack (SND diamond_entry_result).ps_spilled
    ["B";"A"] ["E"] (SND diamond_entry_result) =
    SOME (FST diamond_B_result ++ FST diamond_J_result ++
          [SOLabel "A"] ++ diamond_A_first_ops ++ diamond_A_jump_ops,
          ["A";"J";"B";"E"],diamond_final)
Proof
  simp[Once generate_fn_plan_aux_def] >>
  simp[diamond_dfs_B, diamond_sibling_states] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[diamond_dfs_A, diamond_sibling_states] >>
  simp[generate_fn_plan_aux_def]
QED

Definition diamond_fn_ops_def:
  diamond_fn_ops = FST diamond_entry_result ++ FST diamond_B_result ++
    FST diamond_J_result ++ [SOLabel "A"] ++ diamond_A_first_ops ++ diamond_A_jump_ops
End

Theorem diamond_dfs_E:
  generate_fn_plan_aux diamond_live diamond_dfg diamond_cfg diamond_fn
    ["E"] [] diamond_initial =
    SOME (diamond_fn_ops,["A";"J";"B";"E"],diamond_final)
Proof
  simp[Once generate_fn_plan_aux_def, diamond_lookup,
       SRULE [] diamond_entry_success, diamond_cfg_edges] >>
  simp[pairTheory.pair_CASE_def, pairTheory.UNCURRY, diamond_succs_E] >>
  simp[generate_fn_plan_aux_def, diamond_fn_ops_def]
QED

Theorem diamond_whole_success:
  generate_fn_plan_with_cleanup_analyzed diamond_live diamond_dfg diamond_cfg
    NONE [] diamond_fn 0 0 = SOME (diamond_fn_ops,diamond_final)
Proof
  simp[generate_fn_plan_with_cleanup_analyzed_def, diamond_lookup,
       GSYM diamond_initial_def, diamond_dfs_E]
QED

Theorem diamond_A_result_value:
  diamond_A_result =
    ([SOLabel "A"] ++ diamond_A_first_ops ++ diamond_A_jump_ops, diamond_A_after)
Proof
  simp[diamond_A_result_def, diamond_A_success]
QED
