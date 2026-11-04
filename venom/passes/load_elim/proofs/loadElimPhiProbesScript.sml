Theory loadElimPhiProbes
Ancestors
  loadElimDefs loadElimJoinProps venomExecSemantics venomState venomWf venomInst finite_map
  codegenReadyCompute

Definition probe_inst_def:
  probe_inst id op ops outs =
    <| inst_id := id; inst_opcode := op; inst_operands := ops;
       inst_outputs := outs |>
End

Definition singleton_probe_fn_def:
  singleton_probe_fn = mk_raw_function "f"
    [<| bb_label := "e";
        bb_instructions :=
          [probe_inst 0 SLOAD [Lit 0w] ["x"];
           probe_inst 1 SLOAD [Lit 0w] ["y"];
           probe_inst 2 STOP [] []] |>]
End

Theorem singleton_probe_wf:
  wf_function singleton_probe_fn /\ fn_inst_wf singleton_probe_fn /\
  wf_ssa singleton_probe_fn
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  simp[wf_ssa_def, ssa_form_def, def_dominates_uses_def,
       singleton_probe_fn_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, probe_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem singleton_transfer_probe:
  !ctx. ctx.lctx_config = storage_config ==>
    load_transfer ctx (probe_inst 0 SLOAD [Lit 0w] ["x"]) NONE =
    SOME (FEMPTY |+
      (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
        (normalize_operand ctx.lctx_dfg [])
        (probe_inst 0 SLOAD [Lit 0w] ["x"]), [Var "x"]))
Proof
  simp[load_transfer_def, storage_config_def, probe_inst_def,
       unwrap_load_lattice_def]
QED

Definition singleton_probe_ctx_def:
  singleton_probe_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function singleton_probe_fn) storage_config
End

Theorem singleton_analysis_probe:
  load_elim_inst singleton_probe_ctx []
    (df_at NONE (load_analyze singleton_probe_ctx singleton_probe_fn) "e" 1)
    (probe_inst 1 SLOAD [Lit 0w] ["y"]) =
  mk_assign_inst (probe_inst 1 SLOAD [Lit 0w] ["y"]) (Var "x")
Proof
  EVAL_TAC >> simp[FUN_FMAP_EMPTY] >> EVAL_TAC
QED

Definition diamond_probe_fn_def:
  diamond_probe_fn = mk_raw_function "diamond"
    [<| bb_label := "e"; bb_instructions :=
         [probe_inst 0 JNZ [Lit 1w; Label "l"; Label "r"] []] |>;
     <| bb_label := "l"; bb_instructions :=
         [probe_inst 1 SLOAD [Lit 0w] ["x"];
          probe_inst 2 JMP [Label "j"] []] |>;
     <| bb_label := "r"; bb_instructions :=
         [probe_inst 3 SLOAD [Lit 0w] ["y"];
          probe_inst 4 JMP [Label "j"] []] |>;
     <| bb_label := "j"; bb_instructions :=
         [probe_inst 5 JMP [Label "s"] []] |>;
     <| bb_label := "s"; bb_instructions :=
         [probe_inst 6 SLOAD [Lit 0w] ["z"];
          probe_inst 7 STOP [] []] |>]
End

Definition diamond_probe_ctx_def:
  diamond_probe_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function diamond_probe_fn) storage_config
End

Theorem diamond_probe_wf:
  wf_function diamond_probe_fn /\ fn_inst_wf diamond_probe_fn /\
  wf_ssa diamond_probe_fn
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  simp[wf_ssa_def, ssa_form_def, def_dominates_uses_def,
       diamond_probe_fn_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, probe_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem diamond_cfg_probe:
  cfg_analyze diamond_probe_fn =
    <| cfg_succs := FEMPTY |++ [("e",["r";"l"]); ("l",["j"]);
         ("r",["j"]); ("j",["s"]); ("s",[])];
       cfg_preds := FEMPTY |++ [("e",[]); ("l",["e"]); ("r",["e"]);
         ("j",["l";"r"]); ("s",["j"])];
       cfg_reachable := FEMPTY |++ [("e",T);("l",T);("r",T);("j",T);("s",T)];
       cfg_dfs_post := ["s";"j";"r";"l";"e"];
       cfg_dfs_pre := ["e";"r";"j";"s";"l"] |>
Proof
  EVAL_TAC >> simp[fmap_EXT, FLOOKUP_DEF, FUN_EQ_THM] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[SF DISJ_ss, FAPPLY_FUPDATE_THM] >>
  rpt strip_tac >> gvs[FAPPLY_FUPDATE_THM] >> EVAL_TAC
QED


val _ = computeLib.add_funs
  [load_join_empty_left, load_join_empty_right, load_join_singleton_same,
   FUN_FMAP_EMPTY, load_key_to_memloc_def];

Definition diamond_process_def:
  diamond_process = df_process_block Forward NONE load_join load_transfer
    load_edge_transfer diamond_probe_ctx (SOME ("e", SOME FEMPTY))
    (cfg_analyze diamond_probe_fn) diamond_probe_fn.fn_blocks
End

Definition diamond_changed_def:
  diamond_changed lbl old new =
    (df_boundary NONE new lbl <> df_boundary NONE old lbl)
End

Definition diamond_step_def:
  diamond_step = wl_step diamond_changed diamond_process
    (cfg_succs_of (cfg_analyze diamond_probe_fn))
End

Definition diamond_initial_def:
  diamond_initial =
    (["e";"r";"j";"s";"l"],
     (init_df_state (NONE : load_lattice) ["e";"l";"r";"j";"s"]) with
       ds_boundary := FEMPTY |++ [("e",SOME FEMPTY);("l",NONE);
         ("r",NONE);("j",NONE);("s",NONE)])
End

Theorem diamond_step0_probe:
  diamond_step diamond_initial =
    (["r";"j";"s";"l"], SND diamond_initial)
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Definition diamond_after_entry_def:
  diamond_after_entry = (["r";"j";"s";"l"], SND diamond_initial)
End

Definition diamond_values_def:
  diamond_values vs = SOME (FEMPTY |+
    (LK_Loc <| ml_offset := SOME 0; ml_size := SOME 1;
       ml_alloca := NONE; ml_volatile := F |>, vs))
End

Definition diamond_after_right_def:
  diamond_after_right = (["j";"s";"l";"j"],
    (SND diamond_initial) with ds_boundary :=
      (SND diamond_initial).ds_boundary |+ ("r", diamond_values [Var "y"]))
End

Theorem diamond_step1_probe:
  diamond_step diamond_after_entry = diamond_after_right
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Definition diamond_after_join1_def:
  diamond_after_join1 = (["s";"l";"j";"s"],
    (SND diamond_after_right) with ds_boundary :=
      (SND diamond_after_right).ds_boundary |+ ("j", diamond_values [Var "y"]))
End

Theorem diamond_step2_probe:
  diamond_step diamond_after_right = diamond_after_join1
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Definition diamond_after_successor1_def:
  diamond_after_successor1 = (["l";"j";"s"],
    (SND diamond_after_join1) with ds_boundary :=
      (SND diamond_after_join1).ds_boundary |+ ("s", diamond_values [Var "z"]))
End

Theorem diamond_step3_probe:
  diamond_step diamond_after_join1 = diamond_after_successor1
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Definition diamond_after_left_def:
  diamond_after_left = (["j";"s";"j"],
    (SND diamond_after_successor1) with ds_boundary :=
      (SND diamond_after_successor1).ds_boundary |+ ("l", diamond_values [Var "x"]))
End

Theorem diamond_step4_probe:
  diamond_step diamond_after_successor1 = diamond_after_left
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Definition diamond_after_join2_def:
  diamond_after_join2 = (["s";"j";"s"],
    (SND diamond_after_left) with ds_boundary :=
      (SND diamond_after_left).ds_boundary |+
        ("j", diamond_values [Var "y"; Var "x"]))
End

Theorem diamond_step5_probe:
  diamond_step diamond_after_left = diamond_after_join2
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF]
QED

Theorem diamond_step6_probe:
  diamond_step diamond_after_join2 =
    (["j";"s"], SND diamond_after_join2)
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF]
QED

Theorem diamond_step7_probe:
  diamond_step (["j";"s"], SND diamond_after_join2) =
    (["s"], SND diamond_after_join2)
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF]
QED

Theorem diamond_step8_probe:
  diamond_step (["s"], SND diamond_after_join2) =
    ([], SND diamond_after_join2)
Proof
  rewrite_tac[diamond_step_def, diamond_process_def, diamond_cfg_probe] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF]
QED

Theorem diamond_worklists_probe:
  FST diamond_initial = ["e";"r";"j";"s";"l"] /\
  FST diamond_after_entry = ["r";"j";"s";"l"] /\
  FST diamond_after_right = ["j";"s";"l";"j"] /\
  FST diamond_after_join1 = ["s";"l";"j";"s"] /\
  FST diamond_after_successor1 = ["l";"j";"s"] /\
  FST diamond_after_left = ["j";"s";"j"] /\
  FST diamond_after_join2 = ["s";"j";"s"]
Proof
  simp[diamond_initial_def, diamond_after_entry_def, diamond_after_right_def,
    diamond_after_join1_def, diamond_after_successor1_def,
    diamond_after_left_def, diamond_after_join2_def]
QED

Theorem diamond_iteration_probe:
  WHILE (\p. FST p <> []) diamond_step diamond_initial =
    ([], SND diamond_after_join2)
Proof
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [diamond_worklists_probe, listTheory.NOT_CONS_NIL,
    diamond_step0_probe, GSYM diamond_after_entry_def] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [diamond_worklists_probe, listTheory.NOT_CONS_NIL,
    diamond_step1_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [diamond_worklists_probe, listTheory.NOT_CONS_NIL,
    diamond_step2_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [diamond_worklists_probe, listTheory.NOT_CONS_NIL,
    diamond_step3_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [diamond_worklists_probe, listTheory.NOT_CONS_NIL,
    diamond_step4_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [diamond_worklists_probe, listTheory.NOT_CONS_NIL,
    diamond_step5_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [diamond_worklists_probe, listTheory.NOT_CONS_NIL,
    diamond_step6_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [pairTheory.FST, listTheory.NOT_CONS_NIL, diamond_step7_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp [pairTheory.FST, listTheory.NOT_CONS_NIL, diamond_step8_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[]
QED

Theorem diamond_initial_state_probe:
  (init_df_state NONE (MAP (\bb. bb.bb_label) diamond_probe_fn.fn_blocks)
    with ds_boundary :=
      (init_df_state NONE (MAP (\bb. bb.bb_label) diamond_probe_fn.fn_blocks)).ds_boundary
        |+ ("e", SOME FEMPTY)) = SND diamond_initial
Proof
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM] >>
  rpt strip_tac >> gvs[FAPPLY_FUPDATE_THM] >> EVAL_TAC
QED

Theorem diamond_analysis_probe:
  load_analyze diamond_probe_ctx diamond_probe_fn =
    df_populate_inst Forward NONE load_join load_transfer load_edge_transfer
      diamond_probe_ctx (SOME ("e", SOME FEMPTY))
      (cfg_analyze diamond_probe_fn) diamond_probe_fn.fn_blocks
      ["e";"l";"r";"j";"s"] (SND diamond_after_join2)
Proof
  rewrite_tac[load_analyze_def, dfAnalyzeDefsTheory.df_analyze_def] >>
  `fn_entry_label diamond_probe_fn = SOME "e"` by EVAL_TAC >>
  `MAP (\bb. bb.bb_label) diamond_probe_fn.fn_blocks =
    ["e";"l";"r";"j";"s"]` by EVAL_TAC >>
  simp[LET_THM] >>
  AP_TERM_TAC >>
  `((cfg_analyze diamond_probe_fn).cfg_dfs_pre) = FST diamond_initial`
    by EVAL_TAC >>
  rewrite_tac[GSYM diamond_changed_def, GSYM diamond_process_def,
    worklistDefsTheory.wl_iterate_def, GSYM diamond_step_def] >>
  `init_df_state NONE ["e";"l";"r";"j";"s"] with
    ds_boundary := (init_df_state NONE ["e";"l";"r";"j";"s"]).ds_boundary
      |+ ("e", SOME FEMPTY) = SND diamond_initial`
    by metis_tac[diamond_initial_state_probe] >>
  simp[SF ETA_ss, GSYM diamond_step_def, pairTheory.PAIR,
       diamond_iteration_probe]
QED

Theorem diamond_left_boundary_probe:
  df_boundary NONE (load_analyze diamond_probe_ctx diamond_probe_fn) "l" =
    diamond_values [Var "x"]
Proof
  rewrite_tac[diamond_analysis_probe, diamond_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Theorem diamond_right_boundary_probe:
  df_boundary NONE (load_analyze diamond_probe_ctx diamond_probe_fn) "r" =
    diamond_values [Var "y"]
Proof
  rewrite_tac[diamond_analysis_probe, diamond_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Theorem diamond_load_input_probe:
  df_at NONE (load_analyze diamond_probe_ctx diamond_probe_fn) "s" 0 =
    diamond_values [Var "y"; Var "x"]
Proof
  rewrite_tac[diamond_analysis_probe, diamond_cfg_probe] >>
  EVAL_TAC >> simp[FUN_FMAP_DEF, fmap_EXT, FAPPLY_FUPDATE_THM]
QED

Definition diamond_phi_action_def:
  diamond_phi_action =
    <| pa_join_lbl := "j"; pa_phi_id := 14; pa_phi_out := "$le_phi_6";
       pa_phi_ops := [Label "l"; Var "x"; Label "r"; Var "y"];
       pa_load_id := 6; pa_load_lbl := "s" |>
End

Theorem diamond_actions_exact_probe:
  collect_phi_actions 7 diamond_probe_ctx (cfg_analyze diamond_probe_fn)
    (load_analyze diamond_probe_ctx diamond_probe_fn) diamond_probe_fn =
  [diamond_phi_action]
Proof
  rewrite_tac[diamond_analysis_probe, diamond_cfg_probe] >>
  EVAL_TAC >> simp[FUN_FMAP_DEF, fmap_EXT, FAPPLY_FUPDATE_THM] >> EVAL_TAC
QED

Theorem diamond_phi_left_probe:
  s.vs_prev_bb = SOME "l" /\ lookup_var "x" s = SOME w ==>
  eval_phis s (phis_for_block [diamond_phi_action] "j") =
    OK (update_var "$le_phi_6" w s)
Proof
  strip_tac >>
  simp[phis_for_block_def, diamond_phi_action_def, eval_phis_def,
    eval_one_phi_def, resolve_phi_def, eval_operand_def]
QED

Theorem diamond_phi_right_probe:
  s.vs_prev_bb = SOME "r" /\ lookup_var "y" s = SOME w ==>
  eval_phis s (phis_for_block [diamond_phi_action] "j") =
    OK (update_var "$le_phi_6" w s)
Proof
  strip_tac >>
  simp[phis_for_block_def, diamond_phi_action_def, eval_phis_def,
    eval_one_phi_def, resolve_phi_def, eval_operand_def]
QED

Theorem diamond_selected_phi_consumer_probe:
  ((s.vs_prev_bb = SOME "l" /\ lookup_var "x" s = SOME w) \/
   (s.vs_prev_bb = SOME "r" /\ lookup_var "y" s = SOME w)) ==>
  eval_phis s
    (phis_for_block
      (collect_phi_actions 7 diamond_probe_ctx (cfg_analyze diamond_probe_fn)
        (load_analyze diamond_probe_ctx diamond_probe_fn) diamond_probe_fn) "j") =
    OK (update_var "$le_phi_6" w s)
Proof
  rewrite_tac[diamond_actions_exact_probe] >> strip_tac
  >- (irule diamond_phi_left_probe >> simp[])
  >> irule diamond_phi_right_probe >> simp[]
QED

(* The backedge stores x, while the old PHI overwrites x with y.
   The generated PHI must therefore read the pre-PHI x, not the new x. *)
Definition loop_probe_fn_def:
  loop_probe_fn = mk_raw_function "loop"
    [<| bb_label := "e"; bb_instructions :=
         [probe_inst 8 JMP [Label "p"] []] |>;
     <| bb_label := "p"; bb_instructions :=
         [probe_inst 0 SLOAD [Lit 0w] ["a"];
          probe_inst 1 JMP [Label "h"] []] |>;
     <| bb_label := "h"; bb_instructions :=
         [probe_inst 2 PHI [Label "p"; Var "a"; Label "h"; Var "y"] ["x"];
          probe_inst 3 SLOAD [Lit 0w] ["z"];
          probe_inst 4 ADD [Var "x"; Lit 1w] ["y"];
          probe_inst 5 SSTORE [Lit 0w; Var "x"] [];
          probe_inst 6 JNZ [Lit 0w; Label "h"; Label "q"] []] |>;
     <| bb_label := "q"; bb_instructions := [probe_inst 7 STOP [] []] |>]
End

Definition loop_probe_ctx_def:
  loop_probe_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function loop_probe_fn) storage_config
End

Theorem loop_probe_wf:
  wf_function loop_probe_fn /\ fn_inst_wf loop_probe_fn /\ wf_ssa loop_probe_fn
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  rewrite_tac[wf_ssa_def] >> conj_tac >- EVAL_TAC >>
  rewrite_tac[def_dominates_uses_compute] >> EVAL_TAC
QED

Theorem loop_cfg_probe:
  cfg_analyze loop_probe_fn =
    <| cfg_succs := FEMPTY |++ [("e",["p"]); ("p",["h"]); ("h",["q";"h"]); ("q",[])];
       cfg_preds := FEMPTY |++ [("e",[]); ("p",["e"]); ("h",["p";"h"]); ("q",["h"])];
       cfg_reachable := FEMPTY |++ [("e",T);("p",T);("h",T);("q",T)];
       cfg_dfs_post := ["q";"h";"p";"e"];
       cfg_dfs_pre := ["e";"p";"h";"q"] |>
Proof
  EVAL_TAC >> simp[fmap_EXT, FLOOKUP_DEF, FUN_EQ_THM] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[SF DISJ_ss, FAPPLY_FUPDATE_THM] >>
  rpt strip_tac >> gvs[FAPPLY_FUPDATE_THM] >> EVAL_TAC
QED

Definition loop_process_def:
  loop_process = df_process_block Forward NONE load_join load_transfer
    load_edge_transfer loop_probe_ctx (SOME ("e", SOME FEMPTY))
    (cfg_analyze loop_probe_fn) loop_probe_fn.fn_blocks
End

Definition loop_changed_def:
  loop_changed lbl old new =
    (df_boundary NONE new lbl <> df_boundary NONE old lbl)
End

Definition loop_step_def:
  loop_step = wl_step loop_changed loop_process
    (cfg_succs_of (cfg_analyze loop_probe_fn))
End

Definition loop_initial_def:
  loop_initial =
    (["e";"p";"h";"q"],
     (init_df_state (NONE : load_lattice) ["e";"p";"h";"q"]) with
       ds_boundary := FEMPTY |++ [("e",SOME FEMPTY);("p",NONE);("h",NONE);("q",NONE)])
End

Definition loop_after_entry_def:
  loop_after_entry = (["p";"h";"q"], SND loop_initial)
End

Theorem loop_step0_probe:
  loop_step loop_initial = loop_after_entry
Proof
  rewrite_tac[loop_step_def, loop_process_def, loop_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Definition loop_after_preheader_def:
  loop_after_preheader = (["h";"q";"h"], (SND loop_initial) with
    ds_boundary := (SND loop_initial).ds_boundary |+ ("p",diamond_values [Var "a"]))
End

Theorem loop_step1_probe:
  loop_step loop_after_entry = loop_after_preheader
Proof
  rewrite_tac[loop_step_def, loop_process_def, loop_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Definition loop_after_header_def:
  loop_after_header = (["q";"h";"q";"h"], (SND loop_after_preheader) with
    ds_boundary := (SND loop_after_preheader).ds_boundary |+ ("h",diamond_values [Var "x"]))
End

Theorem loop_step2_probe:
  loop_step loop_after_preheader = loop_after_header
Proof
  rewrite_tac[loop_step_def, loop_process_def, loop_cfg_probe] >>
  EVAL_TAC >> simp[load_key_to_memloc_def] >> EVAL_TAC
QED

Definition loop_fixed_def:
  loop_fixed = (SND loop_after_header) with ds_boundary :=
    (SND loop_after_header).ds_boundary |+ ("q", diamond_values [Var "x"])
End

Theorem loop_step3_probe:
  loop_step loop_after_header = (["h";"q";"h"],loop_fixed)
Proof
  rewrite_tac[loop_step_def, loop_process_def, loop_cfg_probe] >>
  EVAL_TAC >> simp[]
QED

Theorem loop_header_stable_probe:
  loop_process "h" loop_fixed = loop_fixed
Proof
  rewrite_tac[loop_process_def, loop_cfg_probe] >> EVAL_TAC >>
  simp[load_key_to_memloc_def] >> EVAL_TAC >>
  simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF] >>
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM, FUN_FMAP_DEF]
QED

Theorem loop_exit_stable_probe:
  loop_process "q" loop_fixed = loop_fixed
Proof
  rewrite_tac[loop_process_def, loop_cfg_probe] >> EVAL_TAC >> simp[]
QED

Theorem loop_worklists_probe:
  FST loop_initial = ["e";"p";"h";"q"] /\
  FST loop_after_entry = ["p";"h";"q"] /\
  FST loop_after_preheader = ["h";"q";"h"] /\
  FST loop_after_header = ["q";"h";"q";"h"]
Proof
  simp[loop_initial_def, loop_after_entry_def, loop_after_preheader_def,
    loop_after_header_def]
QED

Theorem loop_iteration_probe:
  WHILE (\p. FST p <> []) loop_step loop_initial = ([],loop_fixed)
Proof
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[loop_worklists_probe, loop_step0_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[loop_worklists_probe, loop_step1_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[loop_worklists_probe, loop_step2_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[loop_worklists_probe, loop_step3_probe] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[loop_step_def, worklistDefsTheory.wl_step_def, loop_header_stable_probe, loop_changed_def] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[loop_step_def, worklistDefsTheory.wl_step_def, loop_exit_stable_probe, loop_changed_def] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[loop_step_def, worklistDefsTheory.wl_step_def, loop_header_stable_probe, loop_changed_def] >>
  once_rewrite_tac[WhileTheory.WHILE] >> simp[]
QED

Theorem loop_initial_state_probe:
  (init_df_state NONE (MAP (\bb. bb.bb_label) loop_probe_fn.fn_blocks)
    with ds_boundary :=
      (init_df_state NONE (MAP (\bb. bb.bb_label) loop_probe_fn.fn_blocks)).ds_boundary
        |+ ("e", SOME FEMPTY)) = SND loop_initial
Proof
  EVAL_TAC >> simp[fmap_EXT, FAPPLY_FUPDATE_THM] >>
  rpt strip_tac >> gvs[FAPPLY_FUPDATE_THM] >> EVAL_TAC
QED

Theorem loop_analysis_probe:
  load_analyze loop_probe_ctx loop_probe_fn =
    df_populate_inst Forward NONE load_join load_transfer load_edge_transfer
      loop_probe_ctx (SOME ("e", SOME FEMPTY))
      (cfg_analyze loop_probe_fn) loop_probe_fn.fn_blocks
      ["e";"p";"h";"q"] loop_fixed
Proof
  rewrite_tac[load_analyze_def, dfAnalyzeDefsTheory.df_analyze_def] >>
  `fn_entry_label loop_probe_fn = SOME "e"` by EVAL_TAC >>
  `MAP (\bb. bb.bb_label) loop_probe_fn.fn_blocks =
    ["e";"p";"h";"q"]` by EVAL_TAC >>
  simp[LET_THM] >> AP_TERM_TAC >>
  `((cfg_analyze loop_probe_fn).cfg_dfs_pre) = FST loop_initial`
    by EVAL_TAC >>
  rewrite_tac[GSYM loop_changed_def, GSYM loop_process_def,
    worklistDefsTheory.wl_iterate_def, GSYM loop_step_def] >>
  `init_df_state NONE ["e";"p";"h";"q"] with
    ds_boundary := (init_df_state NONE ["e";"p";"h";"q"]).ds_boundary
      |+ ("e", SOME FEMPTY) = SND loop_initial`
    by metis_tac[loop_initial_state_probe] >>
  simp[SF ETA_ss, GSYM loop_step_def, pairTheory.PAIR, loop_iteration_probe]
QED

Definition loop_phi_action_def:
  loop_phi_action =
    <| pa_join_lbl := "h"; pa_phi_id := 12; pa_phi_out := "$le_phi_3";
       pa_phi_ops := [Label "p"; Var "a"; Label "h"; Var "x"];
       pa_load_id := 3; pa_load_lbl := "h" |>
End

Theorem loop_actions_exact_probe:
  collect_phi_actions 8 loop_probe_ctx (cfg_analyze loop_probe_fn)
    (load_analyze loop_probe_ctx loop_probe_fn) loop_probe_fn = [loop_phi_action]
Proof
  rewrite_tac[loop_analysis_probe, loop_cfg_probe] >> EVAL_TAC >>
  simp[load_key_to_memloc_def, FUN_FMAP_DEF, fmap_EXT, FAPPLY_FUPDATE_THM] >>
  EVAL_TAC >> simp[FUN_FMAP_DEF, fmap_EXT, FAPPLY_FUPDATE_THM]
QED

Theorem loop_parallel_phi_probe:
  s.vs_prev_bb = SOME "h" /\ lookup_var "x" s = SOME old_x /\
  lookup_var "y" s = SOME new_x ==>
  eval_phis s
    (phis_for_block [loop_phi_action] "h" ++
     [probe_inst 2 PHI [Label "p"; Var "a"; Label "h"; Var "y"] ["x"]]) =
  OK (update_var "$le_phi_3" old_x (update_var "x" new_x s))
Proof
  strip_tac >>
  simp[phis_for_block_def, loop_phi_action_def, probe_inst_def,
    eval_phis_def, eval_one_phi_def, resolve_phi_def, eval_operand_def]
QED

Theorem loop_entry_phi_probe:
  s.vs_prev_bb = SOME "p" /\ lookup_var "a" s = SOME w ==>
  eval_phis s
    (phis_for_block [loop_phi_action] "h" ++
     [probe_inst 2 PHI [Label "p"; Var "a"; Label "h"; Var "y"] ["x"]]) =
  OK (update_var "$le_phi_3" w (update_var "x" w s))
Proof
  strip_tac >>
  simp[phis_for_block_def, loop_phi_action_def, probe_inst_def,
    eval_phis_def, eval_one_phi_def, resolve_phi_def, eval_operand_def]
QED

Definition entry_backedge_probe_fn_def:
  entry_backedge_probe_fn = mk_raw_function "entry_backedge"
    [<| bb_label := "e"; bb_instructions :=
         [probe_inst 0 SLOAD [Lit 0w] ["x"];
          probe_inst 1 JNZ [Lit 0w; Label "e"; Label "q"] []] |>;
     <| bb_label := "q"; bb_instructions := [probe_inst 2 STOP [] []] |>]
End

Definition entry_backedge_probe_ctx_def:
  entry_backedge_probe_ctx = mk_load_context FEMPTY FEMPTY
    (dfg_build_function entry_backedge_probe_fn) storage_config
End

Theorem entry_backedge_wf_probe:
  wf_function entry_backedge_probe_fn /\ fn_inst_wf entry_backedge_probe_fn /\
  wf_ssa entry_backedge_probe_fn
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  rewrite_tac[wf_ssa_def] >> conj_tac >- EVAL_TAC >>
  rewrite_tac[def_dominates_uses_compute] >> EVAL_TAC
QED

Theorem entry_backedge_analysis_probe:
  df_at NONE (load_analyze entry_backedge_probe_ctx entry_backedge_probe_fn) "e" 0 =
    SOME FEMPTY /\
  collect_phi_actions 2 entry_backedge_probe_ctx (cfg_analyze entry_backedge_probe_fn)
    (load_analyze entry_backedge_probe_ctx entry_backedge_probe_fn)
    entry_backedge_probe_fn = []
Proof
  EVAL_TAC >> simp[FUN_FMAP_EMPTY] >> EVAL_TAC
QED

Definition diamond_transformed_probe_fn_def:
  diamond_transformed_probe_fn = diamond_probe_fn with fn_blocks :=
    [<| bb_label := "e"; bb_instructions :=
         [probe_inst 0 JNZ [Lit 1w; Label "l"; Label "r"] []] |>;
     <| bb_label := "l"; bb_instructions :=
         [probe_inst 1 SLOAD [Lit 0w] ["x"];
          probe_inst 2 JMP [Label "j"] []] |>;
     <| bb_label := "r"; bb_instructions :=
         [probe_inst 3 SLOAD [Lit 0w] ["y"];
          probe_inst 4 JMP [Label "j"] []] |>;
     <| bb_label := "j"; bb_instructions :=
         [probe_inst 14 PHI [Label "l"; Var "x"; Label "r"; Var "y"] ["$le_phi_6"];
          probe_inst 5 JMP [Label "s"] []] |>;
     <| bb_label := "s"; bb_instructions :=
         [probe_inst 6 ASSIGN [Var "$le_phi_6"] ["z"];
          probe_inst 7 STOP [] []] |>]
End

Theorem diamond_transformed_exact_probe:
  load_elim_one diamond_probe_ctx (cfg_analyze diamond_probe_fn) diamond_probe_fn =
    diamond_transformed_probe_fn
Proof
  rewrite_tac[load_elim_one_def] >>
  `fn_max_inst_id diamond_probe_fn = 7` by EVAL_TAC >>
  simp[diamond_actions_exact_probe, LET_THM] >>
  rewrite_tac[diamond_analysis_probe, diamond_cfg_probe] >>
  EVAL_TAC >> simp[FUN_FMAP_DEF, fmap_EXT, FAPPLY_FUPDATE_THM] >> EVAL_TAC
QED

