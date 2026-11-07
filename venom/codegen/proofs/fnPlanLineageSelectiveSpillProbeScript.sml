Theory fnPlanLineageSelectiveSpillProbe
Ancestors fnPlanLineage fnPlanLineageNativeOriginProbe fnPlanLineageEntryProbe codegenReadyCompute
  stackPlanGen stackPlanTypes stackPlanOps stackModel livenessDefs cfgDefs
  venomInst cfgTransform finite_map
Libs wordsLib fnPlanLineageProbeLib

val _ = computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY];

(* Eight static variants, each intended for one and two native traversals.
   Parameters: 17/18 live-through names, definition order, later-use order. *)
Definition selective_names_def:
  selective_names n = TAKE n (residual_pressure_names ++ ["v17"])
End
Definition selective_order_def:
  selective_order r xs = if r then REVERSE xs else xs
End
Definition selective_fn_def:
  selective_fn n r u = entry_loop_fn with fn_blocks :=
    LUPDATE ((EL 0 entry_loop_fn.fn_blocks) with bb_instructions :=
      MAPi (\i v. mk_inst (10+i) ADD [Lit 3w; Lit 4w] [v])
        (selective_order r (selective_names n)) ++
      [mk_inst 0 ADD [Lit 0w; Lit 1w] ["a"];
       mk_inst 1 JMP [Label "H"] []]) 0
    (LUPDATE ((EL 1 entry_loop_fn.fn_blocks) with bb_instructions :=
      [mk_inst 2 PHI [Label "entry"; Var "a"; Label "back"; Var "n"] ["x"];
       mk_inst 7 ADD [Var "x"; Var (LAST (selective_names n))] ["hold"]] ++
      MAPi (\i v. mk_inst (100+i) ADD [Var v; Lit 1w] [STRCAT "dead_" v])
        (selective_order u (FRONT (selective_names n))) ++
      [mk_inst 3 ADD [Var "hold"; Lit 1w] ["n"];
       mk_inst 4 JNZ [Lit 1w; Label "back"; Label "exit"] []])
      1 entry_loop_fn.fn_blocks)
End

Theorem selective_17_forward_ready:
  codegen_ready_fn (selective_fn 17 F F)
Proof
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem selective_17_forward_markers:
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) (selective_fn 17 F F).fn_blocks
Proof
  EVAL_TAC
QED


Definition selective_lv_def:
  selective_lv = liveness_analyze (selective_fn 17 F F)
End
Definition selective_dg_def:
  selective_dg = dfg_build_function (selective_fn 17 F F)
End
Definition selective_cg_def:
  selective_cg = cfg_analyze (selective_fn 17 F F)
End
Definition selective_run_def:
  selective_run i ps = generate_block_plan selective_lv selective_dg selective_cg
    (selective_fn 17 F F) (EL i (selective_fn 17 F F).fn_blocks) ps
End
Definition selective_entry_def:
  selective_entry = SND (THE (selective_run 0 entry_probe_start))
End

Theorem selective_entry_some:
  IS_SOME (selective_run 0 entry_probe_start)
Proof
  rewrite_tac[selective_run_def] >>
  CONV_TAC (RAND_CONV (funpow 5 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (funpow 4 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (funpow 3 RATOR_CONV (RAND_CONV EVAL))) >> EVAL_TAC
QED

Theorem selective_entry_stack:
  selective_entry.ps_stack = REVERSE (MAP Var (FRONT (selective_names 17))) ++
    [Var "v16"; Var "a"]
Proof
  EVAL_TAC
QED

Definition selective_header_after_def:
  selective_header_after = SND (THE (selective_run 1 selective_entry))
End
Definition selective_back_after_def:
  selective_back_after = SND (THE (selective_run 2 selective_header_after))
End
Definition selective_reentry_def:
  selective_reentry = selective_entry with
    <|ps_stack := selective_back_after.ps_stack;
      ps_spilled := selective_back_after.ps_spilled|>
End

Theorem selective_header_some:
  IS_SOME (selective_run 1 selective_entry)
Proof
  rewrite_tac[selective_run_def] >>
  CONV_TAC (RAND_CONV (funpow 5 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (funpow 4 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (funpow 3 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >> EVAL_TAC
QED

Theorem selective_header_cache:
  selective_header_after = entry_probe_start with
    <|ps_stack := REVERSE (MAP Var (FRONT (selective_names 17))) ++ [Var "v16"; Var "n"];
      ps_alloc := <|sa_free_slots :=
        [0;32;64;96;128;160;192;224;256;288;320;352;384;416;448;512;544;480];
        sa_next_offset := 576; sa_spill_base := 0|> |>
Proof
  rewrite_tac[selective_header_after_def, selective_run_def] >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 5 RATOR_CONV (RAND_CONV EVAL))))) >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 4 RATOR_CONV (RAND_CONV EVAL))))) >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 3 RATOR_CONV (RAND_CONV EVAL))))) >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV EVAL)))) >>
  CONV_TAC (LAND_CONV EVAL) >> EVAL_TAC
QED

Theorem selective_back_some:
  IS_SOME (selective_run 2 selective_header_after)
Proof
  rewrite_tac[selective_header_cache, selective_run_def] >>
  CONV_TAC (RAND_CONV (funpow 5 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (funpow 4 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (funpow 3 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >> EVAL_TAC
QED

Theorem selective_back_cache:
  selective_back_after = selective_header_after
Proof
  rewrite_tac[selective_back_after_def, selective_header_cache, selective_run_def] >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 5 RATOR_CONV (RAND_CONV EVAL))))) >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 4 RATOR_CONV (RAND_CONV EVAL))))) >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 3 RATOR_CONV (RAND_CONV EVAL))))) >>
  EVAL_TAC
QED

Theorem selective_reentry_stack:
  selective_reentry.ps_stack = REVERSE (MAP Var (FRONT (selective_names 17))) ++
    [Var "v16"; Var "n"] /\
  selective_reentry.ps_spilled = FEMPTY
Proof
  simp[selective_reentry_def, selective_back_cache, selective_header_cache,
    entry_probe_start_def, init_cleanup_plan_state_def, init_plan_state_def]
QED

Theorem selective_entry_result:
  ?ops. selective_run 0 entry_probe_start = SOME (ops, selective_entry)
Proof
  mp_tac selective_entry_some >>
  Cases_on `selective_run 0 entry_probe_start` >> simp[selective_entry_def] >>
  PairCases_on `x` >> simp[]
QED

Theorem selective_entry_call:
  dfs_aux_call selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start ["entry"] [] entry_probe_start
Proof
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem selective_entry_succs:
  dfs_succs_call selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start selective_entry.ps_stack selective_entry.ps_spilled
    ["H"] ["entry"] selective_entry
Proof
  `["H"] = cfg_succs_of selective_cg "entry"` by EVAL_TAC >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_succs >>
  conj_tac >- simp[] >>
  qx_choose_then `ops` assume_tac selective_entry_result >>
  qexistsl_tac [`EL 0 (selective_fn 17 F F).fn_blocks`, `ops`, `entry_probe_start`, `[]`] >>
  simp[selective_entry_call, GSYM selective_run_def] >>
  CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED

Theorem selective_header_call:
  dfs_aux_call selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start ["H"] ["entry"] selective_entry
Proof
  mp_tac selective_entry_succs >>
  disch_then (mp_tac o MATCH_MP dfs_aux_call_branch) >> simp[]
QED

Theorem selective_header_dfs:
  dfs_block_state selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start "H" selective_entry
Proof
  simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `["entry"]`] >>
  simp[selective_header_call]
QED

Definition selective_phi_def:
  selective_phi ps = SND (generate_phi_plan
    (HD (EL 1 (selective_fn 17 F F).fn_blocks).bb_instructions)
    (live_vars_at selective_lv "H" 1) F ps)
End

Theorem selective_entry_cache:
  selective_entry = entry_probe_start with
    <|ps_stack := REVERSE (MAP Var (FRONT (selective_names 17))) ++ [Var "v16"; Var "a"];
      ps_alloc := <|sa_free_slots :=
        [0;32;64;96;128;160;192;224;256;288;320;352;384;416;448;480;512;544];
        sa_next_offset := 576; sa_spill_base := 0|> |>
Proof
  CONV_TAC (LAND_CONV EVAL) >> EVAL_TAC
QED

Theorem selective_phi_stack:
  (selective_phi selective_entry).ps_stack =
    REVERSE (MAP Var (FRONT (selective_names 17))) ++ [Var "v16"; Var "x"] /\
  (selective_phi selective_reentry).ps_stack =
    (selective_phi selective_entry).ps_stack /\
  (selective_phi selective_reentry).ps_spilled = FEMPTY
Proof
  rewrite_tac[selective_reentry_def, selective_back_cache, selective_header_cache,
    selective_entry_cache] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem selective_header_result:
  ?ops. selective_run 1 selective_entry = SOME (ops, selective_header_after)
Proof
  mp_tac selective_header_some >>
  Cases_on `selective_run 1 selective_entry` >> simp[selective_header_after_def] >>
  PairCases_on `x` >> simp[]
QED

Theorem selective_back_result:
  ?ops. selective_run 2 selective_header_after = SOME (ops, selective_header_after)
Proof
  mp_tac selective_back_some >>
  Cases_on `selective_run 2 selective_header_after` >>
  simp[GSYM selective_back_cache, selective_back_after_def] >>
  PairCases_on `x` >> simp[]
QED

Definition selective_exit_after_def:
  selective_exit_after = SND (THE (selective_run 3 selective_header_after))
End

Theorem selective_exit_some:
  IS_SOME (selective_run 3 selective_header_after)
Proof
  rewrite_tac[selective_header_cache, selective_run_def] >>
  CONV_TAC (RAND_CONV (funpow 5 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (funpow 4 RATOR_CONV (RAND_CONV EVAL))) >>
  CONV_TAC (RAND_CONV (funpow 3 RATOR_CONV (RAND_CONV EVAL))) >> EVAL_TAC
QED

Theorem selective_exit_result:
  ?ops. selective_run 3 selective_header_after = SOME (ops, selective_exit_after)
Proof
  mp_tac selective_exit_some >>
  Cases_on `selective_run 3 selective_header_after` >> simp[selective_exit_after_def] >>
  PairCases_on `x` >> simp[]
QED

Theorem selective_exit_cache:
  selective_exit_after = selective_header_after with ps_stack := []
Proof
  rewrite_tac[selective_exit_after_def, selective_header_cache, selective_run_def] >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 5 RATOR_CONV (RAND_CONV EVAL))))) >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 4 RATOR_CONV (RAND_CONV EVAL))))) >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV
    (funpow 3 RATOR_CONV (RAND_CONV EVAL))))) >> EVAL_TAC
QED

Theorem selective_exit_sibling_metadata:
  selective_header_after with
    <|ps_alloc := selective_exit_after.ps_alloc with
        sa_free_slots := selective_header_after.ps_alloc.sa_free_slots;
      ps_label_counter := selective_exit_after.ps_label_counter|> = selective_header_after
Proof
  simp[selective_exit_cache]
QED

Theorem selective_cfg_cache:
  cfg_succs_of selective_cg "entry" = ["H"] /\
  cfg_succs_of selective_cg "H" = ["exit";"back"] /\
  cfg_succs_of selective_cg "back" = ["H"] /\
  cfg_succs_of selective_cg "exit" = []
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem selective_lookup_cache:
  lookup_block "entry" (selective_fn 17 F F).fn_blocks =
    SOME (EL 0 (selective_fn 17 F F).fn_blocks) /\
  lookup_block "H" (selective_fn 17 F F).fn_blocks =
    SOME (EL 1 (selective_fn 17 F F).fn_blocks) /\
  lookup_block "back" (selective_fn 17 F F).fn_blocks =
    SOME (EL 2 (selective_fn 17 F F).fn_blocks) /\
  lookup_block "exit" (selective_fn 17 F F).fn_blocks =
    SOME (EL 3 (selective_fn 17 F F).fn_blocks)
Proof
  rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED

Theorem selective_back_traversal:
  ?ops. generate_fn_plan_aux selective_lv selective_dg selective_cg
    (selective_fn 17 F F) ["back"] ["exit";"H";"entry"] selective_header_after =
    SOME (ops, ["back";"exit";"H";"entry"], selective_header_after)
Proof
  qx_choose_then `ops` assume_tac selective_back_result >>
  simp[Once generate_fn_plan_aux_def, selective_lookup_cache,
    GSYM selective_run_def] >>
  simp[Once (cj 4 generate_fn_plan_aux_def)] >>
  simp[selective_cfg_cache, Once (cj 4 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once (cj 3 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def]
QED

Theorem selective_exit_traversal:
  ?ops. generate_fn_plan_aux selective_lv selective_dg selective_cg
    (selective_fn 17 F F) ["exit"] ["H";"entry"] selective_header_after =
    SOME (ops, ["exit";"H";"entry"], selective_exit_after)
Proof
  qx_choose_then `ops` assume_tac selective_exit_result >>
  simp[Once generate_fn_plan_aux_def, selective_lookup_cache,
    GSYM selective_run_def, selective_cfg_cache] >>
  simp[Once (cj 3 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def]
QED

Theorem selective_header_traversal:
  ?ops. generate_fn_plan_aux selective_lv selective_dg selective_cg
    (selective_fn 17 F F) ["H"] ["entry"] selective_entry =
    SOME (ops, ["back";"exit";"H";"entry"], selective_header_after)
Proof
  qx_choose_then `hops` assume_tac selective_header_result >>
  qx_choose_then `eops` assume_tac selective_exit_traversal >>
  qx_choose_then `bops` assume_tac selective_back_traversal >>
  simp[Once generate_fn_plan_aux_def, selective_lookup_cache,
    GSYM selective_run_def, selective_cfg_cache] >>
  simp[Once (cj 4 generate_fn_plan_aux_def)] >>
  simp[selective_exit_sibling_metadata] >>
  simp[Once (cj 4 generate_fn_plan_aux_def)] >>
  simp[Once (cj 3 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def]
QED

Definition selective_root_after_def:
  selective_root_after = selective_entry with
    <|ps_alloc := selective_header_after.ps_alloc with
        sa_free_slots := selective_entry.ps_alloc.sa_free_slots;
      ps_label_counter := selective_header_after.ps_label_counter|>
End

Theorem selective_root_traversal:
  ?ops. generate_fn_plan_aux selective_lv selective_dg selective_cg
    (selective_fn 17 F F) ["entry"] [] entry_probe_start =
    SOME (ops, ["back";"exit";"H";"entry"], selective_root_after)
Proof
  qx_choose_then `eops` assume_tac selective_entry_result >>
  qx_choose_then `hops` assume_tac selective_header_traversal >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [selective_run_def, listTheory.EL]) >>
  simp[Once generate_fn_plan_aux_def, selective_lookup_cache,
    GSYM selective_run_def, selective_cfg_cache] >>
  simp[Once (cj 4 generate_fn_plan_aux_def)] >>
  simp[Once (cj 3 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def, selective_root_after_def]
QED

Theorem selective_17_forward_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze (selective_fn 17 F F)) (dfg_build_function (selective_fn 17 F F))
    (cfg_analyze (selective_fn 17 F F)) NONE [] (selective_fn 17 F F) 0 0)
Proof
  `canonical_param_prefix (selective_fn 17 F F)` by EVAL_TAC >>
  `fn_entry_label (selective_fn 17 F F) = SOME "entry"` by EVAL_TAC >>
  qx_choose_then `ops` assume_tac selective_root_traversal >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, GSYM selective_lv_def,
    GSYM selective_dg_def, GSYM selective_cg_def, GSYM entry_probe_start_def]
QED

Theorem selective_header_lineage:
  lineage_state selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start "H" selective_entry
Proof
  irule dfs_block_state_lineage_state >> simp[selective_header_dfs]
QED

Theorem selective_phi_exact:
  selective_phi selective_reentry = selective_phi selective_entry
Proof
  rewrite_tac[selective_reentry_def, selective_back_cache, selective_header_cache,
    selective_entry_cache] >> EVAL_TAC
QED

Theorem selective_reentry_replay:
  selective_run 1 selective_reentry = selective_run 1 selective_entry
Proof
  rewrite_tac[selective_reentry_def, selective_back_cache, selective_header_cache,
    selective_entry_cache, selective_run_def] >>
  CONV_TAC (eval_def_occurrences selective_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_cg_def) >> EVAL_TAC
QED

Theorem selective_header_succs:
  dfs_succs_call selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start selective_header_after.ps_stack selective_header_after.ps_spilled
    ["exit";"back"] ["H";"entry"] selective_header_after
Proof
  qx_choose_then `ops` assume_tac selective_header_result >>
  ` ["exit";"back"] = cfg_succs_of selective_cg "H"` by simp[selective_cfg_cache] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`EL 1 (selective_fn 17 F F).fn_blocks`, `ops`, `selective_entry`, `[]`] >>
  simp[selective_header_call, selective_lookup_cache, GSYM selective_run_def]
QED

Theorem selective_back_call:
  dfs_aux_call selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start ["back"] ["exit";"H";"entry"] selective_header_after
Proof
  qx_choose_then `ops` assume_tac selective_exit_traversal >>
  `dfs_succs_call selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start selective_header_after.ps_stack selective_header_after.ps_spilled
    ["back"] ["exit";"H";"entry"] selective_header_after` suffices_by
      (disch_then (mp_tac o MATCH_MP dfs_aux_call_branch) >> simp[]) >>
  once_rewrite_tac[GSYM selective_exit_sibling_metadata] >>
  irule dfs_aux_call_sibling >> simp[] >>
  qexistsl_tac [`ops`, `"exit"`, `["H";"entry"]`] >>
  simp[selective_header_succs]
QED

Theorem selective_back_dfs:
  dfs_block_state selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start "back" selective_header_after
Proof
  simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `["exit";"H";"entry"]`] >>
  simp[selective_back_call]
QED

Theorem selective_back_lineage:
  lineage_state selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start "back" selective_header_after
Proof
  irule dfs_block_state_lineage_state >> simp[selective_back_dfs]
QED

Theorem selective_reentry_lineage:
  lineage_state selective_lv selective_dg selective_cg (selective_fn 17 F F)
    entry_probe_start "H" selective_reentry
Proof
  rewrite_tac[selective_reentry_def] >> irule lineage_state_step >>
  conj_tac >- simp[selective_header_dfs] >>
  qx_choose_then `ops` assume_tac selective_back_result >>
  `selective_header_after with <|ps_cleanup_height := NONE;
      ps_cleanup_promised := F|> = selective_header_after` by
    simp[selective_header_cache, entry_probe_start_def, init_cleanup_plan_state_def,
      init_plan_state_def] >>
  qexists_tac `EL 2 (selective_fn 17 F F).fn_blocks` >>
  qexists_tac `ops` >> qexists_tac `NONE` >> qexists_tac `"back"` >>
  qexists_tac `F` >> qexists_tac `selective_header_after` >>
  qexists_tac `selective_header_after` >> qexists_tac `selective_back_after` >>
  simp[selective_back_lineage, selective_back_dfs, selective_back_cache,
    selective_lookup_cache, GSYM selective_run_def, selective_cfg_cache]
QED

(* Actual instruction-indexed phases, with the original block's liveness and
   successor opcode (not a truncated block with a changed live-out). *)
Definition selective_phase_def:
  selective_phase 0 = selective_entry /\
  selective_phase (SUC i) = SND (THE (generate_inst_plan selective_lv selective_dg
    selective_cg (selective_fn 17 F F)
    (EL i (EL 1 (selective_fn 17 F F).fn_blocks).bb_instructions)
    (live_vars_at selective_lv "H" (SUC i)) F
    (if SUC i < LENGTH (EL 1 (selective_fn 17 F F).fn_blocks).bb_instructions then
       is_terminator (EL (SUC i)
         (EL 1 (selective_fn 17 F F).fn_blocks).bb_instructions).inst_opcode
     else F)
    "H" (selective_phase i)))
End

Theorem selective_first_input_depth:
  stack_get_depth (Var "v16") (selective_phi selective_entry).ps_stack = SOME 1
Proof
  rewrite_tac[selective_entry_cache] >> EVAL_TAC
QED

Theorem selective_phase_phi:
  selective_phase 1 = selective_phi selective_entry
Proof
  `1 = SUC 0` by decide_tac >> pop_assum (fn th => pure_rewrite_tac[th]) >>
  rewrite_tac[selective_phase_def, selective_phi_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV selective_fn_def THENC EVAL)) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``selective_lv``, ``selective_dg``, ``selective_cg``,
     ``selective_entry``, ``generate_phi_plan``])
QED

Theorem selective_first_add_spills:
  (selective_phase 2).ps_spilled = FEMPTY
Proof
  `2 = SUC 1` by decide_tac >> pop_assum (fn th => pure_rewrite_tac[th]) >>
  pure_once_rewrite_tac[selective_phase_def] >>
  rewrite_tac[selective_phase_phi, selective_entry_cache] >>
  CONV_TAC (eval_def_occurrences selective_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_cg_def) >> EVAL_TAC
QED

(* Shared shape and native-state boundaries for the bounded family. *)
Definition selective_shape_def:
  selective_shape cfg fn eb hb bb xb <=>
    fn_entry_label fn = SOME "entry" /\
    lookup_block "entry" fn.fn_blocks = SOME eb /\
    lookup_block "H" fn.fn_blocks = SOME hb /\
    lookup_block "back" fn.fn_blocks = SOME bb /\
    lookup_block "exit" fn.fn_blocks = SOME xb /\
    cfg_succs_of cfg "entry" = ["H"] /\
    cfg_succs_of cfg "H" = ["exit";"back"] /\
    cfg_succs_of cfg "back" = ["H"] /\ cfg_succs_of cfg "exit" = []
End
Definition selective_rebase_def:
  selective_rebase base after = base with
    <|ps_stack := after.ps_stack; ps_spilled := after.ps_spilled|>
End
Definition selective_merge_def:
  selective_merge base after = base with
    <|ps_alloc := after.ps_alloc with sa_free_slots := base.ps_alloc.sa_free_slots;
      ps_label_counter := after.ps_label_counter|>
End

Theorem selective_shape_back_traversal:
  selective_shape cg fn eb hb bb xb /\
  generate_block_plan lv dg cg fn bb B = SOME (bops, A) ==>
  generate_fn_plan_aux lv dg cg fn ["back"] ["exit";"H";"entry"] B =
    SOME (bops, ["back";"exit";"H";"entry"], selective_merge A A)
Proof
  simp[selective_shape_def] >> rpt strip_tac >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once (cj 4 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once (cj 3 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def, selective_merge_def]
QED

Theorem selective_shape_exit_traversal:
  selective_shape cg fn eb hb bb xb /\
  generate_block_plan lv dg cg fn xb H = SOME (xops, X) ==>
  generate_fn_plan_aux lv dg cg fn ["exit"] ["H";"entry"] H =
    SOME (xops, ["exit";"H";"entry"], X)
Proof
  simp[selective_shape_def] >> rpt strip_tac >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once (cj 3 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def]
QED

Theorem selective_merge_stack_restore[simp]:
  selective_merge ps after with
    <|ps_stack := ps.ps_stack; ps_spilled := ps.ps_spilled|> =
  selective_merge ps after
Proof
  simp[selective_merge_def, plan_state_component_equality]
QED

Theorem selective_shape_header_traversal:
  selective_shape cg fn eb hb bb xb /\
  generate_block_plan lv dg cg fn hb E = SOME (hops, H) /\
  generate_block_plan lv dg cg fn xb H = SOME (xops, X) /\
  B = selective_merge H X /\
  generate_block_plan lv dg cg fn bb B = SOME (bops, A) ==>
  ?ops. generate_fn_plan_aux lv dg cg fn ["H"] ["entry"] E =
    SOME (ops, ["back";"exit";"H";"entry"], selective_merge B (selective_merge A A))
Proof
  rpt strip_tac >> qpat_x_assum `B = _` SUBST_ALL_TAC >>
  drule_all selective_shape_exit_traversal >> strip_tac >>
  drule_all selective_shape_back_traversal >> strip_tac >>
  fs[selective_shape_def] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once (cj 4 generate_fn_plan_aux_def), GSYM selective_merge_def] >>
  simp[Once (cj 4 generate_fn_plan_aux_def), GSYM selective_merge_def] >>
  simp[Once (cj 3 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def]
QED

Theorem selective_shape_root_traversal:
  selective_shape cg fn eb hb bb xb /\
  generate_block_plan lv dg cg fn eb ps0 = SOME (eops, E) /\
  generate_fn_plan_aux lv dg cg fn ["H"] ["entry"] E =
    SOME (hops, ["back";"exit";"H";"entry"], Z) ==>
  ?ops. generate_fn_plan_aux lv dg cg fn ["entry"] [] ps0 =
    SOME (ops, ["back";"exit";"H";"entry"], selective_merge E Z)
Proof
  simp[selective_shape_def] >> rpt strip_tac >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once (cj 4 generate_fn_plan_aux_def), GSYM selective_merge_def] >>
  simp[Once (cj 3 generate_fn_plan_aux_def)] >>
  simp[Once generate_fn_plan_aux_def]
QED

Theorem selective_shape_header_call:
  selective_shape cg fn eb hb bb xb /\
  generate_block_plan lv dg cg fn eb ps0 = SOME (eops, E) ==>
  dfs_aux_call lv dg cg fn ps0 ["H"] ["entry"] E
Proof
  rpt strip_tac >> fs[selective_shape_def] >>
  `E = E with <|ps_stack := E.ps_stack; ps_spilled := E.ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_branch >> qexists_tac `[]` >>
  qpat_x_assum `cfg_succs_of cg "entry" = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`eops`, `ps0`, `[]`] >>
  simp[dfs_aux_call_entry]
QED

Theorem selective_shape_back_dfs:
  selective_shape cg fn eb hb bb xb /\
  generate_block_plan lv dg cg fn eb ps0 = SOME (eops, E) /\
  generate_block_plan lv dg cg fn hb E = SOME (hops, H) /\
  generate_block_plan lv dg cg fn xb H = SOME (xops, X) ==>
  dfs_block_state lv dg cg fn ps0 "back" (selective_merge H X)
Proof
  rpt strip_tac >>
  drule_all selective_shape_header_call >> strip_tac >>
  drule_all selective_shape_exit_traversal >> strip_tac >>
  fs[selective_shape_def] >>
  simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `["exit";"H";"entry"]`] >> simp[] >>
  once_rewrite_tac[GSYM selective_merge_stack_restore] >>
  irule dfs_aux_call_branch >> qexists_tac `[]` >>
  simp[selective_merge_def] >>
  irule dfs_aux_call_sibling >> simp[] >>
  qexistsl_tac [`xops`, `"exit"`, `["H";"entry"]`] >> simp[] >>
  qpat_x_assum `cfg_succs_of cg "H" = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule dfs_aux_call_succs >> simp[] >>
  qexistsl_tac [`hops`, `E`, `[]`] >> simp[]
QED

Definition selective_case_lv_def:
  selective_case_lv n r u = liveness_analyze (selective_fn n r u)
End
Definition selective_case_dg_def:
  selective_case_dg n r u = dfg_build_function (selective_fn n r u)
End
Definition selective_case_cg_def:
  selective_case_cg n r u = cfg_analyze (selective_fn n r u)
End
Definition selective_case_run_def:
  selective_case_run n r u i ps = generate_block_plan
    (selective_case_lv n r u) (selective_case_dg n r u) (selective_case_cg n r u)
    (selective_fn n r u) (EL i (selective_fn n r u).fn_blocks) ps
End
Definition selective_case_entry_def:
  selective_case_entry n r u = SND (THE (selective_case_run n r u 0 entry_probe_start))
End
Definition selective_case_header_def:
  selective_case_header n r u = SND (THE
    (selective_case_run n r u 1 (selective_case_entry n r u)))
End
Definition selective_case_exit_def:
  selective_case_exit n r u = SND (THE
    (selective_case_run n r u 3 (selective_case_header n r u)))
End
Definition selective_case_back_base_def:
  selective_case_back_base n r u = selective_merge
    (selective_case_header n r u) (selective_case_exit n r u)
End
Definition selective_case_back_def:
  selective_case_back n r u = SND (THE
    (selective_case_run n r u 2 (selective_case_back_base n r u)))
End

Theorem selective_cases_ready:
  (n = 17 \/ n = 18) ==> codegen_ready_fn (selective_fn n r u)
Proof
  strip_tac >> gvs[]
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "a" >> suspend "b") >>
      Cases_on `u` >- suspend "c" >> suspend "d") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "e" >> suspend "f") >>
  Cases_on `u` >- suspend "g" >> suspend "h"
QED
Resume selective_cases_ready[a]:
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
Resume selective_cases_ready[b]:
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
Resume selective_cases_ready[c]:
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
Resume selective_cases_ready[d]:
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
Resume selective_cases_ready[e]:
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
Resume selective_cases_ready[f]:
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
Resume selective_cases_ready[g]:
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
Resume selective_cases_ready[h]:
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED
Finalise selective_cases_ready

Theorem selective_cases_markers:
  (n = 17 \/ n = 18) ==>
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) (selective_fn n r u).fn_blocks
Proof
  strip_tac >> gvs[] >> Cases_on `r` >> Cases_on `u` >> EVAL_TAC
QED

Theorem selective_cases_shape:
  (n = 17 \/ n = 18) ==>
  selective_shape (selective_case_cg n r u) (selective_fn n r u)
    (EL 0 (selective_fn n r u).fn_blocks) (EL 1 (selective_fn n r u).fn_blocks)
    (EL 2 (selective_fn n r u).fn_blocks) (EL 3 (selective_fn n r u).fn_blocks)
Proof
  strip_tac >> gvs[]
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "a" >> suspend "b") >>
      Cases_on `u` >- suspend "c" >> suspend "d") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "e" >> suspend "f") >>
  Cases_on `u` >- suspend "g" >> suspend "h"
QED
Resume selective_cases_shape[a]:
  rewrite_tac[selective_shape_def] >> rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED
Resume selective_cases_shape[b]:
  rewrite_tac[selective_shape_def] >> rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED
Resume selective_cases_shape[c]:
  rewrite_tac[selective_shape_def] >> rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED
Resume selective_cases_shape[d]:
  rewrite_tac[selective_shape_def] >> rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED
Resume selective_cases_shape[e]:
  rewrite_tac[selective_shape_def] >> rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED
Resume selective_cases_shape[f]:
  rewrite_tac[selective_shape_def] >> rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED
Resume selective_cases_shape[g]:
  rewrite_tac[selective_shape_def] >> rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED
Resume selective_cases_shape[h]:
  rewrite_tac[selective_shape_def] >> rpt conj_tac >> CONV_TAC (BINOP_CONV EVAL) >> simp[]
QED
Finalise selective_cases_shape

Theorem selective_cases_entry_some:
  (n = 17 \/ n = 18) ==>
  IS_SOME (selective_case_run n r u 0 entry_probe_start)
Proof
  strip_tac >> gvs[]
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "a" >> suspend "b") >>
      Cases_on `u` >- suspend "c" >> suspend "d") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "e" >> suspend "f") >>
  Cases_on `u` >- suspend "g" >> suspend "h"
QED
Resume selective_cases_entry_some[a]:
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_entry_some[b]:
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_entry_some[c]:
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_entry_some[d]:
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_entry_some[e]:
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_entry_some[f]:
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_entry_some[g]:
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_entry_some[h]:
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Finalise selective_cases_entry_some

Theorem selective_cases_entry_result:
  (n = 17 \/ n = 18) ==>
  ?ops. selective_case_run n r u 0 entry_probe_start =
    SOME (ops, selective_case_entry n r u)
Proof
  disch_tac >>
  `IS_SOME (selective_case_run n r u 0 entry_probe_start)` by
    metis_tac[selective_cases_entry_some] >> pop_assum mp_tac >>
  Cases_on `selective_case_run n r u 0 entry_probe_start` >>
  simp[selective_case_entry_def] >> PairCases_on `x` >> simp[]
QED

Theorem selective_cases_header_some:
  (n = 17 \/ n = 18) ==>
  IS_SOME (selective_case_run n r u 1 (selective_case_entry n r u))
Proof
  strip_tac >> gvs[]
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "a" >> suspend "b") >>
      Cases_on `u` >- suspend "c" >> suspend "d") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "e" >> suspend "f") >>
  Cases_on `u` >- suspend "g" >> suspend "h"
QED
Resume selective_cases_header_some[a]:
  rewrite_tac[selective_case_entry_def] >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_DEPTH_CONV (REWR_CONV selective_case_run_def)))) >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >>
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_header_some[b]:
  rewrite_tac[selective_case_entry_def] >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_DEPTH_CONV (REWR_CONV selective_case_run_def)))) >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >>
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_header_some[c]:
  rewrite_tac[selective_case_entry_def] >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_DEPTH_CONV (REWR_CONV selective_case_run_def)))) >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >>
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_header_some[d]:
  rewrite_tac[selective_case_entry_def] >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_DEPTH_CONV (REWR_CONV selective_case_run_def)))) >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >>
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_header_some[e]:
  rewrite_tac[selective_case_entry_def] >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_DEPTH_CONV (REWR_CONV selective_case_run_def)))) >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >>
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_header_some[f]:
  rewrite_tac[selective_case_entry_def] >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_DEPTH_CONV (REWR_CONV selective_case_run_def)))) >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >>
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_header_some[g]:
  rewrite_tac[selective_case_entry_def] >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_DEPTH_CONV (REWR_CONV selective_case_run_def)))) >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >>
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Resume selective_cases_header_some[h]:
  rewrite_tac[selective_case_entry_def] >>
  CONV_TAC (RAND_CONV (RAND_CONV
    (ONCE_DEPTH_CONV (REWR_CONV selective_case_run_def)))) >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (RAND_CONV (RAND_CONV EVAL)) >>
  rewrite_tac[selective_case_run_def] >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_lv_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_dg_def THENC EVAL)) >>
  CONV_TAC (ONCE_DEPTH_CONV (REWR_CONV selective_case_cg_def THENC EVAL)) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED
Finalise selective_cases_header_some

Theorem selective_cases_header_result:
  (n = 17 \/ n = 18) ==>
  ?ops. selective_case_run n r u 1 (selective_case_entry n r u) =
    SOME (ops, selective_case_header n r u)
Proof
  disch_tac >>
  `IS_SOME (selective_case_run n r u 1 (selective_case_entry n r u))` by
    metis_tac[selective_cases_header_some] >> pop_assum mp_tac >>
  Cases_on `selective_case_run n r u 1 (selective_case_entry n r u)` >>
  simp[selective_case_header_def] >> PairCases_on `x` >> simp[]
QED

Theorem selective_cases_header_dfs:
  (n = 17 \/ n = 18) ==>
  dfs_block_state (selective_case_lv n r u) (selective_case_dg n r u)
    (selective_case_cg n r u) (selective_fn n r u) entry_probe_start
    "H" (selective_case_entry n r u)
Proof
  disch_tac >>
  `?ops. selective_case_run n r u 0 entry_probe_start =
    SOME (ops, selective_case_entry n r u)` by
      metis_tac[selective_cases_entry_result] >>
  simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `["entry"]`] >> simp[] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [selective_case_run_def]) >>
  irule selective_shape_header_call >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`EL 2 (selective_fn n r u).fn_blocks`,
    `EL 1 (selective_fn n r u).fn_blocks`, `EL 3 (selective_fn n r u).fn_blocks`] >>
  simp[] >> irule (SRULE [listTheory.EL] selective_cases_shape) >> simp[]
QED

Theorem selective_second_reentry_fixed:
  selective_rebase selective_header_after
    (SND (THE (selective_run 1 selective_reentry))) = selective_header_after /\
  selective_rebase selective_entry
    (SND (THE (selective_run 2 selective_header_after))) = selective_reentry
Proof
  simp[selective_reentry_replay, GSYM selective_header_after_def,
    GSYM selective_back_after_def, selective_rebase_def, selective_reentry_def]
QED

Theorem selective_third_phase_spills:
  (selective_phase 3).ps_spilled = FEMPTY
Proof
  `3 = SUC (SUC (SUC 0))` by decide_tac >> pop_assum (fn th => pure_rewrite_tac[th]) >>
  rewrite_tac[selective_phase_def, selective_entry_cache] >>
  CONV_TAC (eval_def_occurrences selective_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_cg_def) >> EVAL_TAC
QED

Theorem selective_cases_exit_boundary:
  (n = 17 \/ n = 18) ==>
  IS_SOME (selective_case_run n r u 3 (selective_case_header n r u)) /\
  selective_case_back_base n r u = selective_case_header n r u
Proof
  strip_tac >> gvs[]
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "a" >> suspend "b") >>
      Cases_on `u` >- suspend "c" >> suspend "d") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "e" >> suspend "f") >>
  Cases_on `u` >- suspend "g" >> suspend "h"
QED
Resume selective_cases_exit_boundary[a]:
  rewrite_tac[selective_case_back_base_def, selective_case_exit_def,
    selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_exit_boundary[b]:
  rewrite_tac[selective_case_back_base_def, selective_case_exit_def,
    selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_exit_boundary[c]:
  rewrite_tac[selective_case_back_base_def, selective_case_exit_def,
    selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_exit_boundary[d]:
  rewrite_tac[selective_case_back_base_def, selective_case_exit_def,
    selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_exit_boundary[e]:
  rewrite_tac[selective_case_back_base_def, selective_case_exit_def,
    selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_exit_boundary[f]:
  rewrite_tac[selective_case_back_base_def, selective_case_exit_def,
    selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_exit_boundary[g]:
  rewrite_tac[selective_case_back_base_def, selective_case_exit_def,
    selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_exit_boundary[h]:
  rewrite_tac[selective_case_back_base_def, selective_case_exit_def,
    selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Finalise selective_cases_exit_boundary

Theorem selective_cases_exit_result:
  (n = 17 \/ n = 18) ==>
  ?ops. selective_case_run n r u 3 (selective_case_header n r u) =
    SOME (ops, selective_case_exit n r u)
Proof
  disch_tac >>
  `IS_SOME (selective_case_run n r u 3 (selective_case_header n r u))` by
    metis_tac[selective_cases_exit_boundary] >> pop_assum mp_tac >>
  Cases_on `selective_case_run n r u 3 (selective_case_header n r u)` >>
  simp[selective_case_exit_def] >> PairCases_on `x` >> simp[]
QED

Theorem selective_cases_back_dfs:
  (n = 17 \/ n = 18) ==>
  dfs_block_state (selective_case_lv n r u) (selective_case_dg n r u)
    (selective_case_cg n r u) (selective_fn n r u) entry_probe_start
    "back" (selective_case_back_base n r u)
Proof
  disch_tac >>
  drule selective_cases_entry_result >> disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  drule selective_cases_header_result >> disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  drule selective_cases_exit_result >> disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  rewrite_tac[selective_case_back_base_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [selective_case_run_def]) >>
  irule selective_shape_back_dfs >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexists_tac `EL 2 (selective_fn n r u).fn_blocks` >>
  irule selective_cases_shape >> simp[]
QED

Theorem selective_cases_back_some:
  (n = 17 \/ n = 18) ==>
  IS_SOME (selective_case_run n r u 2 (selective_case_back_base n r u))
Proof
  disch_tac >> drule selective_cases_exit_boundary >>
  disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  asm_rewrite_tac[] >> qpat_x_assum `selective_case_back_base _ _ _ = _` kall_tac >>
  gvs[]
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "a" >> suspend "b") >>
      Cases_on `u` >- suspend "c" >> suspend "d") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "e" >> suspend "f") >>
  Cases_on `u` >- suspend "g" >> suspend "h"
QED
Resume selective_cases_back_some[a]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_back_some[b]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_back_some[c]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_back_some[d]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_back_some[e]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_back_some[f]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_back_some[g]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_back_some[h]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Finalise selective_cases_back_some

Theorem selective_cases_back_result:
  (n = 17 \/ n = 18) ==>
  ?ops. selective_case_run n r u 2 (selective_case_back_base n r u) =
    SOME (ops, selective_case_back n r u)
Proof
  disch_tac >> drule selective_cases_back_some >>
  disch_then (qspecl_then [`u`, `r`] mp_tac) >>
  Cases_on `selective_case_run n r u 2 (selective_case_back_base n r u)` >>
  simp[selective_case_back_def] >> PairCases_on `x` >> simp[]
QED

Theorem selective_cases_root_traversal:
  (n = 17 \/ n = 18) ==>
  ?ops ps. generate_fn_plan_aux (selective_case_lv n r u)
    (selective_case_dg n r u) (selective_case_cg n r u) (selective_fn n r u)
    ["entry"] [] entry_probe_start = SOME (ops, ["back";"exit";"H";"entry"], ps)
Proof
  disch_tac >>
  drule selective_cases_entry_result >> disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  drule selective_cases_header_result >> disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  drule selective_cases_exit_result >> disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  drule selective_cases_back_result >> disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  `selective_shape (selective_case_cg n r u) (selective_fn n r u)
    (EL 0 (selective_fn n r u).fn_blocks) (EL 1 (selective_fn n r u).fn_blocks)
    (EL 2 (selective_fn n r u).fn_blocks) (EL 3 (selective_fn n r u).fn_blocks)` by
      (irule selective_cases_shape >> simp[]) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [selective_case_run_def]) >>
  `selective_case_back_base n r u = selective_merge
    (selective_case_header n r u) (selective_case_exit n r u)` by
      simp[selective_case_back_base_def] >>
  drule_all selective_shape_header_traversal >> strip_tac >>
  drule_all selective_shape_root_traversal >> strip_tac >>
  goal_assum (drule_at Any)
QED

Theorem selective_cases_success:
  (n = 17 \/ n = 18) ==>
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (selective_case_lv n r u) (selective_case_dg n r u) (selective_case_cg n r u)
    NONE [] (selective_fn n r u) 0 0)
Proof
  disch_tac >>
  `canonical_param_prefix (selective_fn n r u)` by
    (gvs[] >> Cases_on `r` >> Cases_on `u` >> EVAL_TAC) >>
  `fn_entry_label (selective_fn n r u) = SOME "entry"` by
    (gvs[] >> Cases_on `r` >> Cases_on `u` >> EVAL_TAC) >>
  drule selective_cases_root_traversal >>
  disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, GSYM entry_probe_start_def]
QED

(* A native DFS block is a lineage source; choosing its own cleanup fields
   makes the replay premise reflexive.  No physical transfer is assumed. *)
Theorem selective_dfs_edge_lineage:
  dfs_block_state lv dg cg fn ps0 lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dg cg fn bb ps = SOME (ops, after) /\
  MEM succ (cfg_succs_of cg lbl) /\
  dfs_block_state lv dg cg fn ps0 succ ps_base ==>
  lineage_state lv dg cg fn ps0 succ (selective_rebase ps_base after)
Proof
  rpt strip_tac >> rewrite_tac[selective_rebase_def] >>
  irule lineage_state_step >> conj_tac >- simp[] >>
  `ps with <|ps_cleanup_height := ps.ps_cleanup_height;
    ps_cleanup_promised := ps.ps_cleanup_promised|> = ps` by simp[] >>
  metis_tac[dfs_block_state_lineage_state]
QED

Definition selective_case_reentry_def:
  selective_case_reentry n r u = selective_rebase
    (selective_case_entry n r u) (selective_case_back n r u)
End

Theorem selective_cases_reentry_lineage:
  (n = 17 \/ n = 18) ==>
  lineage_state (selective_case_lv n r u) (selective_case_dg n r u)
    (selective_case_cg n r u) (selective_fn n r u) entry_probe_start
    "H" (selective_case_reentry n r u)
Proof
  disch_tac >>
  `dfs_block_state (selective_case_lv n r u) (selective_case_dg n r u)
    (selective_case_cg n r u) (selective_fn n r u) entry_probe_start
    "back" (selective_case_back_base n r u)` by
      (irule selective_cases_back_dfs >> simp[]) >>
  drule selective_cases_back_result >> disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [selective_case_run_def]) >>
  rewrite_tac[selective_case_reentry_def] >> irule selective_dfs_edge_lineage >>
  reverse conj_tac >- (irule selective_cases_header_dfs >> simp[]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  `selective_shape (selective_case_cg n r u) (selective_fn n r u)
    (EL 0 (selective_fn n r u).fn_blocks) (EL 1 (selective_fn n r u).fn_blocks)
    (EL 2 (selective_fn n r u).fn_blocks) (EL 3 (selective_fn n r u).fn_blocks)` by
      (irule selective_cases_shape >> simp[]) >>
  gvs[selective_shape_def] >> irule selective_cases_header_dfs >> simp[]
QED

Theorem selective_cases_reentry_replay:
  (n = 17 \/ n = 18) ==>
  selective_case_run n r u 1 (selective_case_reentry n r u) =
  selective_case_run n r u 1 (selective_case_entry n r u)
Proof
  disch_tac >>
  `selective_case_back_base n r u = selective_case_header n r u` by
    metis_tac[selective_cases_exit_boundary] >>
  rewrite_tac[selective_case_reentry_def, selective_case_back_def] >>
  asm_rewrite_tac[] >> pop_assum kall_tac >> gvs[]
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "a" >> suspend "b") >>
      Cases_on `u` >- suspend "c" >> suspend "d") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "e" >> suspend "f") >>
  Cases_on `u` >- suspend "g" >> suspend "h"
QED
Resume selective_cases_reentry_replay[a]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_reentry_replay[b]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_reentry_replay[c]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_reentry_replay[d]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_reentry_replay[e]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_reentry_replay[f]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_reentry_replay[g]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (LAND_CONV (RAND_CONV EVAL)) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Resume selective_cases_reentry_replay[h]:
  rewrite_tac[selective_case_header_def, selective_case_entry_def, selective_case_run_def] >>
  CONV_TAC (eval_def_occurrences selective_case_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_case_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_case_cg_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >>
  CONV_TAC (eval_def_occurrences entry_probe_start_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >>
  CONV_TAC (fnPlanLineageProbeLib.eval_def_innermost generate_block_plan_def) >> EVAL_TAC
QED
Finalise selective_cases_reentry_replay

Theorem selective_cases_circuit_fixed:
  (n = 17 \/ n = 18) ==>
  selective_rebase (selective_case_back_base n r u)
    (SND (THE (selective_case_run n r u 1 (selective_case_reentry n r u)))) =
    selective_case_back_base n r u /\
  selective_rebase (selective_case_entry n r u)
    (SND (THE (selective_case_run n r u 2 (selective_case_back_base n r u)))) =
    selective_case_reentry n r u
Proof
  disch_tac >>
  `selective_case_run n r u 1 (selective_case_reentry n r u) =
    selective_case_run n r u 1 (selective_case_entry n r u)` by
      (irule selective_cases_reentry_replay >> simp[]) >>
  `selective_case_back_base n r u = selective_case_header n r u` by
    metis_tac[selective_cases_exit_boundary] >>
  simp[selective_case_header_def, selective_case_reentry_def,
    selective_case_back_def, selective_rebase_def]
QED

Theorem selective_cases_second_reentry_replay:
  (n = 17 \/ n = 18) ==>
  selective_case_run n r u 1
    (selective_rebase (selective_case_entry n r u)
      (SND (THE (selective_case_run n r u 2
        (selective_rebase (selective_case_back_base n r u)
          (SND (THE (selective_case_run n r u 1 (selective_case_reentry n r u))))))))) =
  selective_case_run n r u 1 (selective_case_entry n r u)
Proof
  disch_tac >>
  drule selective_cases_circuit_fixed >>
  disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  asm_rewrite_tac[] >> irule selective_cases_reentry_replay >> simp[]
QED

(* Evaluate the original instruction context, never a truncated header.
   The accumulator records each actual optional call and advances only on SOME.
   EVERY IS_SOME on the resulting log certifies every phase of this trace. *)
Definition selective_case_inst_def:
  selective_case_inst n r u i ps = generate_inst_plan
    (selective_case_lv n r u) (selective_case_dg n r u) (selective_case_cg n r u)
    (selective_fn n r u)
    (EL i (EL 1 (selective_fn n r u).fn_blocks).bb_instructions)
    (live_vars_at (selective_case_lv n r u) "H" (SUC i)) F
    (if SUC i < LENGTH (EL 1 (selective_fn n r u).fn_blocks).bb_instructions then
      is_terminator (EL (SUC i)
        (EL 1 (selective_fn n r u).fn_blocks).bb_instructions).inst_opcode else F)
    "H" ps
End
Definition selective_case_trace_def:
  selective_case_trace n r u ps = SND (FOLDL
    (\(st, calls) i. case selective_case_inst n r u i st of
       NONE => (st, calls ++ [NONE])
     | SOME (ops, after) => (after, calls ++ [SOME (ops, after)]))
    (ps, []) (COUNT_LIST (LENGTH (EL 1 (selective_fn n r u).fn_blocks).bb_instructions)))
End
Definition selective_case_spill_phases_def:
  selective_case_spill_phases n r u ps =
    MAP FST (FILTER (\(i, result). case result of NONE => F
      | SOME (ops, after) => after.ps_spilled <> FEMPTY)
      (MAPi (\i result. (i, result)) (selective_case_trace n r u ps)))
End

(* Inspect the first case's entire log, including the last consuming ADD. *)
Theorem selective_case_trace_17_F_F:
  EVERY IS_SOME (selective_case_trace 17 F F (selective_case_entry 17 F F)) /\
  selective_case_spill_phases 17 F F (selective_case_entry 17 F F) = []
Proof
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  EVAL_TAC
QED

Theorem selective_cases_trace_certificate:
  (n = 17 \/ n = 18) ==>
  ?phases. EVERY IS_SOME (selective_case_trace n r u (selective_case_entry n r u)) /\
    selective_case_spill_phases n r u (selective_case_entry n r u) = phases
Proof
  disch_then DISJ_CASES_TAC >> qpat_x_assum `n = _` SUBST_ALL_TAC
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "trace17FF" >> suspend "trace17FT") >>
      Cases_on `u` >- suspend "trace17TF" >> suspend "trace17TT") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "trace18FF" >> suspend "trace18FT") >>
  Cases_on `u` >- suspend "trace18TF" >> suspend "trace18TT"
QED
Resume selective_cases_trace_certificate[trace17FF]:
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  pure_rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (QUANT_CONV (RAND_CONV (LAND_CONV
    (fn tm => let val th = EVAL tm
                  val _ = print ("post-call spill phases: " ^ term_to_string (rhs (concl th)) ^ "\n")
              in th end)))) >> EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qexists `[]` >> REFL_TAC
QED
Resume selective_cases_trace_certificate[trace17FT]:
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  pure_rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (QUANT_CONV (RAND_CONV (LAND_CONV
    (fn tm => let val th = EVAL tm
                  val _ = print ("17FT post-call spill phases: " ^ term_to_string (rhs (concl th)) ^ "\n")
              in th end)))) >> EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qexists `[]` >> REFL_TAC
QED
Resume selective_cases_trace_certificate[trace17TF]:
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  pure_rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (QUANT_CONV (RAND_CONV (LAND_CONV
    (fn tm => let val th = EVAL tm
                  val _ = print ("17TF post-call spill phases: " ^ term_to_string (rhs (concl th)) ^ "\n")
              in th end)))) >> EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qexists `[]` >> REFL_TAC
QED
Resume selective_cases_trace_certificate[trace17TT]:
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  pure_rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (QUANT_CONV (RAND_CONV (LAND_CONV
    (fn tm => let val th = EVAL tm
                  val _ = print ("17TT post-call spill phases: " ^ term_to_string (rhs (concl th)) ^ "\n")
              in th end)))) >> EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qexists `[]` >> REFL_TAC
QED
Resume selective_cases_trace_certificate[trace18FF]:
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  pure_rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (QUANT_CONV (RAND_CONV (LAND_CONV
    (fn tm => let val th = EVAL tm
                  val _ = print ("18FF post-call spill phases: " ^ term_to_string (rhs (concl th)) ^ "\n")
              in th end)))) >> EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qexists `[]` >> REFL_TAC
QED
Resume selective_cases_trace_certificate[trace18FT]:
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  pure_rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (QUANT_CONV (RAND_CONV (LAND_CONV
    (fn tm => let val th = EVAL tm
                  val _ = print ("18FT post-call spill phases: " ^ term_to_string (rhs (concl th)) ^ "\n")
              in th end)))) >> EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qexists `[]` >> REFL_TAC
QED
Resume selective_cases_trace_certificate[trace18TF]:
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  pure_rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (QUANT_CONV (RAND_CONV (LAND_CONV
    (fn tm => let val th = EVAL tm
                  val _ = print ("18TF post-call spill phases: " ^ term_to_string (rhs (concl th)) ^ "\n")
              in th end)))) >> EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qexists `[]` >> REFL_TAC
QED
Resume selective_cases_trace_certificate[trace18TT]:
  pure_rewrite_tac[selective_case_spill_phases_def] >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_lv_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_dg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_cg_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_fn_def) >>
  CONV_TAC (cache_context selective_case_trace_def selective_case_entry_def) >>
  pure_rewrite_tac[selective_case_trace_def] >> CONV_TAC trace_prepare >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (trace_step selective_case_inst_def) >>
  CONV_TAC (QUANT_CONV (RAND_CONV (LAND_CONV
    (fn tm => let val th = EVAL tm
                  val _ = print ("18TT post-call spill phases: " ^ term_to_string (rhs (concl th)) ^ "\n")
              in th end)))) >> EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qexists `[]` >> REFL_TAC
QED
Finalise selective_cases_trace_certificate

(* These lists measure nonempty spill maps AFTER original instruction calls,
   not transient spill/restore operations inside a call. *)
Theorem selective_cases_spill_phase_table:
  (n = 17 \/ n = 18) ==>
  selective_case_spill_phases n r u (selective_case_entry n r u) = []
Proof
  disch_tac >> gvs[]
  >- (Cases_on `r`
      >- (Cases_on `u` >- suspend "a" >> suspend "b") >>
      Cases_on `u` >- suspend "c" >> suspend "d") >>
  Cases_on `r`
  >- (Cases_on `u` >- suspend "e" >> suspend "f") >>
  Cases_on `u` >- suspend "g" >> suspend "h"
QED
Resume selective_cases_spill_phase_table[a]:
  EVAL_TAC
QED
Resume selective_cases_spill_phase_table[b]:
  EVAL_TAC
QED
Resume selective_cases_spill_phase_table[c]:
  EVAL_TAC
QED
Resume selective_cases_spill_phase_table[d]:
  EVAL_TAC
QED
Resume selective_cases_spill_phase_table[e]:
  EVAL_TAC
QED
Resume selective_cases_spill_phase_table[f]:
  EVAL_TAC
QED
Resume selective_cases_spill_phase_table[g]:
  EVAL_TAC
QED
Resume selective_cases_spill_phase_table[h]:
  EVAL_TAC
QED
Finalise selective_cases_spill_phase_table

(* This is an actual second circuit: the first edge consumes the lineage
   reentry and its checked replay, not the native DFS source in its place. *)
Theorem selective_cases_circuit_lineage:
  (n = 17 \/ n = 18) ==>
  lineage_state (selective_case_lv n r u) (selective_case_dg n r u)
    (selective_case_cg n r u) (selective_fn n r u) entry_probe_start "back"
    (selective_rebase (selective_case_back_base n r u)
      (SND (THE (selective_case_run n r u 1 (selective_case_reentry n r u))))) /\
  lineage_state (selective_case_lv n r u) (selective_case_dg n r u)
    (selective_case_cg n r u) (selective_fn n r u) entry_probe_start "H"
    (selective_rebase (selective_case_entry n r u)
      (SND (THE (selective_case_run n r u 2
        (selective_rebase (selective_case_back_base n r u)
          (SND (THE (selective_case_run n r u 1 (selective_case_reentry n r u)))))))))
Proof
  disch_tac >> conj_asm1_tac
  >- suspend "outward"
  >> suspend "return"
QED
Resume selective_cases_circuit_lineage[outward]:
  drule selective_cases_reentry_lineage >>
  disch_then (qspecl_then [`u`, `r`] assume_tac) >>
  drule selective_cases_header_dfs >>
  disch_then (qspecl_then [`u`, `r`] assume_tac) >>
  drule selective_cases_header_result >>
  disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  drule selective_cases_reentry_replay >>
  disch_then (qspecl_then [`u`, `r`] assume_tac) >>
  drule selective_cases_shape >>
  disch_then (qspecl_then [`u`, `r`]
    (strip_assume_tac o PURE_REWRITE_RULE [selective_shape_def])) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [selective_case_run_def]) >>
  asm_rewrite_tac[selective_case_run_def] >>
  rewrite_tac[selective_rebase_def] >> irule lineage_state_step >>
  conj_tac >- (irule selective_cases_back_dfs >> simp[]) >>
  `selective_case_reentry n r u with
    <|ps_cleanup_height := (selective_case_reentry n r u).ps_cleanup_height;
      ps_cleanup_promised := (selective_case_reentry n r u).ps_cleanup_promised|> =
    selective_case_reentry n r u` by simp[] >>
  simp[] >> metis_tac[listTheory.MEM]
QED
Resume selective_cases_circuit_lineage[return]:
  drule selective_cases_circuit_fixed >>
  disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `lineage_state _ _ _ _ _ "back" _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule selective_cases_back_dfs >>
  disch_then (qspecl_then [`u`, `r`] assume_tac) >>
  drule selective_cases_back_result >>
  disch_then (qspecl_then [`u`, `r`] strip_assume_tac) >>
  drule selective_cases_shape >>
  disch_then (qspecl_then [`u`, `r`]
    (strip_assume_tac o PURE_REWRITE_RULE [selective_shape_def])) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [selective_case_run_def]) >>
  rewrite_tac[selective_case_reentry_def, selective_rebase_def] >>
  irule lineage_state_step >>
  conj_tac >- (irule selective_cases_header_dfs >> simp[]) >>
  `selective_case_back_base n r u with
    <|ps_cleanup_height := (selective_case_back_base n r u).ps_cleanup_height;
      ps_cleanup_promised := (selective_case_back_base n r u).ps_cleanup_promised|> =
    selective_case_back_base n r u` by simp[] >>
  metis_tac[listTheory.MEM]
QED
Finalise selective_cases_circuit_lineage

(* Intermediate native-site inspection for C3.native_shadow_loss. *)
Theorem selective_phase_two_stack:
  (selective_phase 2).ps_stack =
    REVERSE (MAP Var (FRONT (selective_names 17))) ++ [Var "v16"; Var "hold"]
Proof
  `2 = SUC 1` by decide_tac >> pop_assum (fn th => pure_rewrite_tac[th]) >>
  pure_once_rewrite_tac[selective_phase_def] >>
  rewrite_tac[selective_phase_phi, selective_entry_cache] >>
  CONV_TAC (eval_def_occurrences selective_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_dg_def) >>
  CONV_TAC (eval_def_occurrences selective_cg_def) >> EVAL_TAC
QED

Theorem selective_phase_three_liveness:
  live_vars_at selective_lv "H" 3 =
    REVERSE (FRONT (selective_names 17)) ++ ["v16"; "hold"]
Proof
  rewrite_tac[selective_lv_def] >> EVAL_TAC
QED

(* In the existing forward fixture every pressure-name consuming ADD has
   dead outputs.  Thus none can expose a selective spill by an optimistic
   query in that same instruction, regardless of its internal reorder. *)
Theorem selective_pressure_outputs_dead:
  EVERY (\i.
    FILTER (\out. MEM out (live_vars_at selective_lv "H" (SUC i)))
      (EL i (EL 1 (selective_fn 17 F F).fn_blocks).bb_instructions).inst_outputs = [])
    (GENLIST (\i. i + 2) 16)
Proof
  CONV_TAC (eval_def_occurrences selective_lv_def) >>
  CONV_TAC (eval_def_occurrences selective_fn_def) >> EVAL_TAC
QED

(* One targeted adaptation: keep the first pressure output live by an
   immediate consumer.  The backedge is retained, so actual analysis, not
   a fabricated next-live list, decides whether the deep input is dead. *)
Definition shadow_fn_def:
  shadow_fn = selective_fn 17 F F with fn_blocks :=
    LUPDATE ((EL 1 (selective_fn 17 F F).fn_blocks) with bb_instructions :=
      TAKE 2 (EL 1 (selective_fn 17 F F).fn_blocks).bb_instructions ++
      [mk_inst 199 ADD [Var "v15"; Lit 1w] ["shadow_live"];
       mk_inst 200 ADD [Var "shadow_live"; Lit 2w] ["shadow_dead"]] ++
      TAKE 15 (DROP 2 (EL 1 (selective_fn 17 F F).fn_blocks).bb_instructions) ++
      DROP 18 (EL 1 (selective_fn 17 F F).fn_blocks).bb_instructions)
      1 (selective_fn 17 F F).fn_blocks
End
Definition shadow_lv_def:
  shadow_lv = liveness_analyze shadow_fn
End

Theorem shadow_deep_input_still_live:
  MEM "v15" (live_vars_at shadow_lv "H" 3) /\
  MEM "shadow_live" (live_vars_at shadow_lv "H" 3)
Proof
  CONV_TAC (eval_def_occurrences shadow_lv_def) >> EVAL_TAC
QED

Definition shadow_dg_def:
  shadow_dg = dfg_build_function shadow_fn
End
Definition shadow_cg_def:
  shadow_cg = cfg_analyze shadow_fn
End
Definition shadow_entry_def:
  shadow_entry = SND (THE (generate_block_plan shadow_lv shadow_dg shadow_cg
    shadow_fn (EL 0 shadow_fn.fn_blocks) entry_probe_start))
End
Definition shadow_phase_def:
  shadow_phase 0 = shadow_entry /\
  shadow_phase (SUC i) = SND (THE (generate_inst_plan shadow_lv shadow_dg
    shadow_cg shadow_fn (EL i (EL 1 shadow_fn.fn_blocks).bb_instructions)
    (live_vars_at shadow_lv "H" (SUC i)) F F "H" (shadow_phase i)))
End

Theorem shadow_ready:
  codegen_ready_fn shadow_fn
Proof
  rewrite_tac[codegen_ready_fn_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem shadow_entry_cache:
  shadow_entry = entry_probe_start with
    <|ps_stack := REVERSE (MAP Var (TAKE 15 (selective_names 17))) ++
        [Var "v15"; Var "v16"; Var "a"];
      ps_alloc := <|sa_free_slots :=
        [0;32;64;96;128;160;192;224;256;288;320;352;384;416;448;480;512;544];
        sa_next_offset := 576; sa_spill_base := 0|> |>
Proof
  rewrite_tac[shadow_entry_def, selective_entry_cache] >>
  CONV_TAC (eval_def_occurrences shadow_lv_def) >>
  CONV_TAC (eval_def_occurrences shadow_dg_def) >>
  CONV_TAC (eval_def_occurrences shadow_cg_def) >>
  CONV_TAC (LAND_CONV EVAL) >> EVAL_TAC
QED

Theorem shadow_phase_two_cache:
  (shadow_phase 2).ps_stack =
    REVERSE (MAP Var (TAKE 15 (selective_names 17))) ++
      [Var "v15"; Var "v16"; Var "hold"] /\
  (shadow_phase 2).ps_spilled = FEMPTY
Proof
  `2 = SUC (SUC 0)` by decide_tac >> pop_assum SUBST1_TAC >>
  rewrite_tac[shadow_phase_def, shadow_entry_cache] >>
  CONV_TAC (eval_def_occurrences shadow_lv_def) >>
  CONV_TAC (eval_def_occurrences shadow_dg_def) >>
  CONV_TAC (eval_def_occurrences shadow_cg_def) >> EVAL_TAC
QED

(* Actual analyzed first-use order changes the join suffix before this
   instruction can run.  The proposed deep input is shallow AND live-through;
   neither a dead deep reorder nor an optimistic query for v00 is reached. *)
Theorem shadow_site_obstruction:
  stack_get_depth (Var "v15") (shadow_phase 2).ps_stack = SOME 2 /\
  MEM "v15" (live_vars_at shadow_lv "H" 3) /\
  LAST (live_vars_at shadow_lv "H" 3) = "shadow_live" /\
  (EL 2 (EL 1 shadow_fn.fn_blocks).bb_instructions).inst_outputs = ["shadow_live"]
Proof
  rewrite_tac[shadow_phase_two_cache] >>
  CONV_TAC (eval_def_occurrences shadow_lv_def) >> EVAL_TAC
QED

Theorem shadow_site_emit:
  emit_one_input ADD (live_vars_at shadow_lv "H" 3) (Var "v15")
    (shadow_phase 2) = do_dup 2 (shadow_phase 2)
Proof
  mp_tac shadow_site_obstruction >> strip_tac >>
  simp[emit_one_input_def, shadow_phase_two_cache] >>
  Cases_on `do_dup 2 (shadow_phase 2)` >> simp[]
QED

Theorem shadow_site_optimistic_skips:
  !ps. optimistic_swap_plan shadow_dg
    (EL 2 (EL 1 shadow_fn.fn_blocks).bb_instructions)
    (live_vars_at shadow_lv "H" 3) F ps = ([], ps)
Proof
  gen_tac >> rewrite_tac[optimistic_swap_plan_def] >>
  CONV_TAC (eval_def_occurrences shadow_lv_def) >>
  CONV_TAC (eval_def_occurrences shadow_dg_def) >> EVAL_TAC
QED

Theorem shadow_entry_success:
  IS_SOME (generate_block_plan shadow_lv shadow_dg shadow_cg shadow_fn
    (EL 0 shadow_fn.fn_blocks) entry_probe_start)
Proof
  CONV_TAC (eval_def_occurrences shadow_lv_def) >>
  CONV_TAC (eval_def_occurrences shadow_dg_def) >>
  CONV_TAC (eval_def_occurrences shadow_cg_def) >> EVAL_TAC
QED

Theorem shadow_prefix_dispatch_success:
  EVERY (\i.
    IS_SOME (generate_inst_plan shadow_lv shadow_dg shadow_cg shadow_fn
      (EL i (EL 1 shadow_fn.fn_blocks).bb_instructions)
      (live_vars_at shadow_lv "H" (SUC i)) F F "H" (shadow_phase i)) /\
    ~is_terminator
      (EL (SUC i) (EL 1 shadow_fn.fn_blocks).bb_instructions).inst_opcode)
    [0;1]
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``generate_regular_inst_plan``, ``generate_phi_plan``,
     ``shadow_phase``, ``shadow_lv``, ``shadow_dg``, ``shadow_cg``])
QED
