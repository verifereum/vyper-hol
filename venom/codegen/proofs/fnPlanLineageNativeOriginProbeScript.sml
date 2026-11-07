Theory fnPlanLineageNativeOriginProbe
Ancestors fnPlanLineage fnPlanLineageEntryProbe stackPlanGen stackPlanTypes
  stackPlanOps stackModel livenessDefs cfgDefs venomInst finite_map
Libs wordsLib

val _ = computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY];

(* Native finite-call certificates. No arbitrary stack mutations. *)
Theorem native_origin_first_branch[local]:
  dfs_aux_call lv dg cg fn ps0 [lbl] visited ps /\
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dg cg fn bb ps = SOME (ops,after) /\
  cfg_succs_of cg lbl = next::rest ==>
  dfs_aux_call lv dg cg fn ps0 [next] (lbl::visited) after
Proof
  rpt strip_tac >> drule_all dfs_aux_call_succs >>
  simp[] >> disch_then (mp_tac o MATCH_MP dfs_aux_call_branch) >> simp[]
QED

Definition native_loop_lv_def:
  native_loop_lv = liveness_analyze residual_loop_fn
End
Definition native_loop_dg_def:
  native_loop_dg = dfg_build_function residual_loop_fn
End
Definition native_loop_cg_def:
  native_loop_cg = cfg_analyze residual_loop_fn
End
Definition native_loop_run_def:
  native_loop_run n ps = generate_block_plan native_loop_lv native_loop_dg
    native_loop_cg residual_loop_fn (EL n residual_loop_fn.fn_blocks) ps
End
Definition native_loop_entry_def:
  native_loop_entry = residual_step residual_loop_fn 0 entry_probe_start
End

Theorem native_loop_entry_success:
  IS_SOME (native_loop_run 0 entry_probe_start)
Proof
  EVAL_TAC
QED

Theorem native_loop_entry_call:
  dfs_aux_call native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start ["entry"] [] entry_probe_start
Proof
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem native_loop_header_call:
  dfs_aux_call native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start ["H"] ["entry"] native_loop_entry
Proof
  irule native_origin_first_branch >>
  conj_tac >- simp[] >> conj_tac >- (qexists_tac `[]` >> EVAL_TAC) >>
  qexistsl_tac [`EL 0 residual_loop_fn.fn_blocks`,
    `FST (THE (native_loop_run 0 entry_probe_start))`, `entry_probe_start`] >>
  simp[native_loop_entry_call] >> EVAL_TAC
QED

Definition native_loop_header_after_def:
  native_loop_header_after = SND (THE (native_loop_run 1 native_loop_entry))
End

Theorem native_loop_header_success:
  IS_SOME (native_loop_run 1 native_loop_entry)
Proof
  EVAL_TAC
QED

Theorem native_loop_header_succs:
  dfs_succs_call native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start native_loop_header_after.ps_stack native_loop_header_after.ps_spilled
    ["exit";"back"] ["H";"entry"] native_loop_header_after
Proof
  `["exit";"back"] = cfg_succs_of native_loop_cg "H"` by EVAL_TAC >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_succs >>
  conj_tac >- simp[] >>
  qexistsl_tac [`EL 1 residual_loop_fn.fn_blocks`,
    `FST (THE (native_loop_run 1 native_loop_entry))`, `native_loop_entry`, `[]`] >>
  simp[native_loop_header_call] >> EVAL_TAC
QED

Theorem native_loop_back_succs:
  dfs_succs_call native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start native_loop_header_after.ps_stack native_loop_header_after.ps_spilled
    ["back"] ["exit";"H";"entry"] native_loop_header_after
Proof
  assume_tac native_loop_header_succs >>
  drule dfs_aux_call_sibling >>
  disch_then (qspecl_then
    [`SND (THE (native_loop_run 3 native_loop_header_after))`,
     `FST (THE (native_loop_run 3 native_loop_header_after))`,
     `["exit";"H";"entry"]`] mp_tac) >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >> simp[] >>
  CONV_TAC (BINOP_CONV (RAND_CONV EVAL)) >> simp[]
QED

Theorem native_loop_back_call:
  dfs_aux_call native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start ["back"] ["exit";"H";"entry"] native_loop_header_after
Proof
  mp_tac native_loop_back_succs >>
  disch_then (mp_tac o MATCH_MP dfs_aux_call_branch) >> simp[]
QED

Theorem native_loop_dfs_states:
  dfs_block_state native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start "entry" entry_probe_start /\
  dfs_block_state native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start "H" native_loop_entry /\
  dfs_block_state native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start "back" native_loop_header_after
Proof
  simp[dfs_block_state_def] >> rpt conj_tac
  >- (qexistsl_tac [`[]`,`[]`] >> simp[native_loop_entry_call])
  >- (qexistsl_tac [`[]`,`["entry"]`] >> simp[native_loop_header_call]) >>
  qexistsl_tac [`[]`,`["exit";"H";"entry"]`] >> simp[native_loop_back_call]
QED

Theorem native_loop_entry_lineage:
  lineage_state native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start "entry" entry_probe_start
Proof
  irule lineage_state_entry >> EVAL_TAC
QED

Theorem native_loop_header_lineage:
  lineage_state native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start "H" native_loop_entry
Proof
  `native_loop_entry = native_loop_entry with
    <|ps_stack := native_loop_entry.ps_stack; ps_spilled := native_loop_entry.ps_spilled|>`
    by simp[] >> pop_assum SUBST1_TAC >>
  irule lineage_state_step >>
  conj_tac >- simp[native_loop_dfs_states] >>
  qexistsl_tac [`EL 0 residual_loop_fn.fn_blocks`,
    `FST (THE (native_loop_run 0 entry_probe_start))`, `NONE`, `"entry"`, `F`,
    `entry_probe_start`, `entry_probe_start`, `native_loop_entry`] >>
  simp[native_loop_entry_lineage, native_loop_dfs_states] >> EVAL_TAC
QED

Theorem native_loop_back_success:
  IS_SOME (native_loop_run 2 native_loop_header_after)
Proof
  EVAL_TAC
QED

Definition native_loop_back_after_def:
  native_loop_back_after = SND (THE (native_loop_run 2 native_loop_header_after))
End
Definition native_loop_reentry_def:
  native_loop_reentry = native_loop_entry with
    <|ps_stack := native_loop_back_after.ps_stack;
      ps_spilled := native_loop_back_after.ps_spilled|>
End

Theorem native_loop_back_lineage:
  lineage_state native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start "back" native_loop_header_after
Proof
  `native_loop_header_after = native_loop_header_after with
    <|ps_stack := native_loop_header_after.ps_stack;
      ps_spilled := native_loop_header_after.ps_spilled|>` by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >>
  conj_tac >- simp[native_loop_dfs_states] >>
  qexistsl_tac [`EL 1 residual_loop_fn.fn_blocks`,
    `FST (THE (native_loop_run 1 native_loop_entry))`, `NONE`, `"H"`, `F`,
    `native_loop_entry`, `native_loop_entry`, `native_loop_header_after`] >>
  simp[native_loop_header_lineage, native_loop_dfs_states] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem native_loop_reentry_lineage:
  lineage_state native_loop_lv native_loop_dg native_loop_cg residual_loop_fn
    entry_probe_start "H" native_loop_reentry
Proof
  rewrite_tac[native_loop_reentry_def] >> irule lineage_state_step >>
  conj_tac >- simp[native_loop_dfs_states] >>
  qexistsl_tac [`EL 2 residual_loop_fn.fn_blocks`,
    `FST (THE (native_loop_run 2 native_loop_header_after))`, `NONE`, `"back"`, `F`,
    `native_loop_header_after`, `native_loop_header_after`, `native_loop_back_after`] >>
  simp[native_loop_back_lineage, native_loop_dfs_states] >>
  conj_tac >- EVAL_TAC >>
  `native_loop_header_after with
     <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
   native_loop_header_after` by EVAL_TAC >>
  simp[GSYM native_loop_run_def] >>
  conj_tac
  >- (mp_tac native_loop_back_success >>
      Cases_on `native_loop_run 2 native_loop_header_after` >>
      simp[native_loop_back_after_def]) >>
  EVAL_TAC
QED

Theorem native_loop_reentry_cache:
  native_loop_reentry = entry_probe_start with ps_stack := [Var "t";Var "n"]
Proof
  EVAL_TAC
QED

Theorem native_loop_reentry_replay:
  IS_SOME (native_loop_run 1 native_loop_reentry) /\
  FST (THE (native_loop_run 1 native_loop_reentry)) =
    FST (THE (native_loop_run 1 native_loop_entry)) /\
  (SND (THE (native_loop_run 1 native_loop_reentry))).ps_alloc =
    (SND (THE (native_loop_run 1 native_loop_entry))).ps_alloc /\
  native_loop_reentry.ps_alloc = native_loop_entry.ps_alloc /\
  native_loop_reentry.ps_spilled = native_loop_entry.ps_spilled /\
  native_loop_entry.ps_stack = [Var "t";Var "a"] /\
  native_loop_reentry.ps_stack = [Var "t";Var "n"]
Proof
  pure_rewrite_tac[native_loop_reentry_cache] >>
  rpt conj_tac >> EVAL_TAC
QED

Definition native_pressure_lv_def:
  native_pressure_lv = liveness_analyze residual_pressure_fn
End
Definition native_pressure_dg_def:
  native_pressure_dg = dfg_build_function residual_pressure_fn
End
Definition native_pressure_cg_def:
  native_pressure_cg = cfg_analyze residual_pressure_fn
End
Definition native_pressure_run_def:
  native_pressure_run n ps = generate_block_plan native_pressure_lv native_pressure_dg
    native_pressure_cg residual_pressure_fn (EL n residual_pressure_fn.fn_blocks) ps
End

Theorem native_pressure_entry_call:
  dfs_aux_call native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start ["entry"] [] entry_probe_start
Proof
  irule dfs_aux_call_entry >> EVAL_TAC
QED

Theorem native_pressure_right_call:
  dfs_aux_call native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start ["R"] ["entry"] residual_pressure_entry
Proof
  irule native_origin_first_branch >> conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `["L"]` >> EVAL_TAC) >>
  strip_assume_tac residual_pressure_entry_result >>
  qexistsl_tac [`EL 0 residual_pressure_fn.fn_blocks`, `ops`, `entry_probe_start`] >>
  gvs[native_pressure_entry_call, native_pressure_lv_def, listTheory.EL,
       native_pressure_dg_def, native_pressure_cg_def] >> EVAL_TAC
QED

Theorem native_pressure_join_call:
  dfs_aux_call native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start ["J"] ["R";"entry"] (residual_pressure_incoming 2)
Proof
  irule native_origin_first_branch >> conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `[]` >> EVAL_TAC) >>
  qspec_then `2` mp_tac residual_pressure_sides_result >> simp[] >> strip_tac >>
  qexistsl_tac [`EL 2 residual_pressure_fn.fn_blocks`, `ops`, `residual_pressure_entry`] >>
  simp[native_pressure_right_call, native_pressure_lv_def,
       native_pressure_dg_def, native_pressure_cg_def] >> EVAL_TAC
QED

Theorem native_pressure_entry_succs:
  dfs_succs_call native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start residual_pressure_entry.ps_stack residual_pressure_entry.ps_spilled
    ["R";"L"] ["entry"] residual_pressure_entry
Proof
  `["R";"L"] = cfg_succs_of native_pressure_cg "entry"` by EVAL_TAC >>
  pop_assum SUBST1_TAC >> irule dfs_aux_call_succs >> conj_tac >- simp[] >>
  strip_assume_tac residual_pressure_entry_result >>
  qexistsl_tac [`EL 0 residual_pressure_fn.fn_blocks`, `ops`, `entry_probe_start`, `[]`] >>
  gvs[native_pressure_entry_call, native_pressure_lv_def, listTheory.EL,
       native_pressure_dg_def, native_pressure_cg_def] >> EVAL_TAC
QED

Definition native_pressure_right_result_def:
  native_pressure_right_result = THE (generate_fn_plan_aux native_pressure_lv
    native_pressure_dg native_pressure_cg residual_pressure_fn ["R"] ["entry"]
    residual_pressure_entry)
End

Theorem native_pressure_right_success:
  IS_SOME (generate_fn_plan_aux native_pressure_lv native_pressure_dg native_pressure_cg
    residual_pressure_fn ["R"] ["entry"] residual_pressure_entry)
Proof
  pure_rewrite_tac[native_pressure_lv_def, residual_pressure_liveness_cache] >>
  CONV_TAC (PAT_CONV ``IS_SOME (generate_fn_plan_aux lv dg cg fn wl vis ps)`` EVAL) >>
  EVAL_TAC
QED

Theorem native_pressure_right_result_some:
  generate_fn_plan_aux native_pressure_lv native_pressure_dg native_pressure_cg
    residual_pressure_fn ["R"] ["entry"] residual_pressure_entry =
    SOME native_pressure_right_result
Proof
  mp_tac native_pressure_right_success >>
  Cases_on `generate_fn_plan_aux native_pressure_lv native_pressure_dg native_pressure_cg
    residual_pressure_fn ["R"] ["entry"] residual_pressure_entry` >>
  simp[native_pressure_right_result_def]
QED

Theorem native_pressure_join_result:
  ?ops. native_pressure_run 3 (residual_pressure_incoming 2) =
    SOME (ops, residual_pressure_incoming 2 with ps_stack := [])
Proof
  pure_rewrite_tac[native_pressure_run_def, native_pressure_lv_def,
    residual_pressure_liveness_cache] >>
  CONV_TAC (PAT_CONV ``?ops. generate_block_plan lv dg cg fn bb ps = SOME (ops,result)`` EVAL) >>
  EVAL_TAC >> simp[] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qmatch_goalsub_abbrev_tac `ops = _` >> qexists_tac `ops` >> simp[]
QED

Theorem native_pressure_exit_result:
  ?ops. native_pressure_run 4 (residual_pressure_incoming 2 with ps_stack := []) =
    SOME (ops, residual_pressure_incoming 2 with ps_stack := [])
Proof
  pure_rewrite_tac[native_pressure_run_def, native_pressure_lv_def,
    residual_pressure_liveness_cache] >>
  CONV_TAC (PAT_CONV ``?ops. generate_block_plan lv dg cg fn bb ps = SOME (ops,result)`` EVAL) >>
  EVAL_TAC >> simp[] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qmatch_goalsub_abbrev_tac `ops = _` >> qexists_tac `ops` >> simp[]
QED

Theorem native_pressure_right_result_fields:
  FST (SND native_pressure_right_result) = ["exit";"J";"R";"entry"] /\
  (SND (SND native_pressure_right_result)).ps_alloc.sa_next_offset = 576 /\
  (SND (SND native_pressure_right_result)).ps_alloc.sa_spill_base = 0 /\
  (SND (SND native_pressure_right_result)).ps_label_counter = 0
Proof
  qspec_then `2` mp_tac residual_pressure_sides_result >> simp[] >>
  disch_then (qx_choose_then `rops` assume_tac) >>
  qx_choose_then `jops` assume_tac native_pressure_join_result >>
  qx_choose_then `eops` assume_tac native_pressure_exit_result >>
  gvs[GSYM native_pressure_lv_def, GSYM native_pressure_dg_def,
      GSYM native_pressure_cg_def, native_pressure_run_def] >>
  qpat_x_assum `SOME (rops,_) = _` (assume_tac o SYM) >>
  qpat_x_assum `SOME (jops,_) = _` (assume_tac o SYM) >>
  qpat_x_assum `SOME (eops,_) = _` (assume_tac o SYM) >>
  `lookup_block "R" residual_pressure_fn.fn_blocks = SOME (EL 2 residual_pressure_fn.fn_blocks) /\
   lookup_block "J" residual_pressure_fn.fn_blocks = SOME (EL 3 residual_pressure_fn.fn_blocks) /\
   lookup_block "exit" residual_pressure_fn.fn_blocks = SOME (EL 4 residual_pressure_fn.fn_blocks) /\
   cfg_succs_of native_pressure_cg "R" = ["J"] /\
   cfg_succs_of native_pressure_cg "J" = ["exit"] /\
   cfg_succs_of native_pressure_cg "exit" = []` by (rpt conj_tac >> EVAL_TAC) >>
  simp[native_pressure_right_result_def, generate_fn_plan_aux_def] >>
  simp[residual_pressure_incoming_def]
QED

Definition native_pressure_left_start_def:
  native_pressure_left_start = residual_pressure_entry with ps_alloc :=
    residual_pressure_entry.ps_alloc with sa_next_offset := 576
End

Theorem native_pressure_left_succs:
  dfs_succs_call native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start residual_pressure_entry.ps_stack residual_pressure_entry.ps_spilled
    ["L"] ["exit";"J";"R";"entry"] native_pressure_left_start
Proof
  assume_tac native_pressure_entry_succs >> drule dfs_aux_call_sibling >>
  disch_then (qspecl_then [`SND (SND native_pressure_right_result)`,
    `FST native_pressure_right_result`, `FST (SND native_pressure_right_result)`] mp_tac) >>
  simp[native_pressure_right_result_some] >>
  strip_assume_tac native_pressure_right_result_fields >>
  `(SND (SND native_pressure_right_result)).ps_alloc with sa_free_slots := [] =
     <|sa_free_slots := []; sa_next_offset := 576; sa_spill_base := 0|>`
    by simp[spill_alloc_component_equality] >>
  gvs[native_pressure_left_start_def, residual_pressure_entry_def]
QED

Theorem native_pressure_left_call:
  dfs_aux_call native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start ["L"] ["exit";"J";"R";"entry"] native_pressure_left_start
Proof
  mp_tac native_pressure_left_succs >>
  disch_then (mp_tac o MATCH_MP dfs_aux_call_branch) >>
  simp[native_pressure_left_start_def, residual_pressure_entry_def]
QED

Definition native_pressure_left_after_def:
  native_pressure_left_after = residual_pressure_incoming 1 with ps_alloc :=
    <|sa_free_slots := GENLIST (\n. 576 + 32*n) 18;
      sa_next_offset := 1152; sa_spill_base := 0|>
End

Theorem native_pressure_left_result:
  ?ops. native_pressure_run 1 native_pressure_left_start =
    SOME (ops,native_pressure_left_after)
Proof
  pure_rewrite_tac[native_pressure_run_def, native_pressure_lv_def,
    residual_pressure_liveness_cache] >>
  CONV_TAC (PAT_CONV ``?ops. generate_block_plan lv dg cg fn bb ps = SOME (ops,result)`` EVAL) >>
  EVAL_TAC >> simp[] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  qmatch_goalsub_abbrev_tac `ops = _` >> qexists_tac `ops` >> simp[]
QED

Theorem native_pressure_exit_call:
  dfs_aux_call native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start ["exit"] ["J";"R";"entry"]
    (residual_pressure_incoming 2 with ps_stack := [])
Proof
  irule native_origin_first_branch >> conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `[]` >> EVAL_TAC) >>
  qx_choose_then `ops` assume_tac native_pressure_join_result >>
  qexistsl_tac [`EL 3 residual_pressure_fn.fn_blocks`, `ops`, `residual_pressure_incoming 2`] >>
  fs[native_pressure_run_def, native_pressure_join_call] >> EVAL_TAC
QED

Theorem native_pressure_dfs_states:
  dfs_block_state native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start "entry" entry_probe_start /\
  dfs_block_state native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start "L" native_pressure_left_start /\
  dfs_block_state native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start "J" (residual_pressure_incoming 2) /\
  dfs_block_state native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start "exit" (residual_pressure_incoming 2 with ps_stack := [])
Proof
  simp[dfs_block_state_def] >> rpt conj_tac
  >- (qexistsl_tac [`[]`,`[]`] >> simp[native_pressure_entry_call])
  >- (qexistsl_tac [`[]`,`["exit";"J";"R";"entry"]`] >> simp[native_pressure_left_call])
  >- (qexistsl_tac [`[]`,`["R";"entry"]`] >> simp[native_pressure_join_call]) >>
  qexistsl_tac [`[]`,`["J";"R";"entry"]`] >> simp[native_pressure_exit_call]
QED

Theorem native_pressure_entry_lineage:
  lineage_state native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start "entry" entry_probe_start
Proof
  irule lineage_state_entry >> EVAL_TAC
QED

Theorem native_pressure_left_lineage:
  lineage_state native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start "L" native_pressure_left_start
Proof
  `native_pressure_left_start = native_pressure_left_start with
    <|ps_stack := residual_pressure_entry.ps_stack;
      ps_spilled := residual_pressure_entry.ps_spilled|>`
    by simp[native_pressure_left_start_def, residual_pressure_entry_def] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >>
  conj_tac >- simp[native_pressure_dfs_states] >>
  qx_choose_then `ops` assume_tac residual_pressure_entry_result >>
  qexistsl_tac [`EL 0 residual_pressure_fn.fn_blocks`, `ops`, `NONE`, `"entry"`, `F`,
    `entry_probe_start`, `entry_probe_start`, `residual_pressure_entry`] >>
  gvs[native_pressure_dfs_states, native_pressure_entry_lineage, native_pressure_lv_def,
    native_pressure_dg_def, native_pressure_cg_def, listTheory.EL] >>
  conj_tac >- (CONV_TAC (BINOP_CONV EVAL) >> simp[]) >>
  conj_tac
  >- (`entry_probe_start with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
       entry_probe_start` by EVAL_TAC >> simp[]) >>
  EVAL_TAC
QED

Definition native_pressure_alt_join_def:
  native_pressure_alt_join = residual_pressure_incoming 2 with
    <|ps_stack := native_pressure_left_after.ps_stack;
      ps_spilled := native_pressure_left_after.ps_spilled|>
End

Theorem native_pressure_alt_join_cache:
  native_pressure_alt_join = residual_pressure_incoming 1
Proof
  EVAL_TAC
QED

Theorem native_pressure_alt_join_lineage:
  lineage_state native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start "J" native_pressure_alt_join
Proof
  rewrite_tac[native_pressure_alt_join_def] >> irule lineage_state_step >>
  conj_tac >- simp[native_pressure_dfs_states] >>
  qx_choose_then `ops` assume_tac native_pressure_left_result >>
  `native_pressure_left_start with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    native_pressure_left_start` by EVAL_TAC >>
  qexistsl_tac [`EL 1 residual_pressure_fn.fn_blocks`, `ops`, `NONE`, `"L"`, `F`,
    `native_pressure_left_start`, `native_pressure_left_start`, `native_pressure_left_after`] >>
  gvs[native_pressure_run_def, native_pressure_dfs_states, native_pressure_left_lineage] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem native_pressure_alt_join_replay:
  native_pressure_run 3 native_pressure_alt_join =
    native_pressure_run 3 (residual_pressure_incoming 2)
Proof
  pure_rewrite_tac[native_pressure_alt_join_cache, native_pressure_run_def,
    native_pressure_lv_def, residual_pressure_liveness_cache] >>
  CONV_TAC (BINOP_CONV (PAT_CONV ``generate_block_plan lv dg cg fn bb ps`` EVAL)) >>
  CONV_TAC (LAND_CONV EVAL) >> EVAL_TAC
QED

Theorem native_pressure_alt_join_success:
  IS_SOME (native_pressure_run 3 native_pressure_alt_join)
Proof
  rewrite_tac[native_pressure_alt_join_replay, native_pressure_run_def,
    native_pressure_lv_def, native_pressure_dg_def, native_pressure_cg_def] >>
  irule residual_pressure_join_success >> simp[]
QED

Definition native_pressure_dfs_exit_def:
  native_pressure_dfs_exit = residual_pressure_incoming 2 with ps_stack := []
End
Definition native_pressure_alt_exit_def:
  native_pressure_alt_exit = native_pressure_dfs_exit with
    <|ps_stack := native_pressure_dfs_exit.ps_stack;
      ps_spilled := native_pressure_dfs_exit.ps_spilled|>
End

Theorem native_pressure_alt_exit_lineage:
  lineage_state native_pressure_lv native_pressure_dg native_pressure_cg residual_pressure_fn
    entry_probe_start "exit" native_pressure_alt_exit
Proof
  rewrite_tac[native_pressure_alt_exit_def] >> irule lineage_state_step >>
  conj_tac >- simp[native_pressure_dfs_exit_def, native_pressure_dfs_states] >>
  qx_choose_then `ops` assume_tac native_pressure_join_result >>
  assume_tac native_pressure_alt_join_replay >>
  `native_pressure_alt_join with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|> =
    native_pressure_alt_join` by (rewrite_tac[native_pressure_alt_join_cache] >> EVAL_TAC) >>
  qexistsl_tac [`EL 3 residual_pressure_fn.fn_blocks`, `ops`, `NONE`, `"J"`, `F`,
    `native_pressure_alt_join`, `residual_pressure_incoming 2`,
    `native_pressure_dfs_exit`] >>
  gvs[native_pressure_dfs_exit_def, native_pressure_run_def,
      native_pressure_dfs_states, native_pressure_alt_join_lineage] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem native_origin_boundary_observations:
  native_pressure_alt_join.ps_alloc = (residual_pressure_incoming 2).ps_alloc /\
  native_pressure_alt_join.ps_spilled = (residual_pressure_incoming 2).ps_spilled /\
  native_pressure_left_after.ps_alloc.sa_next_offset = 1152 /\
  native_pressure_alt_join.ps_alloc.sa_next_offset = 576 /\
  (residual_phi residual_pressure_fn 3 native_pressure_alt_join).ps_stack =
    residual_pressure_post_phi.ps_stack /\
  (residual_phi residual_loop_fn 1 native_loop_reentry).ps_stack = [Var "t";Var "x"] /\
  (residual_phi residual_loop_fn 1 native_loop_reentry).ps_spilled = FEMPTY
Proof
  pure_rewrite_tac[native_pressure_alt_join_cache, native_loop_reentry_cache] >>
  rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- (qspec_then `1` mp_tac residual_pressure_phi_boundary >> simp[]) >>
  EVAL_TAC
QED

(* Native provenance findings:
   - CFG successor order is reversed here: R precedes L, exit precedes back.
   - The pressure sibling's allocator starts at 576 and ends at 1152; entering
     J replaces that metadata with the DFS J allocator (high-water mark 576).
     It is not legitimate to compare sequential residual_step states as if
     their allocator were the actual lineage allocator.
   - Both pressure predecessors restore all targets: J spill maps are empty.
     After PHI both stacks have the SAME complete core, not just common support.
     The checked complete block equality includes every subsequent pop/swap and
     the successful JMP guard. The successor exit state is identical to DFS.
   - First loop reentry differs only in the PHI selected input a versus n;
     after PHI the common core is [t;x]. Complete header replay and alloc
     equality are checked, but neither fixture produces a surviving old prefix
     or a nonempty spill domain at these boundaries.
   Remaining universal producers: shared metadata after exact field replacement
   still needs shared SPILLS; native PHI must produce common query support;
   each prepare/output/pop phase must preserve support for LAST next_liveness
   and capacity for destructive footprints. These finite certificates do not
   establish any of those universal assertions or a frozen-theorem falsehood.
*)

Theorem native_loop_header_output_replay:
  native_loop_run 1 native_loop_reentry = native_loop_run 1 native_loop_entry
Proof
  pure_rewrite_tac[native_loop_reentry_cache] >>
  CONV_TAC (LAND_CONV EVAL) >> EVAL_TAC
QED

Theorem native_pressure_exit_replay:
  native_pressure_alt_exit = native_pressure_dfs_exit /\
  IS_SOME (native_pressure_run 4 native_pressure_alt_exit)
Proof
  simp[native_pressure_alt_exit_def] >>
  qx_choose_then `ops` mp_tac native_pressure_exit_result >>
  simp[native_pressure_dfs_exit_def] >> metis_tac[optionTheory.IS_SOME_DEF]
QED
