(* Counterexample certificate uses only the frozen introduction rules, never
   lineage_state_block_plan or a theorem depending on it. *)
Theory fnPlanLineageDiamondCertificate
Ancestors
  fnPlanLineage fnPlanLineageDiamondChecks

Theorem diamond_call_E:
  dfs_aux_call diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    ["E"] [] diamond_initial
Proof
  irule dfs_aux_call_entry >> simp[diamond_lookup]
QED

Theorem diamond_call_E_succs:
  dfs_succs_call diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    (SND diamond_entry_result).ps_stack (SND diamond_entry_result).ps_spilled
    ["B";"A"] ["E"] (SND diamond_entry_result)
Proof
  rewrite_tac[GSYM (cj 1 diamond_cfg_edges)] >>
  irule dfs_aux_call_succs >>
  simp[diamond_lookup, SRULE [] diamond_entry_success] >>
  qexistsl_tac [`FST diamond_entry_result`, `diamond_initial`, `[]`] >>
  simp[diamond_call_E, SRULE [] diamond_entry_success, pairTheory.PAIR]
QED

Theorem diamond_call_B:
  dfs_aux_call diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    ["B"] ["E"] (SND diamond_entry_result)
Proof
  assume_tac diamond_call_E_succs >> drule dfs_aux_call_branch >> simp[]
QED

Theorem diamond_call_B_succs:
  dfs_succs_call diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    (SND diamond_B_result).ps_stack (SND diamond_B_result).ps_spilled
    ["J"] ["B";"E"] (SND diamond_B_result)
Proof
  rewrite_tac[GSYM (cj 3 diamond_cfg_edges)] >>
  irule dfs_aux_call_succs >> simp[diamond_lookup] >>
  qexistsl_tac [`FST diamond_B_result`, `SND diamond_entry_result`, `[]`] >>
  simp[diamond_call_B, diamond_B_success, pairTheory.PAIR]
QED

Theorem diamond_call_J:
  dfs_aux_call diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    ["J"] ["B";"E"] (SND diamond_B_result)
Proof
  assume_tac diamond_call_B_succs >> drule dfs_aux_call_branch >> simp[]
QED

Theorem diamond_call_A_succs:
  dfs_succs_call diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    (SND diamond_entry_result).ps_stack (SND diamond_entry_result).ps_spilled
    ["A"] ["J";"B";"E"] diamond_A_input
Proof
  assume_tac diamond_call_E_succs >>
  drule dfs_aux_call_sibling >>
  simp[diamond_dfs_B, diamond_sibling_states]
QED

Theorem diamond_call_A:
  dfs_aux_call diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    ["A"] ["J";"B";"E"] diamond_A_input
Proof
  assume_tac diamond_call_A_succs >> drule dfs_aux_call_branch >>
  simp[diamond_sibling_states]
QED

Theorem diamond_dfs_states:
  dfs_block_state diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    "E" diamond_initial /\
  dfs_block_state diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    "A" diamond_A_input /\
  dfs_block_state diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    "J" (SND diamond_B_result)
Proof
  simp[dfs_block_state_def] >> rpt conj_tac
  >- (qexistsl_tac [`[]`,`[]`] >> simp[diamond_call_E])
  >- (qexistsl_tac [`[]`,`["J";"B";"E"]`] >> simp[diamond_call_A])
  >> qexistsl_tac [`[]`,`["B";"E"]`] >> simp[diamond_call_J]
QED

Theorem diamond_lineage_A:
  lineage_state diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    "A" diamond_A_input
Proof
  `lineage_state diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    "E" diamond_initial` by (irule lineage_state_entry >> simp[diamond_lookup]) >>
  once_rewrite_tac[GSYM (cj 3 diamond_sibling_states)] >>
  irule lineage_state_step >>
  simp[diamond_dfs_states] >>
  `diamond_initial with <|ps_cleanup_height := NONE;
     ps_cleanup_promised := F|> = diamond_initial` by EVAL_TAC >>
  qexistsl_tac [`EL 0 diamond_fn.fn_blocks`, `FST diamond_entry_result`,
    `NONE`, `"E"`, `F`, `diamond_initial`, `diamond_initial`,
    `SND diamond_entry_result`] >>
  simp[diamond_lookup, SRULE [] diamond_entry_success, diamond_cfg_edges,
       diamond_dfs_states, pairTheory.PAIR]
QED

Theorem diamond_lineage_J:
  lineage_state diamond_live diamond_dfg diamond_cfg diamond_fn diamond_initial
    "J" diamond_candidate_J
Proof
  rewrite_tac[diamond_candidate_J_def] >> irule lineage_state_step >>
  simp[diamond_dfs_states] >>
  qexistsl_tac [`EL 1 diamond_fn.fn_blocks`,
    `[SOLabel "A"] ++ diamond_A_first_ops ++ diamond_A_jump_ops`,
    `NONE`, `"A"`, `F`, `diamond_A_input`, `diamond_A_input`, `diamond_A_after`] >>
  `diamond_A_input with <|ps_cleanup_height := NONE;
    ps_cleanup_promised := F|> = diamond_A_input` by EVAL_TAC >>
  simp[diamond_lookup, diamond_A_success, diamond_cfg_edges,
       diamond_dfs_states, diamond_lineage_A]
QED

Theorem diamond_frozen_counterexample:
  diamond_live = liveness_analyze diamond_fn /\
  diamond_dfg = dfg_build_function diamond_fn /\
  diamond_cfg = cfg_analyze diamond_fn /\
  codegen_ready_fn diamond_fn /\
  generate_fn_plan_with_cleanup_analyzed diamond_live diamond_dfg diamond_cfg
    NONE [] diamond_fn 0 0 = SOME (diamond_fn_ops,diamond_final) /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) diamond_fn.fn_blocks /\
  lookup_block "J" diamond_fn.fn_blocks = SOME (EL 3 diamond_fn.fn_blocks) /\
  lineage_state diamond_live diamond_dfg diamond_cfg diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "J" diamond_candidate_J /\
  dfs_block_state diamond_live diamond_dfg diamond_cfg diamond_fn
    (init_cleanup_plan_state NONE [] 0 0) "J" (SND diamond_B_result) /\
  generate_block_plan diamond_live diamond_dfg diamond_cfg diamond_fn
    (EL 3 diamond_fn.fn_blocks) (SND diamond_B_result) = SOME diamond_J_result /\
  ~(?h promised after.
    generate_block_plan diamond_live diamond_dfg diamond_cfg diamond_fn
      (EL 3 diamond_fn.fn_blocks)
      (diamond_candidate_J with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (FST diamond_J_result,after) /\
    after.ps_alloc = (SND diamond_J_result).ps_alloc)
Proof
  simp[GSYM diamond_initial_def, GSYM diamond_live_def, GSYM diamond_dfg_def,
       GSYM diamond_cfg_def, diamond_static_ready, diamond_whole_success, diamond_no_marker,
       diamond_lookup, diamond_lineage_J, diamond_dfs_states, diamond_J_success] >>
  metis_tac[diamond_J_no_cleanup_replay]
QED

(* Dependency audit: the proof above names only frozen introduction rules,
   definitions and checked diamond computation lemmas. The generated .dat
   certificate records DISK_THM only (no cheat oracle). *)
