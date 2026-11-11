(*
 * DFS coverage of the function planner, for the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation.
 *
 * The induction step at a jump needs, for the target block, the premises
 * dfs_block_state (the state the planner planned it from) and the
 * successful generate_block_plan from that state, and the target's code
 * inside the function's plan.  The function planner is a DFS over
 * cfg_succs_of from the entry label, so every block reachable in the CFG
 * is planned.
 *
 * TOP-LEVEL:
 *   dfs_block_state_reachable — every reachable block is planned
 *                               and its code is a slice of the plan
 *)

Theory fnPlanCover
Ancestors
  fnPlanLineage stackPlanGen stackPlanTypes venomWf cfgAnalysisProps
  dfAnalyzeProofs

Theorem ready_fn_cfg_edge:
  codegen_ready_fn fn /\ fn_cfg_edge fn a b ==>
  ?bb. lookup_block a fn.fn_blocks = SOME bb /\
       MEM b (cfg_succs_of (cfg_analyze fn) a)
Proof
  rpt strip_tac >>
  gvs[codegen_ready_fn_def, wf_function_def, fn_cfg_edge_def] >>
  `MEM bb.bb_label (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  drule dfAnalyzeProofsTheory.lookup_block_exists >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs]
QED

Theorem cleanup_plan_entry_call:
  fn_entry_label fn = SOME entry /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    spill_base lbl_ctr = SOME (ops, ps_end) ==>
  ?visited.
    generate_fn_plan_aux liveness dfg cfg fn [entry] []
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
      SOME (ops, visited, ps_end)
Proof
  simp[generate_fn_plan_with_cleanup_analyzed_def] >>
  Cases_on `canonical_param_prefix fn` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem traversal_dfs_witness:
  (!liveness dfg cfg fn wl visited ps ops final ps'.
    generate_fn_plan_aux liveness dfg cfg fn wl visited ps =
      SOME (ops, final, ps') ==>
    !ps0 lbl bb.
    dfs_aux_call liveness dfg cfg fn ps0 wl visited ps /\
    MEM lbl final /\ ~MEM lbl visited /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    ?ps_dfs block_ops ps_after pre post.
      dfs_block_state liveness dfg cfg fn ps0 lbl ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb ps_dfs =
        SOME (block_ops, ps_after) /\ ops = pre ++ block_ops ++ post) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops final ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, final, ps') ==>
    !ps0 lbl bb.
    dfs_succs_call liveness dfg cfg fn ps0 ss sp succs visited ps /\
    MEM lbl final /\ ~MEM lbl visited /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    ?ps_dfs block_ops ps_after pre post.
      dfs_block_state liveness dfg cfg fn ps0 lbl ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb ps_dfs =
        SOME (block_ops, ps_after) /\ ops = pre ++ block_ops ++ post)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (simp[Once generate_fn_plan_aux_def] >> metis_tac[])
  >- suspend "aux"
  >- (simp[Once generate_fn_plan_aux_def] >> metis_tac[])
  >> suspend "succ"
QED

Resume traversal_dfs_witness[aux]:
  rpt gen_tac >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  Cases_on `MEM lbl visited`
  >- (gvs[] >> simp[NoAsms, Once generate_fn_plan_aux_def] >>
      asm_rewrite_tac[] >> rpt strip_tac >>
      `dfs_aux_call liveness dfg cfg fn ps0 wl visited ps` by
        metis_tac[dfs_aux_call_visited] >> metis_tac[]) >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- (gvs[] >> simp[NoAsms, Once generate_fn_plan_aux_def] >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `(case NONE of _ => _ | _ => _) = _`
        (mp_tac o SIMP_RULE (srw_ss()) []) >>
      disch_tac >> rpt strip_tac >>
      `lbl' <> lbl` by (strip_tac >> gvs[]) >>
      `dfs_aux_call liveness dfg cfg fn ps0 wl (lbl::visited) ps` by
        metis_tac[dfs_aux_call_missing] >> metis_tac[]) >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  Cases_on `generate_block_plan liveness dfg cfg fn bb ps`
  >- (simp[NoAsms, Once generate_fn_plan_aux_def] >> asm_rewrite_tac[] >> simp[]) >>
  rename1 `generate_block_plan _ _ _ _ _ _ = SOME bp` >>
  PairCases_on `bp` >>
  Cases_on `generate_succs_plan liveness dfg cfg fn bp1.ps_stack
    bp1.ps_spilled (cfg_succs_of cfg lbl) (lbl::visited) bp1`
  >- (simp[NoAsms, Once generate_fn_plan_aux_def] >> asm_rewrite_tac[] >> simp[]) >>
  rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME sr` >>
  PairCases_on `sr` >>
  Cases_on `generate_fn_plan_aux liveness dfg cfg fn wl sr1 sr2`
  >- (simp[NoAsms, Once generate_fn_plan_aux_def] >> asm_rewrite_tac[] >> simp[]) >>
  rename1 `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME rr` >>
  PairCases_on `rr` >>
  simp[NoAsms, Once generate_fn_plan_aux_def] >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `(case SOME bb of _ => _ | _ => _) = _` mp_tac >>
  asm_rewrite_tac[] >> simp[] >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  qpat_assum `generate_block_plan _ _ _ _ _ _ = SOME _` (fn bp =>
    qpat_assum `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME _` (fn sr =>
      rule_assum_tac (SIMP_RULE (srw_ss()) [bp,sr]) >>
      assume_tac bp >> assume_tac sr)) >>
  qpat_assum `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME _` (fn rr =>
    rule_assum_tac (SIMP_RULE (srw_ss()) [rr]) >> assume_tac rr) >>
  qpat_x_assum `MEM lbl visited ==> _` kall_tac >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  Cases_on `lbl' = lbl`
  >- (gvs[] >> qexistsl_tac [`ps`, `bp0`, `bp1`, `[]`, `sr0 ++ rr0`] >>
      simp[dfs_block_state_def] >> metis_tac[]) >>
  `dfs_succs_call liveness dfg cfg fn ps0 bp1.ps_stack bp1.ps_spilled
    (cfg_succs_of cfg lbl) (lbl::visited) bp1` by
    metis_tac[dfs_aux_call_succs] >>
  `dfs_aux_call liveness dfg cfg fn ps0 wl sr1 sr2` by
    metis_tac[dfs_aux_call_rest] >>
  Cases_on `MEM lbl' sr1`
  >- (qpat_x_assum `!ps0 lbl' bb'. _` drule_all >>
      strip_tac >>
      qexistsl_tac [`ps_dfs`, `block_ops`, `ps_after`, `bp0 ++ pre`, `post ++ rr0`] >>
      gvs[listTheory.APPEND_ASSOC]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`ps_dfs`, `block_ops`, `ps_after`, `bp0 ++ sr0 ++ pre`, `post`] >>
  gvs[listTheory.APPEND_ASSOC]
QED

Resume traversal_dfs_witness[succ]:
  rpt gen_tac >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  Cases_on `generate_fn_plan_aux liveness dfg cfg fn [succ] visited
    (ps with <| ps_stack := ss; ps_spilled := sp |>)`
  >- (simp[NoAsms, Once (cj 4 generate_fn_plan_aux_def)] >>
      asm_rewrite_tac[] >> simp[]) >>
  rename1 `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME sr` >>
  PairCases_on `sr` >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  qmatch_asmsub_abbrev_tac `generate_succs_plan liveness dfg cfg fn ss sp succs sr1 next_ps` >>
  Cases_on `generate_succs_plan liveness dfg cfg fn ss sp succs sr1 next_ps`
  >- (simp[NoAsms, Once (cj 4 generate_fn_plan_aux_def)] >>
      asm_rewrite_tac[] >> simp[Abbr `next_ps`]) >>
  rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME rr` >>
  PairCases_on `rr` >>
  simp[NoAsms, Once (cj 4 generate_fn_plan_aux_def)] >>
  asm_rewrite_tac[] >> simp[Abbr `next_ps`] >>
  rpt gen_tac >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  drule dfs_aux_call_branch >> disch_then assume_tac >>
  Cases_on `MEM lbl sr1`
  >- (first_x_assum drule_all >> strip_tac >>
      qexistsl_tac [`ps_dfs`, `block_ops`, `ps_after`, `pre`, `post ++ rr0`] >>
      gvs[listTheory.APPEND_ASSOC]) >>
  drule_all dfs_aux_call_sibling >> disch_then assume_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`ps_dfs`, `block_ops`, `ps_after`, `sr0 ++ pre`, `post`] >>
  gvs[listTheory.APPEND_ASSOC]
QED
Finalise traversal_dfs_witness

Theorem traversal_visited_closed:
  (!liveness dfg cfg fn wl visited ps ops final ps'.
    generate_fn_plan_aux liveness dfg cfg fn wl visited ps =
      SOME (ops, final, ps') ==>
    (!x. MEM x wl ==> MEM x final) /\
    (!x bb y. MEM x final /\ ~MEM x visited /\
      lookup_block x fn.fn_blocks = SOME bb /\
      MEM y (cfg_succs_of cfg x) ==> MEM y final)) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops final ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, final, ps') ==>
    (!x. MEM x succs ==> MEM x final) /\
    (!x bb y. MEM x final /\ ~MEM x visited /\
      lookup_block x fn.fn_blocks = SOME bb /\
      MEM y (cfg_succs_of cfg x) ==> MEM y final))
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  >- (simp[Once generate_fn_plan_aux_def] >> metis_tac[])
  >- suspend "aux_step"
  >- (simp[Once generate_fn_plan_aux_def] >> metis_tac[])
  >> suspend "succ_step"
QED

Resume traversal_visited_closed[aux_step]:
  rpt gen_tac >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  Cases_on `MEM lbl visited`
  >- (gvs[] >> simp[NoAsms, Once generate_fn_plan_aux_def] >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >> gvs[] >>
      rpt strip_tac >>
      drule generate_fn_plan_aux_visited_mono >>
      gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- (gvs[] >> simp[NoAsms, Once generate_fn_plan_aux_def] >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >> gvs[] >>
      rpt strip_tac >>
      drule generate_fn_plan_aux_visited_mono >>
      gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  Cases_on `generate_block_plan liveness dfg cfg fn bb ps`
  >- simp[Once generate_fn_plan_aux_def] >>
  rename1 `generate_block_plan _ _ _ _ _ _ = SOME bp` >>
  PairCases_on `bp` >>
  Cases_on `generate_succs_plan liveness dfg cfg fn bp1.ps_stack
    bp1.ps_spilled (cfg_succs_of cfg lbl) (lbl::visited) bp1`
  >- simp[Once generate_fn_plan_aux_def] >>
  rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME sr` >>
  PairCases_on `sr` >>
  Cases_on `generate_fn_plan_aux liveness dfg cfg fn wl sr1 sr2`
  >- simp[Once generate_fn_plan_aux_def] >>
  rename1 `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME rr` >>
  PairCases_on `rr` >>
  simp[NoAsms, Once generate_fn_plan_aux_def] >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `(case SOME bb of _ => _ | _ => _) = _` mp_tac >>
  simp[NoAsms] >> asm_rewrite_tac[] >> simp[NoAsms] >>
  asm_rewrite_tac[] >> simp[NoAsms] >>
  asm_rewrite_tac[] >> simp[NoAsms] >>
  asm_rewrite_tac[] >> simp[NoAsms] >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  qpat_assum `generate_block_plan _ _ _ _ _ _ = SOME _` (fn bp =>
    qpat_assum `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME _` (fn sr =>
      rule_assum_tac (SIMP_RULE (srw_ss()) [bp,sr]) >>
      assume_tac bp >> assume_tac sr)) >>
  qpat_assum `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME _` (fn rr =>
    rule_assum_tac (SIMP_RULE (srw_ss()) [rr]) >> assume_tac rr) >>
  qpat_x_assum `MEM lbl visited ==> _` kall_tac >> gvs[] >>
  drule generate_fn_plan_aux_visited_mono >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) [pred_setTheory.SUBSET_DEF]) >>
  drule generate_succs_plan_visited_mono >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) [pred_setTheory.SUBSET_DEF]) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >> Cases_on `MEM x sr1`
  >- (Cases_on `x = lbl` >- (gvs[] >> metis_tac[]) >> metis_tac[]) >>
  metis_tac[]
QED

Resume traversal_visited_closed[succ_step]:
  rpt gen_tac >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  Cases_on `generate_fn_plan_aux liveness dfg cfg fn [succ] visited
    (ps with <| ps_stack := ss; ps_spilled := sp |>)`
  >- (simp[NoAsms, Once (cj 4 generate_fn_plan_aux_def)] >>
      asm_rewrite_tac[] >> simp[]) >>
  rename1 `generate_fn_plan_aux _ _ _ _ _ _ _ = SOME sr` >>
  PairCases_on `sr` >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
  qmatch_asmsub_abbrev_tac `generate_succs_plan liveness dfg cfg fn ss sp succs sr1 next_ps` >>
  Cases_on `generate_succs_plan liveness dfg cfg fn ss sp succs sr1 next_ps`
  >- (simp[NoAsms, Once (cj 4 generate_fn_plan_aux_def)] >>
      asm_rewrite_tac[] >> simp[Abbr `next_ps`]) >>
  rename1 `generate_succs_plan _ _ _ _ _ _ _ _ _ = SOME rr` >>
  PairCases_on `rr` >>
  simp[NoAsms, Once (cj 4 generate_fn_plan_aux_def)] >>
  asm_rewrite_tac[] >> simp[NoAsms, Abbr `next_ps`] >>
  rpt gen_tac >> strip_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) []) >> gvs[] >>
  drule generate_succs_plan_visited_mono >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) [pred_setTheory.SUBSET_DEF]) >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM x sr1` >> metis_tac[]
QED
Finalise traversal_visited_closed

Theorem entry_traversal_reachable:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  generate_fn_plan_aux liveness dfg (cfg_analyze fn) fn [entry] [] ps0 =
    SOME (ops, final, ps_end) /\ fn_reachable fn lbl ==>
  MEM lbl final
Proof
  rpt strip_tac >>
  drule (cj 1 traversal_visited_closed) >> simp[] >> strip_tac >>
  `!a b. RTC (fn_cfg_edge fn) a b ==> MEM a final ==> MEM b final` by
    (ho_match_mp_tac relationTheory.RTC_INDUCT >>
     rpt strip_tac >> drule_all ready_fn_cfg_edge >> strip_tac >>
     metis_tac[]) >>
  gvs[fn_reachable_def] >> metis_tac[]
QED

(* Used at each jump of the block induction (JMP, both JNZ targets): the
   target is fn_reachable (the current block is, and the jump is a CFG
   edge), so it has a DFS state, its plan succeeds, and the plan is a
   contiguous slice of the function's plan (which fnPlanPlace places in
   prog).

   Why it should hold: generate_fn_plan_aux starts at [entry] and calls
   generate_succs_plan on cfg_succs_of of every block it plans; each call
   is a dfs_aux_call (dfs_aux_call_branch), and the plan returned SOME, so
   no call failed.  A label is only skipped as visited after it was
   planned, or as missing, which lookup_block = SOME rules out.
   cfg_succs_of (cfg_analyze fn) agrees with bb_succs (fn_cfg_edge) under
   wf_function (codegen_ready_fn), and block_ops is appended to the output
   unchanged (fnPlanDecomp$fn_plan_aux_per_block shows the asm form). *)
Theorem dfs_block_state_reachable:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_reachable fn lbl /\ lookup_block lbl fn.fn_blocks = SOME bb
    ==>
    ?ps_dfs block_ops ps_dfs_after pre post.
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb ps_dfs =
        SOME (block_ops, ps_dfs_after) /\
      fn_ops = pre ++ block_ops ++ post
Proof
  rpt strip_tac >> gvs[] >>
  `?entry. fn_entry_label fn = SOME entry` by
    metis_tac[fn_reachable_def] >>
  drule_all cleanup_plan_entry_call >> strip_tac >>
  `MEM lbl visited` by
    (irule entry_traversal_reachable >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule (cj 1 traversal_dfs_witness) >>
  disch_then irule >> simp[dfs_aux_call_entry]
QED
