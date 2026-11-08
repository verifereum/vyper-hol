(*
 * Planner lineages: the successor-transfer obligation of the block induction
 *
 * The DFS function planner (generate_fn_plan_aux / generate_succs_plan)
 * plans each block once, from the state its first-visited predecessor
 * left.  At run time a join is also entered from its other predecessors,
 * whose planner state at the jump differs from the one the join was
 * planned from.  The block induction behind gen_fn_frame_simulation
 * (venomToAsmPropsScript.sml) therefore runs on lineage states: the
 * planner state of the path actually taken, with every field the frame
 * invariant does not read taken from the block's DFS state.
 *
 * TOP-LEVEL:
 *   dfs_aux_call, dfs_succs_call — the calls the function planner makes
 *   dfs_block_state             — the state the planner planned a block from
 *   lineage_state               — planner states along any CFG path that
 *                                 replays each block's DFS code
 *   lineage_entry               — one lineage step, from an explicit
 *                                 predecessor into its successor
 *   lineage_state_block_plan    — CHEATED successor transfer: a lineage
 *                                 state regenerates the block's DFS code
 * Helper:
 *   lineage_state_dfs_fields    — a lineage state is a DFS state with its
 *                                 stack and spill map replaced
 *   lineage_entry_lineage_state — a lineage entry is a lineage state
 *)

Theory fnPlanLineage
Ancestors
  stackPlanGen stackPlanTypes fnPlanLineageJoinEntry fnPlanLineageLiveness
  fnPlanLineagePhiSchedule fnPlanLineagePhiTemporal codegenReadyCompute
  fnPlanLineageCallTrace fnPlanLineageEdge fnPlanLineageNativeTrace
  fnPlanLineageNativeOrigins fnPlanLineageEntryProduction
  fnPlanLineageChronologicalPrefix fnPlanLineageNativeResources
  fnPlanLineageObserverTransport

(* ===== The calls of the DFS function planner ===== *)

(* dfs_aux_call ... ps0 wl visited ps: the function planner, started from
   ps0 at the entry label as generate_fn_plan_with_cleanup_analyzed starts
   it, calls generate_fn_plan_aux on (wl, visited, ps); dfs_succs_call
   likewise for generate_succs_plan.  Each rule mirrors one recursive call
   of the definition, made once the calls before it have returned. *)
Inductive dfs_aux_call:
[~entry:]
  fn_entry_label fn = SOME lbl ==>
  dfs_aux_call liveness dfg cfg fn ps0 [lbl] [] ps0
[~visited:]
  dfs_aux_call liveness dfg cfg fn ps0 (lbl::rest) visited ps /\
  MEM lbl visited ==>
  dfs_aux_call liveness dfg cfg fn ps0 rest visited ps
[~missing:]
  dfs_aux_call liveness dfg cfg fn ps0 (lbl::rest) visited ps /\
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = NONE ==>
  dfs_aux_call liveness dfg cfg fn ps0 rest (lbl::visited) ps
[~succs:]
  dfs_aux_call liveness dfg cfg fn ps0 (lbl::rest) visited ps /\
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (block_ops, ps1) ==>
  dfs_succs_call liveness dfg cfg fn ps0 ps1.ps_stack ps1.ps_spilled
    (cfg_succs_of cfg lbl) (lbl::visited) ps1
[~rest:]
  dfs_aux_call liveness dfg cfg fn ps0 (lbl::rest) visited ps /\
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (block_ops, ps1) /\
  generate_succs_plan liveness dfg cfg fn ps1.ps_stack ps1.ps_spilled
    (cfg_succs_of cfg lbl) (lbl::visited) ps1 =
    SOME (succ_ops, visited2, ps2) ==>
  dfs_aux_call liveness dfg cfg fn ps0 rest visited2 ps2
[~branch:]
  dfs_succs_call liveness dfg cfg fn ps0 saved_stack saved_spilled
    (succ::succs) visited ps_g ==>
  dfs_aux_call liveness dfg cfg fn ps0 [succ] visited
    (ps_g with <| ps_stack := saved_stack; ps_spilled := saved_spilled |>)
[~sibling:]
  dfs_succs_call liveness dfg cfg fn ps0 saved_stack saved_spilled
    (succ::succs) visited ps_g /\
  generate_fn_plan_aux liveness dfg cfg fn [succ] visited
    (ps_g with <| ps_stack := saved_stack; ps_spilled := saved_spilled |>) =
    SOME (s_ops, visited_after, ps_after) ==>
  dfs_succs_call liveness dfg cfg fn ps0 saved_stack saved_spilled
    succs visited_after
    (ps_g with <|
       ps_alloc := ps_after.ps_alloc with
         sa_free_slots := ps_g.ps_alloc.sa_free_slots;
       ps_label_counter := ps_after.ps_label_counter |>)
End

(* The function planner, run from ps0, planned block lbl from state ps:
   it called generate_fn_plan_aux with lbl unvisited at the head of the
   worklist, which is where generate_block_plan is applied to it. *)
Definition dfs_block_state_def:
  dfs_block_state liveness dfg cfg fn ps0 lbl ps <=>
    ?rest visited.
      dfs_aux_call liveness dfg cfg fn ps0 (lbl::rest) visited ps /\
      ~MEM lbl visited
End

(* ===== Lineage states ===== *)

(* The planner state of a run-time path, from the entry block along CFG
   edges.  Entering block succ from block lbl, the state is succ's DFS
   state with the stack and spill map that lbl's code leaves; the spill
   allocator, label counter and cleanup fields stay those of the DFS
   state, as the emitted code's spill offsets and fresh labels are.

   The code executed at lbl is its DFS code, so a step replays exactly
   that code.  It may do so with other cleanup fields: clean_stack_plan's
   elision test reads LENGTH ps_stack, which counts the dead_stack_marker
   prefix, and that prefix's length depends on the path, while the
   path-local promise in ps_cleanup_promised comes from the DFS path.  No
   field the frame invariant reads (ps_stack, ps_spilled, ps_alloc) is
   chosen freely.

   The step requires lbl's code to leave succ's DFS spill map, so a lineage
   state is succ's DFS state with only ps_stack swapped: ps_spilled is
   pinned to the DFS run and only ps_stack is path dependent. *)
Inductive lineage_state:
[~entry:]
  fn_entry_label fn = SOME lbl ==>
  lineage_state liveness dfg cfg fn ps0 lbl ps0
[~step:]
  lineage_state liveness dfg cfg fn ps0 lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  dfs_block_state liveness dfg cfg fn ps0 lbl ps_dfs /\
  generate_block_plan liveness dfg cfg fn bb ps_dfs =
    SOME (block_ops, ps_dfs_after) /\
  generate_block_plan liveness dfg cfg fn bb
    (ps with <| ps_cleanup_height := ch; ps_cleanup_promised := promised |>) =
    SOME (block_ops, ps_after) /\
  MEM succ (cfg_succs_of cfg lbl) /\
  dfs_block_state liveness dfg cfg fn ps0 succ ps_succ /\
  ps_after.ps_spilled = ps_succ.ps_spilled ==>
  lineage_state liveness dfg cfg fn ps0 succ
    (ps_succ with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>)
End

(* Exact physical edges of the frozen lineage rule, without its recursive
   premise. No resource invariant is imposed on these witnesses. *)
Definition lineage_edge_def:
  lineage_edge lv dfg cfg fn ps0 (lbl,ps) (succ,qs) <=>
    ?bb ps_dfs block_ops ps_dfs_after ch promised ps_after ps_succ.
      lookup_block lbl fn.fn_blocks = SOME bb /\
      dfs_block_state lv dfg cfg fn ps0 lbl ps_dfs /\
      generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,ps_dfs_after) /\
      generate_block_plan lv dfg cfg fn bb
        (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
        SOME (block_ops,ps_after) /\
      MEM succ (cfg_succs_of cfg lbl) /\
      dfs_block_state lv dfg cfg fn ps0 succ ps_succ /\
      ps_after.ps_spilled = ps_succ.ps_spilled /\
      qs = ps_succ with <|ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled|>
End

Theorem lineage_edge_step:
  lineage_state lv dfg cfg fn ps0 lbl ps /\
  lineage_edge lv dfg cfg fn ps0 (lbl,ps) (succ,qs) ==>
  lineage_state lv dfg cfg fn ps0 succ qs
Proof
  rewrite_tac[lineage_edge_def] >> rpt strip_tac >>
  qpat_x_assum `qs = _` SUBST1_TAC >>
  irule lineage_state_step >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem lineage_state_history:
  !lv dfg cfg fn ps0 lbl ps.
    lineage_state lv dfg cfg fn ps0 lbl ps ==>
    ?entry vertices. fn_entry_label fn = SOME entry /\
      LRC (lineage_edge lv dfg cfg fn ps0) vertices (entry,ps0) (lbl,ps)
Proof
  rpt gen_tac >> qid_spec_tac `ps` >> qid_spec_tac `lbl` >>
  ho_match_mp_tac lineage_state_ind >> rpt strip_tac
  >- (qexistsl_tac [`lbl`,`[]`] >> simp[listTheory.LRC_def]) >>
  qexistsl_tac [`entry`,`vertices ++ [(lbl,ps)]`] >>
  simp[fnPlanLineageCallTraceTheory.LRC_APPEND, listTheory.LRC_def] >>
  simp[lineage_edge_def] >>
  qexists_tac `ps_dfs` >>
  qexists_tac `block_ops` >> qexists_tac `ps_dfs_after` >>
  qexists_tac `ch` >> qexists_tac `promised` >>
  qexists_tac `ps_after` >> qexists_tac `ps_succ` >> simp[]
QED

Theorem lineage_history_reconstruct:
  !vertices x y.
    LRC (lineage_edge lv dfg cfg fn ps0) vertices x y ==>
    lineage_state lv dfg cfg fn ps0 (FST x) (SND x) ==>
    lineage_state lv dfg cfg fn ps0 (FST y) (SND y)
Proof
  Induct >> simp[listTheory.LRC_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!x y. _` (qspecl_then [`z`,`y`] mp_tac) >>
  simp[] >> disch_then irule >>
  PairCases_on `h` >> PairCases_on `z` >> gvs[] >>
  metis_tac[lineage_edge_step]
QED

Theorem lineage_state_history_iff:
  lineage_state lv dfg cfg fn ps0 lbl ps <=>
  ?entry vertices. fn_entry_label fn = SOME entry /\
    LRC (lineage_edge lv dfg cfg fn ps0) vertices (entry,ps0) (lbl,ps)
Proof
  eq_tac >- metis_tac[lineage_state_history] >> rpt strip_tac >>
  drule lineage_history_reconstruct >> simp[lineage_state_entry]
QED

Theorem lineage_edge_physical:
  lineage_edge lv dfg cfg fn ps0 (lbl,ps) (succ,qs) ==>
  ?bb ch promised ops after.
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb
      (ps with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    MEM succ (cfg_succs_of cfg lbl) /\
    qs.ps_stack = after.ps_stack /\ qs.ps_spilled = after.ps_spilled
Proof
  simp[lineage_edge_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem lineage_history_cfg:
  codegen_ready_fn fn ==>
  !vertices x y.
    LRC (lineage_edge lv dfg (cfg_analyze fn) fn ps0) vertices x y ==>
    LRC (venomWf$fn_cfg_edge fn) (MAP FST vertices) (FST x) (FST y)
Proof
  strip_tac >> Induct >> simp[listTheory.LRC_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `FST z` >> conj_tac
  >- (PairCases_on `h` >> PairCases_on `z` >> gvs[] >>
      drule lineage_edge_physical >> strip_tac >>
      `wf_function fn` by gvs[codegen_ready_fn_def] >>
      metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze]) >>
  metis_tac[]
QED

Theorem lineage_history_path:
  codegen_ready_fn fn /\
  LRC (lineage_edge lv dfg (cfg_analyze fn) fn ps0) vertices x y ==>
  is_fn_path fn (MAP FST vertices ++ [FST y]) /\
  HD (MAP FST vertices ++ [FST y]) = FST x
Proof
  strip_tac >> drule lineage_history_cfg >> disch_then drule >>
  metis_tac[codegenReadyComputeTheory.lrc_to_is_fn_path]
QED

Theorem lineage_history_consecutive_return:
  LRC (lineage_edge lv dfg cfg fn ps0) pre root (d,ps) /\
  lineage_edge lv dfg cfg fn ps0 (d,ps) z /\
  LRC (lineage_edge lv dfg cfg fn ps0) rest z final /\
  (EXISTS (\s. FST s = d) rest \/ FST final = d) ==>
  ?middle b post.
    rest = middle ++ post /\ FST b = d /\
    EVERY (\s. FST s <> d) middle /\
    LRC (lineage_edge lv dfg cfg fn ps0) pre root (d,ps) /\
    LRC (lineage_edge lv dfg cfg fn ps0) ((d,ps)::middle) (d,ps) b /\
    LRC (lineage_edge lv dfg cfg fn ps0) post b final /\
    LRC (lineage_edge lv dfg cfg fn ps0) (pre ++ (d,ps)::rest) root final
Proof
  strip_tac >>
  ho_match_mp_tac fnPlanLineageCallTraceTheory.LRC_consecutive_return >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem lineage_history_return_path:
  codegen_ready_fn fn /\
  LRC (lineage_edge lv dfg (cfg_analyze fn) fn ps0)
    ((d,ps)::middle) (d,ps) (d,qs) /\
  EVERY (\s. FST s <> d) middle ==>
  is_fn_path fn (d::(MAP FST middle ++ [d])) /\
  MAP FST middle ++ [d] <> [] /\
  LAST (MAP FST middle ++ [d]) = d /\
  ~MEM d (FRONT (MAP FST middle ++ [d]))
Proof
  strip_tac >> drule_all lineage_history_path >> simp[] >>
  gvs[rich_listTheory.FRONT_APPEND, listTheory.EVERY_MEM, listTheory.MEM_MAP] >> metis_tac[]
QED

(* Helper: every field but the stack is a DFS state's. *)
Theorem lineage_state_dfs_fields:
  !liveness dfg cfg fn ps0 lbl ps.
    lineage_state liveness dfg cfg fn ps0 lbl ps ==>
    ?ps_dfs.
      dfs_block_state liveness dfg cfg fn ps0 lbl ps_dfs /\
      ps = ps_dfs with ps_stack := ps.ps_stack
Proof
  rpt gen_tac >> qid_spec_tac `ps` >> qid_spec_tac `lbl` >>
  ho_match_mp_tac lineage_state_ind >> rpt strip_tac
  >- (qexists_tac `ps0` >>
      simp[dfs_block_state_def, plan_state_component_equality] >>
      qexistsl_tac [`[]`, `[]`] >> simp[dfs_aux_call_entry])
  >> qexists_tac `ps_succ` >> simp[]
QED

Theorem dfs_calls_lineage_origin[local]:
  !lv dfg cfg fn ps0.
  (!wl visited ps. dfs_aux_call lv dfg cfg fn ps0 wl visited ps ==>
    dfs_aux_call lv dfg cfg fn ps0 wl visited ps /\
    (wl = [] \/ ?lbl. wl = [lbl] /\
      (~MEM lbl visited ==> lineage_state lv dfg cfg fn ps0 lbl ps))) /\
  (!stack spilled wl visited ps.
    dfs_succs_call lv dfg cfg fn ps0 stack spilled wl visited ps ==>
    dfs_succs_call lv dfg cfg fn ps0 stack spilled wl visited ps /\
    ?pred pb before ops after.
      lineage_state lv dfg cfg fn ps0 pred before /\
      dfs_block_state lv dfg cfg fn ps0 pred before /\
      lookup_block pred fn.fn_blocks = SOME pb /\
      generate_block_plan lv dfg cfg fn pb before = SOME (ops,after) /\
      EVERY (\succ. MEM succ (cfg_succs_of cfg pred)) wl /\
      stack = after.ps_stack /\ spilled = after.ps_spilled)
Proof
  rpt gen_tac >> ho_match_mp_tac dfs_aux_call_ind >>
  rpt strip_tac >> gvs[] >>
  simp[dfs_aux_call_entry, lineage_state_entry]
  >- (irule dfs_aux_call_visited >> goal_assum (drule_at Any) >> simp[])
  >- (irule dfs_aux_call_missing >> goal_assum (drule_at Any) >> simp[])
  >- (irule dfs_aux_call_succs >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> qexists_tac `[]` >> simp[])
  >- (qexistsl_tac [`lbl`, `bb`, `ps`, `block_ops`, `ps'`] >>
      simp[listTheory.EVERY_MEM, dfs_block_state_def] >>
      qexistsl_tac [`[]`, `visited`] >> simp[])
  >- (irule dfs_aux_call_rest >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[])
  >- (irule dfs_aux_call_branch >> goal_assum (drule_at Any))
  >- (strip_tac >>
      `dfs_block_state lv dfg cfg fn ps0 succ
        (ps with <|ps_stack := after.ps_stack; ps_spilled := after.ps_spilled|>)` by
        (simp[dfs_block_state_def] >> qexistsl_tac [`[]`, `visited`] >>
         simp[] >> irule dfs_aux_call_branch >> goal_assum (drule_at Any)) >>
      qmatch_goalsub_abbrev_tac `lineage_state _ _ _ _ _ _ target` >>
      `target = target with <|ps_stack := after.ps_stack;
                              ps_spilled := after.ps_spilled|>` by simp[Abbr `target`] >>
      pop_assum SUBST1_TAC >>
      irule lineage_state_step >>
      conj_tac >- simp[Abbr `target`] >>
      conj_tac >- simp[] >>
      qexistsl_tac [`pb`, `ops`, `before.ps_cleanup_height`, `pred`,
        `before.ps_cleanup_promised`, `before`, `before`, `after`] >> simp[])
  >- (irule dfs_aux_call_sibling >> goal_assum (drule_at Any) >> simp[]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem dfs_block_state_lineage_state:
  !lv dfg cfg fn ps0 lbl ps.
    dfs_block_state lv dfg cfg fn ps0 lbl ps ==>
    lineage_state lv dfg cfg fn ps0 lbl ps
Proof
  rpt strip_tac >> gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_lineage_origin) >> simp[]
QED

Theorem dfs_calls_trace_embedding[local]:
  !lv dfg cfg fn ps0.
  (!wl visited ps. dfs_aux_call lv dfg cfg fn ps0 wl visited ps ==>
    !entry root_result root_events.
    fn_entry_label fn = SOME entry /\
    plan_aux_trace lv dfg cfg fn [entry] [] ps0 root_result root_events ==>
    ?result events. plan_aux_trace lv dfg cfg fn wl visited ps result events /\
      set events SUBSET set root_events) /\
  (!stack spilled wl visited ps. dfs_succs_call lv dfg cfg fn ps0 stack spilled wl visited ps ==>
    !entry root_result root_events.
    fn_entry_label fn = SOME entry /\
    plan_aux_trace lv dfg cfg fn [entry] [] ps0 root_result root_events ==>
    ?result events. plan_succs_trace lv dfg cfg fn stack spilled wl visited ps result events /\
      set events SUBSET set root_events)
Proof
  rpt gen_tac >> ho_match_mp_tac dfs_aux_call_ind >> rpt strip_tac >> gvs[]
  >- (goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum drule >> strip_tac
  >- (drule_all plan_aux_trace_visited_head >> strip_tac >>
      goal_assum (drule_at Any) >> simp[])
  >- (drule_all plan_aux_trace_missing_head >> strip_tac >>
      goal_assum (drule_at Any) >> metis_tac[pred_setTheory.SUBSET_TRANS])
  >- (drule_all plan_aux_trace_present_head >> strip_tac >>
      goal_assum (drule_at Any) >> metis_tac[pred_setTheory.SUBSET_TRANS])
  >- (drule_all plan_aux_trace_present_head >> strip_tac >>
      drule (cj 2 plan_trace_erasure) >> strip_tac >> gvs[] >>
      goal_assum (drule_at Any) >> metis_tac[pred_setTheory.SUBSET_TRANS])
  >- (drule plan_succs_trace_cons >> strip_tac >>
      goal_assum (drule_at Any) >> metis_tac[pred_setTheory.SUBSET_TRANS]) >>
  drule plan_succs_trace_cons >> strip_tac >>
  drule (cj 1 plan_trace_erasure) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem dfs_block_state_trace_event[local]:
  fn_entry_label fn = SOME entry /\
  plan_aux_trace lv dfg cfg fn [entry] [] ps0 result events /\
  dfs_block_state lv dfg cfg fn ps0 lbl ps ==> MEM (lbl,ps) events
Proof
  rpt strip_tac >> gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_trace_embedding) >>
  disch_then drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all plan_aux_trace_fresh_event >>
  fs[pred_setTheory.SUBSET_DEF]
QED

Theorem lineage_state_has_entry[local]:
  !lv dfg cfg fn ps0 lbl ps.
    lineage_state lv dfg cfg fn ps0 lbl ps ==>
    ?entry. fn_entry_label fn = SOME entry
Proof
  rpt gen_tac >> qid_spec_tac `ps` >> qid_spec_tac `lbl` >>
  ho_match_mp_tac lineage_state_ind >> metis_tac[]
QED

(* Successful initialized planning supplies a chronological trace for every
   actual DFS block state.  Keep the prefix witness for freshness consumers. *)
Theorem dfs_block_state_initialized_trace:
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn
    spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps ==>
  ?entry result events pre post.
    fn_entry_label fn = SOME entry /\
    plan_aux_trace lv dfg cfg fn [entry] []
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) result events /\
    events = pre ++ (lbl,ps)::post
Proof
  strip_tac >>
  `?entry. fn_entry_label fn = SOME entry` by
    metis_tac[dfs_block_state_lineage_state, lineage_state_has_entry] >>
  qpat_x_assum `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >> strip_tac >>
  drule (cj 1 plan_trace_complete) >> strip_tac >>
  `MEM (lbl,ps) events` by metis_tac[dfs_block_state_trace_event] >>
  metis_tac[listTheory.MEM_SPLIT]
QED

Theorem dfs_block_state_native_exit:
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb ps = SOME (ops,qs) ==>
  ?pre. ~MEM lbl pre /\ chronological_support fn (lbl::pre) qs /\
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs /\
    cfg_reachable_of (cfg_analyze fn) lbl /\ fn_reachable fn lbl
Proof
  strip_tac >> drule_all dfs_block_state_initialized_trace >> strip_tac >>
  drule_all initialized_trace_event_exit >> strip_tac >>
  drule_all initialized_trace_event_reachable >> strip_tac >>
  qexists_tac `MAP FST pre` >> simp[] >>
  drule plan_aux_trace_distinct_keys >>
  simp[listTheory.MAP_APPEND, listTheory.ALL_DISTINCT_APPEND] >> metis_tac[]
QED

(* The support set belongs to the chronological prefix before this block,
   not to a run-time path.  Saved physical resources survive sibling visits. *)
Theorem dfs_block_state_native_incoming:
  codegen_ready_fn fn /\ fn_entry_label fn <> SOME lbl /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps ==>
  ?entry visited pred before pb ops after.
    fn_entry_label fn = SOME entry /\ fn_reachable fn lbl /\
    ~MEM lbl visited /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb before = SOME (ops,after) /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    ps.ps_stack = after.ps_stack /\ ps.ps_spilled = after.ps_spilled /\
    chronological_support fn visited after /\
    native_live_boundary fn pb (LENGTH pb.bb_instructions) after
Proof
  strip_tac >> drule_all dfs_block_state_initialized_trace >> strip_tac >>
  drule_all initialized_trace_event_reachable >> strip_tac >>
  drule_all plan_aux_trace_singleton_physical_ancestry >> strip_tac >> gvs[] >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  `?earlier rest. pre = earlier ++ (pred,before)::rest` by
    metis_tac[listTheory.MEM_SPLIT] >>
  `chronological_support fn (pred::MAP FST earlier) after /\
   native_live_boundary fn pb (LENGTH pb.bb_instructions) after` by
    (gvs[] >>
     drule_at (Pat `plan_aux_trace _ _ _ _ _ _ _ _ _`)
       initialized_trace_event_exit >>
     simp[] >> disch_then (qspec_then `earlier` mp_tac) >>
     simp[]) >>
  `cfg_reachable_of (cfg_analyze fn) pred` by
    (gvs[] >>
     drule_at (Pat `plan_aux_trace _ _ _ _ _ _ _ _ _`)
       initialized_trace_event_reachable >>
     simp[] >> disch_then (qspec_then `earlier` mp_tac) >> simp[]) >>
  `~MEM lbl (MAP FST pre)` by
    (drule plan_aux_trace_distinct_keys >>
     simp[listTheory.MAP_APPEND, listTheory.ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qexistsl_tac [`MAP FST pre`, `pred`, `before`, `pb`, `ops`, `after`] >>
  simp[] >> irule chronological_support_mono >> goal_assum (drule_at Any) >>
  simp[pred_setTheory.SUBSET_DEF, listTheory.MAP_APPEND] >> metis_tac[]
QED

Theorem dfs_block_state_native_join_residual:
  codegen_ready_fn fn /\ fn_entry_label fn <> SOME lbl /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) ==>
  ?pred prefix.
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    ps.ps_stack = prefix ++ MAP Var
      (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) /\
    DISJOINT (set prefix) (set (MAP Var
      (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)))) /\
    ps.ps_spilled = FEMPTY
Proof
  strip_tac >> drule_all dfs_block_state_native_incoming >> strip_tac >>
  drule_all native_join_edge_residual >> strip_tac >>
  qexistsl_tac [`pred`, `prefix`] >> simp[]
QED

Theorem dfs_block_state_native_phi_selection:
  codegen_ready_fn fn /\ fn_entry_label fn <> SOME lbl /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) ps k qs /\
  k <= j /\ j < LENGTH (collect_phis bb.bb_instructions) ==>
  ?d w. stack_get_phi_depth
      (FILTER is_var_operand (EL j (collect_phis bb.bb_instructions)).inst_operands)
      qs.ps_stack = SOME d /\
    stack_peek d qs.ps_stack = Var w /\
    MEM (Var w) (EL j (collect_phis bb.bb_instructions)).inst_operands
Proof
  strip_tac >> drule_all dfs_block_state_native_incoming >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `EVERY (\inst. inst.inst_opcode = PHI) (TAKE k (non_param_insts bb))` by
    (qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
     `k <= LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
     gvs[listTheory.TAKE_APPEND1] >>
     irule rich_listTheory.EVERY_TAKE >>
     simp[listTheory.EVERY_MEM] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  `?result. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) after k result /\
    result.ps_stack = qs.ps_stack /\ result.ps_spilled = qs.ps_spilled` by
    (irule native_phi_prefix_physical_transport >> metis_tac[]) >>
  `?d w. stack_get_phi_depth
      (FILTER is_var_operand (EL j (collect_phis bb.bb_instructions)).inst_operands)
      result.ps_stack = SOME d /\
    stack_peek d result.ps_stack = Var w /\
    MEM (Var w) (EL j (collect_phis bb.bb_instructions)).inst_operands` by
    (irule incoming_join_native_phi_prefix_selection >>
     simp[] >> gvs[chronological_support_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem dfs_block_state_native_ordinary_boundary:
  codegen_ready_fn fn /\ fn_entry_label fn <> SOME lbl /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) ps k qs /\
  LENGTH (collect_phis bb.bb_instructions) <= k /\
  k <= PRE (LENGTH bb.bb_instructions) ==>
  native_live_boundary fn bb k qs
Proof
  strip_tac >> drule_all dfs_block_state_native_incoming >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  metis_tac[incoming_join_native_ordinary_prefix]
QED

Theorem dfs_block_state_native_ordinary_suffix_exclusion:
  codegen_ready_fn fn /\ fn_entry_label fn <> SOME lbl /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) ps k qs /\
  LENGTH (collect_phis bb.bb_instructions) <= k /\
  k <= PRE (LENGTH bb.bb_instructions) /\
  qs.ps_stack = prefix ++ suffix /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) lbl k) ==> MEM (Var v) suffix) ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) lbl k) ==>
    ~MEM (Var v) prefix /\ Var v NOTIN FDOM qs.ps_spilled /\
    LIST_ELEM_COUNT (Var v) suffix = 1
Proof
  strip_tac >> drule_all dfs_block_state_native_ordinary_boundary >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  metis_tac[native_live_boundary_suffix_exclusion]
QED

Theorem dfs_block_state_native_ordinary_residual_observations:
  codegen_ready_fn fn /\ fn_entry_label fn <> SOME lbl /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) ps a qs /\
  LENGTH (collect_phis bb.bb_instructions) <= a /\
  a <= PRE (LENGTH bb.bb_instructions) /\ a <= j /\ j < LENGTH bb.bb_instructions /\
  qs.ps_stack = prefix ++ suffix /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) lbl a) ==> MEM (Var v) suffix) ==>
  EVERY (\v. ~MEM (Var v) prefix) (live_vars_at (liveness_analyze fn) lbl a) /\
  (!k. a <= k /\ k <= j ==>
    EVERY (\v. ~MEM (Var v) prefix) (EL k bb.bb_instructions).inst_outputs) /\
  EVERY (\v. ~MEM (Var v) prefix)
    (live_vars_at (liveness_analyze fn) lbl (SUC j) ++
     (EL j bb.bb_instructions).inst_outputs) /\
  (!v. MEM (Var v) (compute_operands (EL j bb.bb_instructions)) ==>
    ~MEM (Var v) prefix)
Proof
  strip_tac >> drule_all dfs_block_state_native_incoming >> strip_tac >>
  `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_label, venomExecPropsTheory.lookup_block_MEM] >>
  `lbl <> entry` by metis_tac[] >>
  `~MEM bb.bb_label visited` by simp[] >>
  drule_all incoming_join_native_ordinary_prefix >> strip_tac >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  drule_all native_ordinary_interval_residual_exclusion >> simp[]
QED

Theorem dfs_block_state_unique:
  fn_entry_label fn = SOME entry /\
  generate_fn_plan_aux lv dfg cfg fn [entry] [] ps0 = SOME result /\
  dfs_block_state lv dfg cfg fn ps0 lbl psD /\
  dfs_block_state lv dfg cfg fn ps0 lbl psE ==> psD = psE
Proof
  rpt strip_tac >> drule (cj 1 plan_trace_complete) >> strip_tac >>
  `MEM (lbl,psD) events` by metis_tac[dfs_block_state_trace_event] >>
  `MEM (lbl,psE) events` by metis_tac[dfs_block_state_trace_event] >>
  metis_tac[plan_aux_trace_event_unique]
QED

Theorem lineage_state_actual_dfs_fields:
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn
    spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psD ==>
  ps = psD with ps_stack := ps.ps_stack
Proof
  rpt strip_tac >>
  drule lineage_state_has_entry >> strip_tac >>
  qpat_x_assum `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _`
    mp_tac >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  strip_tac >>
  drule lineage_state_dfs_fields >> strip_tac >>
  `ps_dfs = psD` by (irule dfs_block_state_unique >> goal_assum (drule_at Any) >>
    goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[]
QED

Theorem lineage_state_actual_dfs_alloc:
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn
    spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psD ==>
  ps.ps_alloc = psD.ps_alloc
Proof
  strip_tac >> drule_all lineage_state_actual_dfs_fields >>
  simp[plan_state_component_equality]
QED

Theorem lineage_state_actual_dfs_spilled:
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn
    spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psD ==>
  ps.ps_spilled = psD.ps_spilled
Proof
  strip_tac >> drule_all lineage_state_actual_dfs_fields >>
  simp[plan_state_component_equality]
QED

Theorem lineage_state_actual_dfs_label_counter:
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn
    spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psD ==>
  ps.ps_label_counter = psD.ps_label_counter
Proof
  strip_tac >> drule_all lineage_state_actual_dfs_fields >>
  simp[plan_state_component_equality]
QED

(* Projection-only provenance: this predicate adds no reachability rules. *)
Definition predecessor_plan_fields_def:
  predecessor_plan_fields lv dfg cfg fn lbl stk spills <=>
  ?pred pb psBefore ops psAfter.
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of cfg pred) /\
    generate_block_plan lv dfg cfg fn pb psBefore = SOME (ops, psAfter) /\
    stk = psAfter.ps_stack /\ spills = psAfter.ps_spilled
End

Theorem dfs_calls_predecessor_fields[local]:
  !lv dfg cfg fn ps0.
  (!wl visited ps.
    dfs_aux_call lv dfg cfg fn ps0 wl visited ps ==>
    wl = [] \/
    (?lbl. wl = [lbl] /\
      ((fn_entry_label fn = SOME lbl /\ ps = ps0) \/
       predecessor_plan_fields lv dfg cfg fn lbl ps.ps_stack ps.ps_spilled))) /\
  (!stk spills succs visited ps.
    dfs_succs_call lv dfg cfg fn ps0 stk spills succs visited ps ==>
    !lbl. MEM lbl succs ==> predecessor_plan_fields lv dfg cfg fn lbl stk spills)
Proof
  rpt gen_tac >> ho_match_mp_tac dfs_aux_call_ind >> rpt strip_tac >> gvs[] >>
  simp[predecessor_plan_fields_def] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem dfs_block_state_predecessor_origin:
  !lv dfg cfg fn ps0 lbl ps.
  dfs_block_state lv dfg cfg fn ps0 lbl ps /\ fn_entry_label fn <> SOME lbl ==>
  ?pred pb psBefore ops psAfter.
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of cfg pred) /\
    generate_block_plan lv dfg cfg fn pb psBefore = SOME (ops, psAfter) /\
    ps.ps_stack = psAfter.ps_stack /\ ps.ps_spilled = psAfter.ps_spilled
Proof
  rpt strip_tac >> gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_predecessor_fields) >>
  simp[predecessor_plan_fields_def] >> strip_tac >> gvs[]
QED

Theorem lineage_state_predecessor_origin:
  !lv dfg cfg fn ps0 lbl ps.
  lineage_state lv dfg cfg fn ps0 lbl ps /\ fn_entry_label fn <> SOME lbl ==>
  ?pred pb psBefore ops psAfter.
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of cfg pred) /\
    generate_block_plan lv dfg cfg fn pb psBefore = SOME (ops, psAfter) /\
    ps.ps_stack = psAfter.ps_stack /\ ps.ps_spilled = psAfter.ps_spilled
Proof
  rpt strip_tac >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  simp[Once lineage_state_cases] >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem dfs_calls_reachable_origin[local]:
  !lv dfg fn ps0.
  wf_function fn ==>
  (!wl visited ps.
    dfs_aux_call lv dfg (cfg_analyze fn) fn ps0 wl visited ps ==>
    EVERY (cfg_reachable_of (cfg_analyze fn)) wl /\
    (wl = [] \/
     ?lbl. wl = [lbl] /\
       ((fn_entry_label fn = SOME lbl /\ ps = ps0) \/
        ?pred pb psBefore ops psAfter.
          cfg_reachable_of (cfg_analyze fn) pred /\
          lookup_block pred fn.fn_blocks = SOME pb /\
          MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
          generate_block_plan lv dfg (cfg_analyze fn) fn pb psBefore =
            SOME (ops,psAfter) /\
          ps.ps_stack = psAfter.ps_stack /\ ps.ps_spilled = psAfter.ps_spilled))) /\
  (!stk spills succs visited ps.
    dfs_succs_call lv dfg (cfg_analyze fn) fn ps0 stk spills succs visited ps ==>
    !lbl. MEM lbl succs ==>
      cfg_reachable_of (cfg_analyze fn) lbl /\
      ?pred pb psBefore ops psAfter.
        cfg_reachable_of (cfg_analyze fn) pred /\
        lookup_block pred fn.fn_blocks = SOME pb /\
        MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
        generate_block_plan lv dfg (cfg_analyze fn) fn pb psBefore =
          SOME (ops,psAfter) /\
        stk = psAfter.ps_stack /\ spills = psAfter.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac dfs_aux_call_ind >>
  rpt strip_tac >> gvs[] >>
  metis_tac[analyzed_entry_reachable, analyzed_successor_reachable]
QED

Theorem dfs_block_state_reachable:
  !lv dfg fn ps0 lbl ps.
  wf_function fn /\ dfs_block_state lv dfg (cfg_analyze fn) fn ps0 lbl ps ==>
  cfg_reachable_of (cfg_analyze fn) lbl
Proof
  rpt strip_tac >> gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_reachable_origin) >>
  disch_then drule >> simp[]
QED

Theorem dfs_block_state_reachable_predecessor_origin:
  !lv dfg fn ps0 lbl ps.
  wf_function fn /\ dfs_block_state lv dfg (cfg_analyze fn) fn ps0 lbl ps /\
  fn_entry_label fn <> SOME lbl ==>
  ?pred pb psBefore ops psAfter.
    cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    generate_block_plan lv dfg (cfg_analyze fn) fn pb psBefore = SOME (ops,psAfter) /\
    ps.ps_stack = psAfter.ps_stack /\ ps.ps_spilled = psAfter.ps_spilled
Proof
  rpt strip_tac >> gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_reachable_origin) >>
  disch_then drule >> simp[] >> strip_tac >> gvs[]
QED

Theorem lineage_state_reachable:
  !lv dfg fn ps0 lbl ps.
  wf_function fn /\ lineage_state lv dfg (cfg_analyze fn) fn ps0 lbl ps ==>
  cfg_reachable_of (cfg_analyze fn) lbl
Proof
  rpt gen_tac >> strip_tac >>
  drule lineage_state_dfs_fields >> strip_tac >>
  drule_all dfs_block_state_reachable >> simp[]
QED

Theorem lineage_state_reachable_predecessor_origin:
  !lv dfg fn ps0 lbl ps.
  wf_function fn /\ lineage_state lv dfg (cfg_analyze fn) fn ps0 lbl ps /\
  fn_entry_label fn <> SOME lbl ==>
  ?pred pb psBefore ops psAfter.
    cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    generate_block_plan lv dfg (cfg_analyze fn) fn pb psBefore = SOME (ops,psAfter) /\
    ps.ps_stack = psAfter.ps_stack /\ ps.ps_spilled = psAfter.ps_spilled
Proof
  rpt strip_tac >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  simp[Once lineage_state_cases] >> strip_tac >> gvs[] >>
  drule_all lineage_state_reachable >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Native incoming join states inherit the successful predecessor boundary.
   This leaves the stack prefix unconstrained. *)
Theorem lineage_state_join_boundary:
  codegen_ready_fn fn /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  fn_entry_label fn <> SOME succ /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ ps ==>
  ps.ps_spilled = FEMPTY /\
  ?pred prefix.
    MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
    ps.ps_stack = prefix ++ MAP Var
      (input_vars_from pred sb.bb_instructions
        (live_vars_at (liveness_analyze fn) succ 0))
Proof
  strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all lineage_state_reachable_predecessor_origin >> strip_tac >>
  drule_all analyzed_join_edge_spilled_empty >> strip_tac >>
  drule_all generate_block_plan_join_edge_suffix >> strip_tac >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`pred`, `prefix`] >> simp[]
QED

Theorem dfs_block_state_join_boundary:
  codegen_ready_fn fn /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  fn_entry_label fn <> SOME succ /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ ps ==>
  ps.ps_spilled = FEMPTY /\
  ?pred prefix.
    MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
    ps.ps_stack = prefix ++ MAP Var
      (input_vars_from pred sb.bb_instructions
        (live_vars_at (liveness_analyze fn) succ 0))
Proof
  strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  drule_all dfs_block_state_reachable_predecessor_origin >> strip_tac >>
  drule_all analyzed_join_edge_spilled_empty >> strip_tac >>
  drule_all generate_block_plan_join_edge_suffix >> strip_tac >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`pred`, `prefix`] >> simp[]
QED

Theorem dfs_block_state_native_phi_coverage:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ ps ==>
  ?pred. MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
    (!i. i < LENGTH (collect_phis sb.bb_instructions) ==>
      ?op. MEM op ps.ps_stack /\
        native_phi_class pred (collect_phis sb.bb_instructions) op = SOME i)
Proof
  strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  `fn_reachable fn succ` by
    metis_tac[fn_reachable_cfg_analyze, dfs_block_state_reachable] >>
  `fn_entry_label fn <> SOME succ` by simp[] >>
  drule_all dfs_block_state_reachable_predecessor_origin >> strip_tac >>
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    successful_join_edge_native_phi_coverage >>
  disch_then (qspecl_then [`succ`, `sb`, `pred`, `entry`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem lineage_state_native_phi_coverage:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ ps ==>
  ?pred. MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
    (!i. i < LENGTH (collect_phis sb.bb_instructions) ==>
      ?op. MEM op ps.ps_stack /\
        native_phi_class pred (collect_phis sb.bb_instructions) op = SOME i)
Proof
  strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  `fn_reachable fn succ` by
    metis_tac[fn_reachable_cfg_analyze, lineage_state_reachable] >>
  `fn_entry_label fn <> SOME succ` by simp[] >>
  drule_all lineage_state_reachable_predecessor_origin >> strip_tac >>
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    successful_join_edge_native_phi_coverage >>
  disch_then (qspecl_then [`succ`, `sb`, `pred`, `entry`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem lineage_dfs_join_phi_schedule_ready:
  !fn entry succ sb dfg ps0 psL psD halting.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ psD ==>
  ?pred cells prefixL prefixD cells_end.
    MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
    phi_origin_classes (native_phi_class pred (collect_phis sb.bb_instructions)) cells /\
    psL.ps_stack = prefixL ++ MAP (phi_cell_value T) cells /\
    psD.ps_stack = prefixD ++ MAP (phi_cell_value F) cells /\
    phi_origin_schedule_ready
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) prefixL prefixD cells cells_end /\
    phi_origin_classes (native_phi_class pred (collect_phis sb.bb_instructions)) cells_end
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  `fn_entry_label fn <> SOME succ` by simp[] >>
  `fn_reachable fn succ` by
    metis_tac[fn_reachable_cfg_analyze, lineage_state_reachable] >>
  drule_all lineage_state_reachable_predecessor_origin >> strip_tac >>
  drule_all dfs_block_state_reachable_predecessor_origin >> strip_tac >>
  `?cells prefixP prefixQ cells_end.
    phi_origin_classes (native_phi_class pred (collect_phis sb.bb_instructions)) cells /\
    psAfter.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
    psAfter'.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells /\
    MAP (phi_cell_value T) cells = MAP Var
      (input_vars_from pred sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0)) /\
    phi_origin_schedule_ready
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) prefixP prefixQ cells cells_end /\
    phi_origin_classes (native_phi_class pred (collect_phis sb.bb_instructions)) cells_end` by
    (irule successful_join_edges_phi_schedule_ready >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`dfg`, `ops`, `ops'`, `psBefore`, `psBefore'`, `pred'`, `pb'`] >> simp[]) >>
  qexistsl_tac [`pred`, `cells`, `prefixP`, `prefixQ`, `cells_end`] >> simp[]
QED

Theorem lineage_dfs_join_phi_state_replay:
  !fn entry succ sb dfg ps0 psL psD halting rsL rsD.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ psD /\
  rsL.ps_stack = psL.ps_stack /\ rsD.ps_stack = psD.ps_stack /\
  rsL.ps_alloc = rsD.ps_alloc ==>
  ?cells_end prefixL prefixD ops al.
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) rsL =
      (ops, rsL with <|ps_stack := prefixL ++ MAP (phi_cell_value T) cells_end; ps_alloc := al|>) /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) rsD =
      (ops, rsD with <|ps_stack := prefixD ++ MAP (phi_cell_value F) cells_end; ps_alloc := al|>)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_dfs_join_phi_schedule_ready >>
  disch_then (qspec_then `halting` strip_assume_tac) >>
  `rsL.ps_stack = prefixL ++ MAP (phi_cell_value T) cells /\
   rsD.ps_stack = prefixD ++ MAP (phi_cell_value F) cells` by simp[] >>
  drule_all phi_origin_schedule_state_replay >> strip_tac >>
  qexistsl_tac [`cells_end`, `prefixL`, `prefixD`, `ops`, `al`] >> simp[]
QED

Theorem lineage_dfs_join_phi_common_suffix:
  !fn entry succ sb dfg ps0 psL psD halting rsL rsD.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ psD /\
  rsL.ps_stack = psL.ps_stack /\ rsD.ps_stack = psD.ps_stack /\
  rsL.ps_alloc = rsD.ps_alloc ==>
  ?prefixL prefixD suffix ops al.
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) rsL =
      (ops, rsL with <|ps_stack := prefixL ++ suffix; ps_alloc := al|>) /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) rsD =
      (ops, rsD with <|ps_stack := prefixD ++ suffix; ps_alloc := al|>) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
        (LENGTH (collect_phis sb.bb_instructions))) ==> MEM (Var v) suffix) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
        (LENGTH (collect_phis sb.bb_instructions))) ==> LIST_ELEM_COUNT (Var v) suffix = 1)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  `fn_entry_label fn <> SOME succ` by simp[] >>
  `fn_reachable fn succ` by
    metis_tac[fn_reachable_cfg_analyze, lineage_state_reachable] >>
  drule_all lineage_state_reachable_predecessor_origin >> strip_tac >>
  drule_all dfs_block_state_reachable_predecessor_origin >> strip_tac >>
  irule successful_join_edges_phi_common_suffix_rebased >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem lineage_dfs_join_phi_common_suffix_actual:
  !fn entry succ sb dfg ch growth spill_base lbl_ctr fn_ops ps_end psL psD halting.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psD ==>
  ?prefixL prefixD suffix ops al.
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) psL =
      (ops, psL with <|ps_stack := prefixL ++ suffix; ps_alloc := al|>) /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) psD =
      (ops, psD with <|ps_stack := prefixD ++ suffix; ps_alloc := al|>) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
        (LENGTH (collect_phis sb.bb_instructions))) ==> MEM (Var v) suffix) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
        (LENGTH (collect_phis sb.bb_instructions))) ==> LIST_ELEM_COUNT (Var v) suffix = 1)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_actual_dfs_alloc >> strip_tac >>
  irule lineage_dfs_join_phi_common_suffix >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem lineage_dfs_join_common_cells:
  !fn succ sb dfg ps0 psL psD.
  codegen_ready_fn fn /\ lookup_block succ fn.fn_blocks = SOME sb /\
  fn_entry_label fn <> SOME succ /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ psD ==>
  ?pred cells prefixL prefixD.
    MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
    phi_origin_classes (native_phi_class pred (collect_phis sb.bb_instructions)) cells /\
    psL.ps_stack = prefixL ++ MAP (phi_cell_value T) cells /\
    psD.ps_stack = prefixD ++ MAP (phi_cell_value F) cells
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_predecessor_origin >> strip_tac >>
  drule_all dfs_block_state_predecessor_origin >> strip_tac >>
  `?cells prefixL prefixD.
    phi_origin_classes (native_phi_class pred (collect_phis sb.bb_instructions)) cells /\
    psAfter.ps_stack = prefixL ++ MAP (phi_cell_value T) cells /\
    psAfter'.ps_stack = prefixD ++ MAP (phi_cell_value F) cells` by
    (irule successful_join_edges_common_cells >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any)) >>
  qexistsl_tac [`pred`, `cells`, `prefixL`, `prefixD`] >> simp[]
QED

(* Entering block succ from block pred: the step rule of lineage_state with
   the predecessor named, so a caller can tie it to the run-time
   vs_prev_bb (the PHI values at succ's entry depend on which edge). *)
Definition lineage_entry_def:
  lineage_entry liveness dfg cfg fn ps0 pred succ ps <=>
    ?ps_pred bb ps_dfs block_ops ps_dfs_after ch promised ps_after ps_succ.
      lineage_state liveness dfg cfg fn ps0 pred ps_pred /\
      lookup_block pred fn.fn_blocks = SOME bb /\
      dfs_block_state liveness dfg cfg fn ps0 pred ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb ps_dfs =
        SOME (block_ops, ps_dfs_after) /\
      generate_block_plan liveness dfg cfg fn bb
        (ps_pred with <| ps_cleanup_height := ch;
                         ps_cleanup_promised := promised |>) =
        SOME (block_ops, ps_after) /\
      MEM succ (cfg_succs_of cfg pred) /\
      dfs_block_state liveness dfg cfg fn ps0 succ ps_succ /\
      ps_after.ps_spilled = ps_succ.ps_spilled /\
      ps = ps_succ with <| ps_stack := ps_after.ps_stack;
                           ps_spilled := ps_after.ps_spilled |>
End

(* Helper: a lineage entry is a lineage state of its successor. *)
Theorem lineage_entry_lineage_state:
  !liveness dfg cfg fn ps0 pred succ ps.
    lineage_entry liveness dfg cfg fn ps0 pred succ ps ==>
    lineage_state liveness dfg cfg fn ps0 succ ps
Proof
  rw[lineage_entry_def] >> irule lineage_state_step >> metis_tac[]
QED

(* Positive availability is quantified over every successful cleanup override.
   The setup equation names the actual worker start, not a chosen replay. *)
Theorem lineage_state_successful_run_available:
  !fn dfg ch growth spill_base lbl_ctr entry.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry ==>
    !lbl ps.
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps ==>
    !h promised bb ops after setup_ops start.
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    (if bb = HD fn.fn_blocks then
       prepare_params_plan (liveness_analyze fn) fn
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) ==>
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) /\
    (!k qs v. LENGTH (collect_phis bb.bb_instructions) <= k /\
      k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
      MEM (Var v) (compute_operands
        (EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
    (!k qs v. LENGTH (collect_phis bb.bb_instructions) <= k /\
      k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac lineage_state_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `fn.fn_blocks <> [] /\ lbl = (HD fn.fn_blocks).bb_label` by
        (Cases_on `fn.fn_blocks` >>
         gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def]) >>
      `bb = HD fn.fn_blocks` by
        (Cases_on `fn.fn_blocks` >> gvs[venomInstTheory.lookup_block_def, listTheory.FIND_thm]) >>
      gvs[] >>
      drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
        initialized_entry_block_available >>
      simp[init_cleanup_plan_state_def, init_plan_state_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl /\ fn_reachable fn lbl'` by
    metis_tac[dfs_block_state_reachable, fn_reachable_cfg_analyze] >>
  `MEM lbl (cfg_preds_of (cfg_analyze fn) lbl')` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  `lbl' <> entry` by
    (strip_tac >> gvs[] >>
     `cfg_preds_of (cfg_analyze fn) entry = []` by
       (Cases_on `fn.fn_blocks` >>
        gvs[codegen_ready_fn_def, block_entries_ready_def,
            venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def, listTheory.NULL_EQ]) >>
     gvs[]) >>
  `bb' <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `EVERY (\v. MEM (Var v) ps_after.ps_stack \/ Var v IN FDOM ps_after.ps_spilled)
    (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))` by
    (first_x_assum (qspecl_then [`ch'`,`promised`,`bb`,`block_ops`,`ps_after`] mp_tac) >>
     simp[listTheory.EVERY_MEM] >> metis_tac[pairTheory.PAIR]) >>
  gvs[] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] incoming_edge_block_available) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem lineage_state_live_out_available:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps h promised bb ops after.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lineage_state _ _ _ _ _ _ _`) lineage_state_successful_run_available >>
  disch_then (qspecl_then [`entry`,`h`,`promised`,`bb`,`ops`,`after`] mp_tac) >>
  simp[] >> metis_tac[pairTheory.PAIR]
QED

Theorem lineage_state_ordinary_prefix_available:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps h promised bb ops after setup_ops start k qs v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    (if bb = HD fn.fn_blocks then
       prepare_params_plan (liveness_analyze fn) fn
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    LENGTH (collect_phis bb.bb_instructions) <= k /\ k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    MEM (Var v) (compute_operands
      (EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions)) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lineage_state _ _ _ _ _ _ _`) lineage_state_successful_run_available >>
  disch_then (qspecl_then [`entry`,`h`,`promised`,`bb`,`ops`,`after`,`setup_ops`,`start`] mp_tac) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem lineage_state_ordinary_prefix_live_available:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps h promised bb ops after setup_ops start k qs v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    (if bb = HD fn.fn_blocks then
       prepare_params_plan (liveness_analyze fn) fn
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    LENGTH (collect_phis bb.bb_instructions) <= k /\ k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (get_params bb.bb_instructions)+k)) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lineage_state _ _ _ _ _ _ _`) lineage_state_successful_run_available >>
  disch_then (qspecl_then [`entry`,`h`,`promised`,`bb`,`ops`,`after`,`setup_ops`,`start`] mp_tac) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

(* Choosing the current cleanup fields gives the unmodified actual run. *)
Theorem lineage_state_block_live_out_available:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb ops after.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb ps =
      SOME (ops,after) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >> irule lineage_state_live_out_available >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ps.ps_cleanup_height`,`ops`,`ps.ps_cleanup_promised`] >> simp[]
QED

Theorem dfs_block_state_live_out_available:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps h promised bb ops after.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule dfs_block_state_lineage_state >> strip_tac >>
  rpt strip_tac >> irule lineage_state_live_out_available >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem dfs_block_state_block_live_out_available:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb ops after.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb ps =
      SOME (ops,after) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule dfs_block_state_lineage_state >> strip_tac >>
  metis_tac[lineage_state_block_live_out_available]
QED

Theorem dfs_block_state_ordinary_prefix_available:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps h promised bb ops after setup_ops start k qs v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    (if bb = HD fn.fn_blocks then
       prepare_params_plan (liveness_analyze fn) fn
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    LENGTH (collect_phis bb.bb_instructions) <= k /\ k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    MEM (Var v) (compute_operands
      (EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions)) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule dfs_block_state_lineage_state >> strip_tac >>
  irule lineage_state_ordinary_prefix_available >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[]
QED

(* ===== Successor transfer ===== *)

(* Successful native run boundary, independent of any resource observer. *)
Theorem lineage_state_block_native_run:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) ==>
    MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl /\
    ?entry setup_ops start.
      fn_entry_label fn = SOME entry /\
      (if bb = HD fn.fn_blocks then
         prepare_params_plan (liveness_analyze fn) fn
           (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
       else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
         clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
           (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
       else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
        (setup_ops,start) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) start
        (LENGTH (non_param_insts bb)) after /\
      (!j before w. j < LENGTH (non_param_insts bb) /\
        LENGTH (collect_phis bb.bb_instructions) <= j /\
        native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
          (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
          (LENGTH bb.bb_instructions) (non_param_insts bb) start j before ==>
        (MEM w (live_vars_at (liveness_analyze fn) lbl
          (LENGTH (get_params bb.bb_instructions)+j)) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
        (MEM (Var w) (compute_operands (EL j (non_param_insts bb))) ==>
          MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled))
Proof
  rpt gen_tac >> strip_tac >>
  `?entry. fn_entry_label fn = SOME entry` by metis_tac[lineage_state_has_entry] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
              venomExecPropsTheory.lookup_block_label] >>
  `fn_reachable fn lbl` by
    metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  simp[] >>
  qabbrev_tac `input = ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>` >>
  Cases_on `if bb = HD fn.fn_blocks then prepare_params_plan (liveness_analyze fn) fn input
    else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
      clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb input
    else ([],input)` >>
  rename1 `_ = (setup_ops,start)` >>
  `?worker_ops. generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
    lbl (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) 0 (non_param_insts bb) start = SOME (worker_ops,after)` by
    (`fn.fn_blocks <> []` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
     `cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = []` by
       metis_tac[fnPlanLineageCallersTheory.ready_entry_no_clean] >>
     Cases_on `bb = HD fn.fn_blocks`
     >- (gvs[] >> qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
         simp[generate_block_plan_def] >> gvs[AllCaseEqs()] >> metis_tac[]) >>
     Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1` >> gvs[] >>
     qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_block_plan_def] >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  drule fnPlanLineageEntryProductionTheory.native_worker_prefix_endpoint >> strip_tac >>
  qexistsl_tac [`setup_ops`,`start`] >> simp[] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >> irule lineage_state_ordinary_prefix_live_available >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      gvs[Abbr `input`, arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  strip_tac >>
  `EL j (non_param_insts bb) =
     EL (LENGTH (get_params bb.bb_instructions)+j) bb.bb_instructions` by
    metis_tac[fnPlanLineageCallersTheory.ready_block_suffix_index] >>
  irule lineage_state_ordinary_prefix_available >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[Abbr `input`, arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Theorem ready_parameter_output_head_mem:
  !fn bb inst.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM inst (get_params bb.bb_instructions) ==>
    MEM (HD inst.inst_outputs) inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule fnPlanLineageObserverTransportTheory.get_params_mem >> strip_tac >>
  `inst_wf inst` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def,
         listTheory.EVERY_MEM] >> metis_tac[]) >>
  `LENGTH inst.inst_outputs = 1` by
    (Cases_on `inst.inst_opcode` >>
     gvs[venomInstTheory.is_param_opcode_def, venomWfTheory.inst_wf_def]) >>
  gvs[listTheory.LENGTH_EQ_NUM_compute]
QED

Theorem lineage_state_block_nondefining_observer_bound:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after v b.
    b <= 1 /\ codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= b ==>
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= b
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_block_native_run >> strip_tac >>
  qabbrev_tac `input = ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>` >>
  `LIST_ELEM_COUNT (Var v) start.ps_stack +
     (if Var v IN FDOM start.ps_spilled then 1 else 0) <= b` by
    (Cases_on `bb = HD fn.fn_blocks`
     >- (gvs[] >>
         `EVERY (\inst. v <> HD inst.inst_outputs)
            (get_params (HD fn.fn_blocks).bb_instructions)` by
           (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
            `MEM (HD fn.fn_blocks) fn.fn_blocks` by
              (Cases_on `fn.fn_blocks` >> gvs[codegen_ready_fn_def]) >>
            drule_all ready_parameter_output_head_mem >>
            metis_tac[fnPlanLineageObserverTransportTheory.get_params_mem]) >>
         drule_all fnPlanLineageObserverTransportTheory.prepare_params_plan_nondefining_resource_nonincrease >>
         simp[Abbr `input`] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1` >> gvs[]
     >- (drule fnPlanLineageObserverTransportTheory.clean_stack_plan_resource_nonincrease >>
         disch_then (qspec_then `v` mp_tac) >> simp[Abbr `input`] >>
         metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     gvs[Abbr `input`]) >>
  drule fnPlanLineageObserverTransportTheory.native_inst_prefix_nondefining_observer_bound >>
  disch_then (qspecl_then [`bb`,`v`,`b`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!j before w. _` (qspecl_then [`j`,`before`,`w`] mp_tac) >>
    simp[arithmeticTheory.ADD_COMM])) >> simp[]
QED

Theorem lineage_state_block_fresh_output_resource_bound:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after v.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled ==>
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_block_native_run >> strip_tac >>
  `LIST_ELEM_COUNT (Var v) ps.ps_stack = 0` by
    simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff] >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  drule_all fnPlanLineageCallersTheory.ssa_form_block_outputs_distinct >>
  `bb.bb_instructions = get_params bb.bb_instructions ++ non_param_insts bb` by
    metis_tac[fnPlanLineageCallersTheory.ready_block_parameter_suffix] >>
  disch_then (fn th => mp_tac th) >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
  simp[listTheory.MAP_APPEND, listTheory.FLAT_APPEND, listTheory.ALL_DISTINCT_APPEND] >> strip_tac >>
  `?b. b <= 1 /\
    (EXISTS (\i. MEM v i.inst_outputs) (non_param_insts bb) ==> b = 0) /\
    LIST_ELEM_COUNT (Var v) start.ps_stack +
      (if Var v IN FDOM start.ps_spilled then 1 else 0) <= b` by
    (Cases_on `bb = HD fn.fn_blocks`
     >- (gvs[] >>
         Cases_on `EXISTS (\i. MEM v i.inst_outputs) (get_params (HD fn.fn_blocks).bb_instructions)`
         >- (qexists_tac `1` >> simp[] >> conj_tac
             >- (gvs[listTheory.EXISTS_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP,
                     listTheory.EVERY_MEM, combinTheory.o_DEF] >> metis_tac[]) >>
             irule fnPlanLineageObserverTransportTheory.prepare_params_plan_fresh_output_resource_bound >>
             goal_assum (drule_at Any) >> simp[] >>
             irule fnPlanLineageSetupTheory.ready_parameter_names_distinct >>
             simp[] >> Cases_on `fn.fn_blocks` >> gvs[]) >>
         qexists_tac `0` >> simp[] >>
         drule fnPlanLineageObserverTransportTheory.prepare_params_plan_nondefining_resource_nonincrease >>
         disch_then (qspec_then `v` mp_tac) >>
         impl_tac
         >- (gvs[listTheory.EXISTS_MEM, listTheory.EVERY_MEM] >> rpt strip_tac >>
             `MEM (HD fn.fn_blocks) fn.fn_blocks` by
               (Cases_on `fn.fn_blocks` >> gvs[codegen_ready_fn_def]) >>
             drule_all ready_parameter_output_head_mem >> metis_tac[]) >>
         simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff,
              fnPlanLineageObserverTransportTheory.indicator_zero_iff]) >>
     qexists_tac `0` >> simp[] >>
     Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1` >> gvs[] >>
     drule fnPlanLineageObserverTransportTheory.clean_stack_plan_resource_nonincrease >>
     disch_then (qspec_then `v` mp_tac) >>
     simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff,
          fnPlanLineageObserverTransportTheory.indicator_zero_iff]) >>
  drule fnPlanLineageObserverTransportTheory.native_inst_prefix_phase_resource_bound >>
  disch_then (qspecl_then [`bb`,`v`,`b`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!j before w. _` (qspecl_then [`j`,`before`,`w`] mp_tac) >>
    simp[arithmeticTheory.ADD_COMM])) >>
  Cases_on `b = 1 \/ EXISTS (\i. MEM v i.inst_outputs) (non_param_insts bb)` >>
  simp[] >> strip_tac >> decide_tac
QED

Theorem lineage_state_block_nondefining_observer_upper:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after v.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 ==>
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  irule lineage_state_block_nondefining_observer_bound >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem lineage_state_block_nondefining_absent:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after v.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled ==>
    ~MEM (Var v) after.ps_stack /\ Var v NOTIN FDOM after.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[GSYM fnPlanLineageObserverTransportTheory.resource_zero_iff_absent] >>
  irule lineage_state_block_nondefining_observer_bound >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff,
       fnPlanLineageObserverTransportTheory.indicator_zero_iff] >> metis_tac[]
QED

Theorem lineage_history_nondefining_observer_upper:
  !fn dfg ch growth spill_base lbl_ctr.
    codegen_ready_fn fn ==>
    !vertices a b v.
      lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) (FST a) (SND a) /\
      LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices a b /\
      EVERY (\vertex. !bb. lookup_block (FST vertex) fn.fn_blocks = SOME bb ==>
        EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions) vertices /\
      LIST_ELEM_COUNT (Var v) (SND a).ps_stack +
        (if Var v IN FDOM (SND a).ps_spilled then 1 else 0) <= 1 ==>
      LIST_ELEM_COUNT (Var v) (SND b).ps_stack +
        (if Var v IN FDOM (SND b).ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >> Induct >> simp[listTheory.LRC_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on `h` >> PairCases_on `z` >> gvs[] >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) z0 z1` by
    metis_tac[lineage_edge_step] >>
  drule lineage_edge_physical >> strip_tac >>
  `EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions` by metis_tac[] >>
  `LIST_ELEM_COUNT (Var v) z1.ps_stack +
    (if Var v IN FDOM z1.ps_spilled then 1 else 0) <= 1` by
    (gvs[] >> irule lineage_state_block_nondefining_observer_upper >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> qexists_tac `(z0,z1)` >> gvs[]
QED

Theorem lineage_history_nondefining_absent:
  !fn dfg ch growth spill_base lbl_ctr.
    codegen_ready_fn fn ==>
    !vertices a b v.
      lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) (FST a) (SND a) /\
      LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices a b /\
      EVERY (\vertex. !bb. lookup_block (FST vertex) fn.fn_blocks = SOME bb ==>
        EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions) vertices /\
      ~MEM (Var v) (SND a).ps_stack /\ Var v NOTIN FDOM (SND a).ps_spilled ==>
      ~MEM (Var v) (SND b).ps_stack /\ Var v NOTIN FDOM (SND b).ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Induct >> simp[listTheory.LRC_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on `h` >> PairCases_on `z` >> gvs[] >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) z0 z1` by
    metis_tac[lineage_edge_step] >>
  drule lineage_edge_physical >> strip_tac >>
  `EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions` by metis_tac[] >>
  `~MEM (Var v) z1.ps_stack /\ Var v NOTIN FDOM z1.ps_spilled` by
    (gvs[] >> irule lineage_state_block_nondefining_absent >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> qexists_tac `(z0,z1)` >> gvs[]
QED

(* A label-avoiding actual history has not executed this definition yet.
   Returning histories need a separate extinction argument. *)
Theorem lineage_history_first_arrival_output_absent:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb inst v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn` by
    gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def] >>
  `EVERY (\vertex. !other.
     lookup_block (FST vertex) fn.fn_blocks = SOME other ==>
     EVERY (\i. ~MEM v i.inst_outputs) other.bb_instructions) vertices` by
    (simp[Once listTheory.EVERY_MEM] >> rpt strip_tac >>
     `FST vertex <> lbl` by
       (strip_tac >>
        qpat_x_assum `~MEM lbl (MAP FST vertices)` mp_tac >>
        simp[listTheory.MEM_MAP] >> qexists_tac `vertex` >> simp[]) >>
     metis_tac[fnPlanLineagePathTheory.ssa_output_other_block_no_outputs]) >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) entry
     (init_cleanup_plan_state ch growth spill_base lbl_ctr)` by
    simp[lineage_state_entry] >>
  drule lineage_history_nondefining_absent >>
  disch_then (drule_at Any) >> simp[] >>
  disch_then (drule_at Any) >> simp[]
QED

Theorem lineage_history_first_arrival_output_resource_bound:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb inst v h promised ops after.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) ==>
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_history_first_arrival_output_absent >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    (drule lineage_history_reconstruct >> simp[] >>
     disch_then irule >> simp[lineage_state_entry]) >>
  irule lineage_state_block_fresh_output_resource_bound >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem lineage_state_ordinary_last_use_extinction:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps h promised bb ops after
   setup_ops start k qs inst nl iops last v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    (if bb = HD fn.fn_blocks then
       prepare_params_plan (liveness_analyze fn) fn
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    LENGTH (collect_phis bb.bb_instructions) <= k /\ k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    inst = EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions /\
    nl = live_vars_at (liveness_analyze fn) lbl
      (SUC (LENGTH (get_params bb.bb_instructions)+k)) /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> PHI /\
    ~is_param_opcode inst.inst_opcode /\
    MEM (Var v) (compute_operands inst) /\ ~MEM v nl /\ ~MEM v inst.inst_outputs /\
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1 /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst nl
      (bb_is_halting bb)
      (SUC (LENGTH (get_params bb.bb_instructions)+k) = LENGTH bb.bb_instructions)
      lbl qs = SOME (iops,last)
    ==> ~MEM (Var v) last.ps_stack /\ Var v NOTIN FDOM last.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `!w. MEM (Var w) (compute_operands inst) ==>
    MEM (Var w) qs.ps_stack \/ Var w IN FDOM qs.ps_spilled` by
    (rpt strip_tac >> irule lineage_state_ordinary_prefix_available >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> gvs[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  `inst = EL k (non_param_insts bb)` by metis_tac[fnPlanLineageCallersTheory.ready_block_suffix_index] >>
  `MEM inst (non_param_insts bb)` by metis_tac[listTheory.EL_MEM] >>
  `MEM inst bb.bb_instructions` by gvs[non_param_insts_def, listTheory.MEM_FILTER] >>
  `inst_wf inst /\ codegen_ready_inst inst` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    fnPlanLineageSetupTheory.native_inst_last_use_extinction >> simp[] >> gvs[]
QED

Theorem dfs_block_state_ordinary_last_use_extinction:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps h promised bb ops after
   setup_ops start k qs inst nl iops last v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    (if bb = HD fn.fn_blocks then
       prepare_params_plan (liveness_analyze fn) fn
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    LENGTH (collect_phis bb.bb_instructions) <= k /\ k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    inst = EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions /\
    nl = live_vars_at (liveness_analyze fn) lbl
      (SUC (LENGTH (get_params bb.bb_instructions)+k)) /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> PHI /\
    ~is_param_opcode inst.inst_opcode /\
    MEM (Var v) (compute_operands inst) /\ ~MEM v nl /\ ~MEM v inst.inst_outputs /\
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1 /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn inst nl
      (bb_is_halting bb)
      (SUC (LENGTH (get_params bb.bb_instructions)+k) = LENGTH bb.bb_instructions)
      lbl qs = SOME (iops,last)
    ==> ~MEM (Var v) last.ps_stack /\ Var v NOTIN FDOM last.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule dfs_block_state_lineage_state >> strip_tac >>
  irule lineage_state_ordinary_last_use_extinction >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> gvs[] >> metis_tac[]
QED

Theorem lineage_state_incoming_block_dead_stack:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after pred v.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    ~MEM (Var v) ps.ps_stack /\
    ~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0)) /\
    EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions ==>
    ~MEM (Var v) after.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_block_native_run >> strip_tac >>
  `bb <> HD fn.fn_blocks` by
    (irule fnPlanLineageObserverTransportTheory.ready_incoming_block_nonentry >>
     simp[] >> qexists_tac `pred` >> simp[]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageEntryProductionTheory.nonentry_block_no_params >>
     gvs[codegen_ready_fn_def] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `!j before w. _` kall_tac >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac
       fnPlanLineageLivenessTheory.collect_phis_prefix >>
     metis_tac[listTheory.LENGTH_APPEND, arithmeticTheory.LESS_EQ_ADD]) >>
  `~MEM (Var v) (ps with <|ps_cleanup_height := h;
     ps_cleanup_promised := promised|>).ps_stack` by simp[] >>
  `!j. j < LENGTH bb.bb_instructions ==>
    ~MEM v (EL j bb.bb_instructions).inst_outputs` by
    gvs[listTheory.EVERY_EL] >>
  qspecl_then [`fn`, `bb`] mp_tac
    fnPlanLineageObserverTransportTheory.native_incoming_prefix_dead_stack >>
  simp[] >>
  disch_then (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem lineage_edge_incoming_dead_stack:
  !fn dfg ch growth spill_base lbl_ctr lbl ps succ qs pred v.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) (succ,qs) /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    ~MEM (Var v) ps.ps_stack /\
    (!bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      ~MEM v (input_vars_from pred bb.bb_instructions
        (live_vars_at (liveness_analyze fn) lbl 0)) /\
      EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions) ==>
    ~MEM (Var v) qs.ps_stack /\ MEM succ (cfg_succs_of (cfg_analyze fn) lbl) /\
    (!sb. lookup_block succ fn.fn_blocks = SOME sb ==>
      ~MEM v (input_vars_from lbl sb.bb_instructions
        (live_vars_at (liveness_analyze fn) succ 0)))
Proof
  rpt gen_tac >> strip_tac >>
  drule lineage_edge_physical >> strip_tac >>
  `~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0)) /\
    EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions` by metis_tac[] >>
  `~MEM (Var v) after.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))` by
    (irule lineage_state_incoming_block_dead_stack >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze] >>
  drule_all fnPlanLineageLivenessTheory.analyzed_live_out_edge_subset >>
  simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem lineage_history_incoming_dead_stack:
  !fn dfg ch growth spill_base lbl_ctr.
    codegen_ready_fn fn ==>
    !vertices a b pred v.
      lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) (FST a) (SND a) /\
      LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices a b /\
      MEM (FST a) (cfg_succs_of (cfg_analyze fn) pred) /\
      ~MEM (Var v) (SND a).ps_stack /\
      (!bb. lookup_block (FST a) fn.fn_blocks = SOME bb ==>
        ~MEM v (input_vars_from pred bb.bb_instructions
          (live_vars_at (liveness_analyze fn) (FST a) 0))) /\
      EVERY (\vertex. !bb. lookup_block (FST vertex) fn.fn_blocks = SOME bb ==>
        EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions) vertices ==>
      ~MEM (Var v) (SND b).ps_stack /\
      ?last_pred. MEM (FST b) (cfg_succs_of (cfg_analyze fn) last_pred) /\
        (!bb. lookup_block (FST b) fn.fn_blocks = SOME bb ==>
          ~MEM v (input_vars_from last_pred bb.bb_instructions
            (live_vars_at (liveness_analyze fn) (FST b) 0)))
Proof
  rpt gen_tac >> strip_tac >> Induct >> simp[listTheory.LRC_def]
  >- (rpt strip_tac >> qexists_tac `pred` >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on `h` >> PairCases_on `z` >> gvs[] >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) z0 z1` by
    metis_tac[lineage_edge_step] >>
  `~MEM (Var v) z1.ps_stack /\ MEM z0 (cfg_succs_of (cfg_analyze fn) h0) /\
    (!sb. lookup_block z0 fn.fn_blocks = SOME sb ==>
      ~MEM v (input_vars_from h0 sb.bb_instructions
        (live_vars_at (liveness_analyze fn) z0 0)))` by
    (irule lineage_edge_incoming_dead_stack >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`(z0,z1)`, `h0`] >> gvs[]
QED

(* KEY LEMMA (cheated, for alan): a lineage state regenerates the block's
   DFS code, so the code at the block's label is the plan of a state that
   carries the run-time path's stack and spill map.  With the cleanup
   fields taken from the DFS state the code can differ: entered from a
   predecessor whose path elided a cleanup, the stack carries more
   dead_stack_marker entries than on the DFS path, and a later
   clean_stack_plan whose DFS state has no promise may fail its height
   test only on the run-time path; hence the existential h, promised.

   Why it should hold: lineage and DFS states share alloc, label counter
   and the planner inputs.  The entry block has no predecessors
   (block_entries_ready), so its only lineage state is the initial one.  At
   a join every predecessor ends in a JMP (block_entries_ready), whose
   reorder produces the target stack with no spills left, so the stacks
   agree except for a bottom prefix of dead_stack_marker entries and, before
   the PHI prefix, the names at PHI slots (phi_operands_ready makes the PHI
   code the same).  No operand of the function is a dead_stack_marker, so
   the operand searches never stop in that prefix.  Along other edges the
   induction carries the agreement.

   The planner does not fail on an operand missing from the stack, so the
   agreement alone does not carry through: the length-dependent branches
   (reorder_one's final_dist < LENGTH, stack_swap's truncated index) need
   an invariant of lineage states, e.g. ps_stack is a dead_stack_marker
   prefix followed by distinct variables, disjoint from FDOM ps_spilled,
   which together are the live set at the edge (at a join entry: exactly
   input_vars_from P lbl (live_vars_at liveness lbl 0), in that order, with
   ps_spilled = FEMPTY).  That invariant is static (planner against
   liveness_analyze; livenessAnalysisProps, livenessConvergenceProofs), not
   about execution.  Every DFS state is also a lineage state, since
   generate_succs_plan restores the parent's stack and spill map. *)
Theorem lineage_state_block_plan:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb
   ps ps_dfs block_ops ps_dfs_after.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after)
    ==>
    ?h promised ps_after.
      generate_block_plan liveness dfg cfg fn bb
        (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
        SOME (block_ops, ps_after) /\
      ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
      ps_after.ps_spilled = ps_dfs_after.ps_spilled
Proof
  cheat
QED
