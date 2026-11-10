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

Theorem dfs_block_state_defining_outputs_absent:
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps ==>
  EVERY (\inst. EVERY (\v. ~MEM (Var v) ps.ps_stack /\
    Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs) bb.bb_instructions
Proof
  strip_tac >> Cases_on `fn_entry_label fn = SOME lbl`
  >- (drule_all dfs_block_state_initialized_trace >> strip_tac >>
      `MEM (lbl,init_cleanup_plan_state ch growth spill_base lbl_ctr) events` by
        (drule plan_aux_trace_fresh_event >> gvs[]) >>
      `ps = init_cleanup_plan_state ch growth spill_base lbl_ctr` by
        metis_tac[plan_aux_trace_event_unique, listTheory.MEM_APPEND, listTheory.MEM] >>
      gvs[init_cleanup_plan_state_def, init_plan_state_def]) >>
  drule_all dfs_block_state_native_incoming >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ ssa_form fn` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, codegen_ready_fn_def] >>
  gvs[chronological_support_def, listTheory.EVERY_MEM] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  `MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled` by metis_tac[] >>
  `?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\ MEM db.bb_label visited` by metis_tac[] >>
  drule_all fnPlanLineagePathTheory.visited_definition_fresh_block_outputs >>
  disch_then assume_tac >> gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem lineage_state_defining_outputs_spill_absent:
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps ==>
  EVERY (\inst. EVERY (\v. Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs) bb.bb_instructions
Proof
  strip_tac >> drule lineage_state_dfs_fields >> strip_tac >>
  drule_all dfs_block_state_defining_outputs_absent >>
  `ps.ps_spilled = ps_dfs.ps_spilled` by
    metis_tac[stackPlanTypesTheory.plan_state_accfupds] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
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

Theorem lineage_state_fresh_input_prefix_resource_bound:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after v
   setup_ops start k qs.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    (if bb = HD fn.fn_blocks then
       prepare_params_plan (liveness_analyze fn) fn
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    k <= LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_block_native_run >> strip_tac >> gvs[] >>
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
     Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1` >> gvs[] >>
     drule fnPlanLineageObserverTransportTheory.clean_stack_plan_resource_nonincrease >>
     disch_then (qspec_then `v` mp_tac) >>
     simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff,
          fnPlanLineageObserverTransportTheory.indicator_zero_iff]) >>
  qpat_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs`
    (mp_then Any mp_tac fnPlanLineageObserverTransportTheory.native_inst_prefix_phase_resource_bound) >>
  disch_then (qspecl_then [`bb`,`v`,`b`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!j before w. _` (qspecl_then [`j`,`before`,`w`] mp_tac) >>
    simp[arithmeticTheory.ADD_COMM])) >>
  Cases_on `b = 1 \/ EXISTS (\i. MEM v i.inst_outputs) (TAKE k (non_param_insts bb))` >>
  simp[] >> strip_tac >> decide_tac
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
  irule lineage_state_fresh_input_prefix_resource_bound >>
  goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
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

(* Shared actual-prefix adapter: availability supplies the phase bound premises. *)
Theorem lineage_state_fresh_prefix_resource_bound:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb h promised ops after
   setup_ops start k qs v.
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
    ~MEM (Var v) start.ps_stack /\ Var v NOTIN FDOM start.ps_spilled /\
    k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ ssa_form fn /\ bb.bb_label = lbl /\
    fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, codegen_ready_fn_def,
      lineage_state_reachable, fn_reachable_cfg_analyze] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    metis_tac[fnPlanLineageCallersTheory.ssa_form_block_outputs_distinct] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (non_param_insts bb)))` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (fn th => qpat_x_assum `ALL_DISTINCT _`
       (mp_tac o ONCE_REWRITE_RULE [th])) >>
     simp[listTheory.MAP_APPEND, listTheory.FLAT_APPEND, listTheory.ALL_DISTINCT_APPEND]) >>
  drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs`)
    fnPlanLineageObserverTransportTheory.native_inst_prefix_phase_resource_bound >>
  disch_then (qspecl_then [`bb`,`v`,`0`] mp_tac) >>
  simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff,
       fnPlanLineageObserverTransportTheory.indicator_zero_iff] >>
  (impl_tac
   >- (rpt gen_tac >> strip_tac >>
       `j < LENGTH (non_param_insts bb)` by decide_tac >>
       conj_tac
       >- (strip_tac >> irule lineage_state_ordinary_prefix_live_available >>
           goal_assum (drule_at Any) >> simp[] >>
           goal_assum (drule_at Any) >> simp[] >>
           goal_assum (drule_at Any) >> simp[] >>
           metis_tac[]) >>
       strip_tac >> irule lineage_state_ordinary_prefix_available >>
       goal_assum (drule_at Any) >> simp[] >>
       goal_assum (drule_at Any) >> simp[] >>
       goal_assum (drule_at Any) >> simp[] >>
       metis_tac[fnPlanLineageCallersTheory.ready_block_suffix_index,
         arithmeticTheory.ADD_COMM])) >>
  IF_CASES_TAC >> simp[] >> decide_tac
QED

(* First visits only: seed PHI production from actual history, not freshness assumptions. *)
Theorem lineage_state_fresh_phi_ordinary_joint:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM phi bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `collect_phis bb.bb_instructions <> []` by (strip_tac >> gvs[]) >>
  drule_all fnPlanLineagePhiScheduleTheory.ready_phi_block_suffix >> strip_tac >>
  `bb <> HD fn.fn_blocks /\ LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <> 1` by
    suspend "setup_identity" >>
  `~MEM (Var v) start.ps_stack /\ Var v NOTIN FDOM start.ps_spilled` by gvs[] >>
  `!j mid. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start j mid /\ j <= k ==>
    LIST_ELEM_COUNT (Var v) mid.ps_stack +
      (if Var v IN FDOM mid.ps_spilled then 1 else 0) <= 1` by
    suspend "phase_bound" >>
  conj_tac >- metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
  suspend "suffix_support"
QED

Resume lineage_state_fresh_phi_ordinary_joint[setup_identity]:
  conj_tac
  >- (strip_tac >>
      `fn.fn_blocks <> []` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
      drule_all fnPlanLineageEntryProductionTheory.ready_entry_static_boundary >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `codegen_ready_fn fn` mp_tac >>
  simp[codegen_ready_fn_def, phis_at_joins_def, listTheory.EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, listTheory.NULL_EQ]
QED

Resume lineage_state_fresh_phi_ordinary_joint[phase_bound]:
  rpt gen_tac >> strip_tac >>
  irule lineage_state_fresh_prefix_resource_bound >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Resume lineage_state_fresh_phi_ordinary_joint[suffix_support]:
  qabbrev_tac `p = LENGTH (collect_phis bb.bb_instructions)` >>
  `k = p + (k-p)` by decide_tac >>
  `?seed. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start p seed /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions)+p)
      (LENGTH bb.bb_instructions) (DROP p (non_param_insts bb)) seed (k-p) qs` by
    (qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs` mp_tac >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_split]) >>
  `((MEM (Var v) seed.ps_stack \/ Var v IN FDOM seed.ps_spilled) ==>
    MEM v (live_vars_at (liveness_analyze fn) lbl p))` by
    (`MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
       (irule removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre >>
        gvs[codegen_ready_fn_def]) >>
     simp[Abbr `p`] >> disch_tac >> gvs[] >>
     drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)
       fnPlanLineageObserverTransportTheory.native_defined_phi_body_demand_support >>
     simp[]) >>
  `!j. j < k-p ==> (EL j (DROP p (non_param_insts bb))).inst_opcode <> PHI /\
    (EL j (DROP p (non_param_insts bb))).inst_opcode <> JMP /\
    ~is_param_opcode (EL j (DROP p (non_param_insts bb))).inst_opcode /\
    ~MEM v (EL j (DROP p (non_param_insts bb))).inst_outputs` by
    suspend "suffix_layout" >>
  `!w. MEM w (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (get_params bb.bb_instructions)+p)) ==>
    MEM (Var w) seed.ps_stack \/ Var w IN FDOM seed.ps_spilled` by
    (rpt strip_tac >> irule lineage_state_ordinary_prefix_live_available >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[Abbr `p`] >>
     gvs[] >> decide_tac) >>
  `!j before w. j < k-p /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions)+p)
      (LENGTH bb.bb_instructions) (DROP p (non_param_insts bb)) seed j before /\
    MEM (Var w) (compute_operands (EL j (DROP p (non_param_insts bb)))) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by
    suspend "suffix_available" >>
  `LENGTH (get_params bb.bb_instructions)+k =
    LENGTH (get_params bb.bb_instructions)+p+(k-p)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  disch_tac >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `native_inst_prefix _ _ _ _ _ _ _ _ (DROP _ _) seed _ qs`
    (mp_then (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
      fnPlanLineageObserverTransportTheory.native_supported_ordinary_suffix_demand_support) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  disch_then irule >>
  conj_tac >- gvs[] >>
  reverse conj_tac >- metis_tac[] >>
  qpat_x_assum `!j mid. _ ==> LIST_ELEM_COUNT _ _ + _ <= 1`
    (qspecl_then [`p`,`seed`] mp_tac) >> simp[]
QED

Resume lineage_state_fresh_phi_ordinary_joint[suffix_layout]:
  rpt gen_tac >> strip_tac >>
  `p+j < k /\ p+j < LENGTH (non_param_insts bb)` by decide_tac >>
  `EL j (DROP p (non_param_insts bb)) = EL (p+j) (non_param_insts bb)` by
    gvs[listTheory.EL_DROP] >>
  simp[] >>
  `!i. p <= i /\ i < LENGTH (non_param_insts bb) ==>
    (EL i (non_param_insts bb)).inst_opcode <> PHI /\
    ((EL i (non_param_insts bb)).inst_opcode = JMP ==>
      SUC i = LENGTH (non_param_insts bb))` by
    (drule fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
     disch_then (qspecl_then [`bb`,`p`] mp_tac) >> simp[Abbr `p`]) >>
  `~is_param_opcode (EL (p+j) (non_param_insts bb)).inst_opcode` by
    (`MEM (EL (p+j) (non_param_insts bb)) (non_param_insts bb)` by
       metis_tac[listTheory.EL_MEM] >>
     qpat_x_assum `MEM (EL _ _) (non_param_insts bb)` mp_tac >>
     pure_once_rewrite_tac[non_param_insts_def] >>
     simp[listTheory.MEM_FILTER]) >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `?i. i < LENGTH (collect_phis bb.bb_instructions) /\
     MEM v (EL i (collect_phis bb.bb_instructions)).inst_outputs` by
    metis_tac[listTheory.MEM_EL] >>
  `~MEM v (inst_defs (EL (p+j) bb.bb_instructions))` by
    (irule fnPlanLineagePathTheory.ssa_phi_prefix_tail_no_defs >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  gvs[venomInstTheory.inst_defs_def] >>
  `p <= p+j` by decide_tac >>
  first_x_assum (qspec_then `p+j` mp_tac) >> simp[] >> decide_tac
QED

Resume lineage_state_fresh_phi_ordinary_joint[suffix_available]:
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ j before`)
    fnPlanLineageObserverTransportTheory.native_ordinary_suffix_computed_available >>
  disch_then (qspec_then `w` mp_tac) >> simp[] >>
  disch_then irule >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_TRANS]
QED

Finalise lineage_state_fresh_phi_ordinary_joint

Theorem lineage_state_fresh_phi_ordinary_demand_support:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_fresh_phi_ordinary_joint >> simp[] >> metis_tac[]
QED

Theorem lineage_history_first_phi_ordinary_joint[local]:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM phi bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  drule_all lineage_history_first_arrival_output_absent >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    (drule lineage_history_reconstruct >> simp[] >>
     disch_then irule >> simp[lineage_state_entry]) >>
  irule lineage_state_fresh_phi_ordinary_joint >> metis_tac[]
QED

Theorem lineage_history_first_phi_ordinary_demand_support:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  metis_tac[lineage_history_first_phi_ordinary_joint]
QED

(* Ordinary production is seeded at the actual body cut, not block entry. *)
Theorem lineage_state_body_seeded_ordinary_production:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb v h promised ops after
   setup_ops start seed k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start
      (LENGTH (collect_phis bb.bb_instructions)) seed /\
    ~MEM (Var v) seed.ps_stack /\ Var v NOTIN FDOM seed.ps_spilled /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1 /\
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `p = LENGTH (collect_phis bb.bb_instructions)` >>
  `k = p + (k-p)` by decide_tac >>
  `native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions)+p)
      (LENGTH bb.bb_instructions) (DROP p (non_param_insts bb)) seed (k-p) qs` by
    (qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs` mp_tac >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_split,
       fnPlanLineageEntryProductionTheory.native_inst_prefix_deterministic]) >>
  `!j. j < k-p ==> (EL j (DROP p (non_param_insts bb))).inst_opcode <> PHI /\
    (EL j (DROP p (non_param_insts bb))).inst_opcode <> JMP /\
    ~is_param_opcode (EL j (DROP p (non_param_insts bb))).inst_opcode` by
    suspend "suffix_layout" >>
  `!j before w. j < k-p /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions)+p)
      (LENGTH bb.bb_instructions) (DROP p (non_param_insts bb)) seed j before /\
    MEM (Var w) (compute_operands (EL j (DROP p (non_param_insts bb)))) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by
    suspend "suffix_available" >>
  `LENGTH (get_params bb.bb_instructions)+k =
    LENGTH (get_params bb.bb_instructions)+p+(k-p)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  irule fnPlanLineageObserverTransportTheory.native_defined_ordinary_suffix_production >>
  gvs[] >> qexistsl_tac [`dfg`, `seed`] >>
  gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> gvs[]
QED

Resume lineage_state_body_seeded_ordinary_production[suffix_layout]:
  rpt gen_tac >> strip_tac >>
  `p+j < k /\ p+j < LENGTH (non_param_insts bb)` by decide_tac >>
  `EL j (DROP p (non_param_insts bb)) = EL (p+j) (non_param_insts bb)` by
    gvs[listTheory.EL_DROP] >>
  `!i. p <= i /\ i < LENGTH (non_param_insts bb) ==>
    (EL i (non_param_insts bb)).inst_opcode <> PHI /\
    ((EL i (non_param_insts bb)).inst_opcode = JMP ==>
      SUC i = LENGTH (non_param_insts bb))` by
    (drule fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
     disch_then (qspecl_then [`bb`,`p`] mp_tac) >> simp[Abbr `p`]) >>
  `MEM (EL (p+j) (non_param_insts bb)) (non_param_insts bb)` by
    metis_tac[listTheory.EL_MEM] >>
  `MEM (EL (p+j) (non_param_insts bb)) bb.bb_instructions /\
    ~is_param_opcode (EL (p+j) (non_param_insts bb)).inst_opcode` by
    (qpat_x_assum `MEM (EL _ _) (non_param_insts bb)` mp_tac >>
     simp[non_param_insts_def, listTheory.MEM_FILTER]) >>
  `p <= p+j` by decide_tac >>
  `(EL (p+j) (non_param_insts bb)).inst_opcode <> PHI /\
    (EL (p+j) (non_param_insts bb)).inst_opcode <> JMP` by
    (first_x_assum (qspec_then `p+j` mp_tac) >> simp[] >> decide_tac) >>
  gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Resume lineage_state_body_seeded_ordinary_production[suffix_available]:
  `!u. MEM u (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+p)) ==>
    MEM (Var u) seed.ps_stack \/ Var u IN FDOM seed.ps_spilled` by
    (rpt strip_tac >> irule lineage_state_ordinary_prefix_live_available >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[Abbr `p`] >>
     gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ j before`)
    fnPlanLineageObserverTransportTheory.native_ordinary_suffix_computed_available >>
  disch_then (qspec_then `w` mp_tac) >> simp[] >>
  disch_then irule >> rpt strip_tac >> metis_tac[arithmeticTheory.LESS_TRANS]
QED

Finalise lineage_state_body_seeded_ordinary_production

Theorem lineage_state_fresh_ordinary_demand_support:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb inst v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ MEM inst (non_param_insts bb) /\
    inst.inst_opcode <> PHI /\ MEM v inst.inst_outputs /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst bb.bb_instructions` by
    gvs[non_param_insts_def, listTheory.MEM_FILTER] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `!other. MEM other bb.bb_instructions /\ MEM v other.inst_outputs ==> other = inst` by
    (rpt strip_tac >>
     `ssa_form fn` by gvs[codegen_ready_fn_def] >>
     metis_tac[removeUnusedSsaProofsTheory.ssa_unique_output_block]) >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  `~MEM (Var v) start.ps_stack /\ Var v NOTIN FDOM start.ps_spilled` by
    (drule_at (Pat `(if _ then _ else _) = _`)
       fnPlanLineageObserverTransportTheory.nonentry_setup_resource_absent >> simp[]) >>
  qabbrev_tac `p = LENGTH (collect_phis bb.bb_instructions)` >>
  `k = p + (k-p)` by decide_tac >>
  `?seed. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start p seed /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions)+p)
      (LENGTH bb.bb_instructions) (DROP p (non_param_insts bb)) seed (k-p) qs` by
    (qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs` mp_tac >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_split]) >>
  `~MEM (Var v) seed.ps_stack /\ Var v NOTIN FDOM seed.ps_spilled` by
    suspend "phi_absent" >>
  disch_tac >> irule (cj 2 lineage_state_body_seeded_ordinary_production) >>
  gvs[Abbr `p`] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume lineage_state_fresh_ordinary_demand_support[phi_absent]:
  `!i. i < p ==> (EL i (non_param_insts bb)).inst_opcode = PHI /\
      v <> HD (EL i (non_param_insts bb)).inst_outputs` by
    suspend "phi_layout" >>
  qpat_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ p seed`
    (mp_then (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
      fnPlanLineageObserverTransportTheory.native_inst_prefix_phi_resource_nonincrease) >>
  disch_then (qspec_then `v` mp_tac) >>
  Cases_on `Var v IN FDOM seed.ps_spilled` >>
  gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Resume lineage_state_fresh_ordinary_demand_support[phi_layout]:
  rpt gen_tac >> strip_tac >>
  `collect_phis bb.bb_instructions <> []` by
    (strip_tac >> gvs[Abbr `p`]) >>
  drule_all fnPlanLineagePhiScheduleTheory.ready_phi_block_suffix >> strip_tac >>
  `EL i (non_param_insts bb) = EL i (collect_phis bb.bb_instructions)` by
    (gvs[Abbr `p`] >> metis_tac[rich_listTheory.EL_APPEND1]) >>
  `MEM (EL i (collect_phis bb.bb_instructions)) (collect_phis bb.bb_instructions)` by
    gvs[Abbr `p`, listTheory.EL_MEM] >>
  `MEM (EL i (collect_phis bb.bb_instructions)) bb.bb_instructions /\
    (EL i (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `inst_wf (EL i (collect_phis bb.bb_instructions))` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM] >>
     metis_tac[]) >>
  `LENGTH (EL i (collect_phis bb.bb_instructions)).inst_outputs = 1` by
    metis_tac[cfgNormBaseTheory.inst_wf_phi_well_formed] >>
  `MEM (HD (EL i (collect_phis bb.bb_instructions)).inst_outputs)
      (EL i (collect_phis bb.bb_instructions)).inst_outputs` by
    (Cases_on `(EL i (collect_phis bb.bb_instructions)).inst_outputs` >> gvs[]) >>
  metis_tac[]
QED

Finalise lineage_state_fresh_ordinary_demand_support

Theorem lineage_state_fresh_ordinary_resource_bound:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb inst v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ MEM inst (non_param_insts bb) /\
    inst.inst_opcode <> PHI /\ MEM v inst.inst_outputs /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst bb.bb_instructions` by
    gvs[non_param_insts_def, listTheory.MEM_FILTER] >>
  `~MEM (Var v) start.ps_stack /\ Var v NOTIN FDOM start.ps_spilled` by
    (`bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
     qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
     drule_at (Pat `(if _ then _ else _) = _`)
       fnPlanLineageObserverTransportTheory.nonentry_setup_resource_absent >> simp[]) >>
  irule lineage_state_fresh_prefix_resource_bound >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[] >> metis_tac[]
QED

Theorem lineage_history_first_ordinary_demand_support:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb inst v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ MEM inst (non_param_insts bb) /\
    inst.inst_opcode <> PHI /\ MEM v inst.inst_outputs /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst bb.bb_instructions` by
    gvs[non_param_insts_def, listTheory.MEM_FILTER] >>
  drule_all lineage_history_first_arrival_output_absent >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    (drule lineage_history_reconstruct >> simp[] >>
     disch_then irule >> simp[lineage_state_entry]) >>
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    lineage_state_fresh_ordinary_demand_support >>
  simp[] >> disch_then drule >> gvs[] >> metis_tac[]
QED

Theorem lineage_history_first_ordinary_resource_bound:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb inst v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ MEM inst (non_param_insts bb) /\
    inst.inst_opcode <> PHI /\ MEM v inst.inst_outputs /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst bb.bb_instructions` by
    gvs[non_param_insts_def, listTheory.MEM_FILTER] >>
  drule_all lineage_history_first_arrival_output_absent >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    (drule lineage_history_reconstruct >> simp[] >>
     disch_then irule >> simp[lineage_state_entry]) >>
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    lineage_state_fresh_ordinary_resource_bound >>
  simp[] >> disch_then drule >> gvs[] >> metis_tac[]
QED

Theorem lineage_history_first_phi_ordinary_resource_bound:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb v h promised ops after
   setup_ops start k qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  metis_tac[lineage_history_first_phi_ordinary_joint]
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

(* A starting cut may lie inside the PHIs. Only the actually traversed
   suffix is constrained not to define the observer. *)
Theorem lineage_state_suffix_dead_stack:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after
   setup_ops start a seed v.
    codegen_ready_fn fn /\
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
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start a seed /\
    ~MEM (Var v) seed.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) lbl
      (MAX (LENGTH (get_params bb.bb_instructions)+a)
        (LENGTH (collect_phis bb.bb_instructions)))) /\
    (!j. a <= j /\ j < LENGTH (non_param_insts bb) ==>
      ~MEM v (EL j (non_param_insts bb)).inst_outputs) ==>
    ~MEM (Var v) after.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_block_native_run >> strip_tac >> gvs[] >>
  `a <= LENGTH (non_param_insts bb)` by
    metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_bound] >>
  `LENGTH (get_params bb.bb_instructions) + LENGTH (non_param_insts bb) =
    LENGTH bb.bb_instructions` by
    (drule_all fnPlanLineageCallersTheory.ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac
       fnPlanLineageLivenessTheory.collect_phis_prefix >>
     metis_tac[listTheory.LENGTH_APPEND, arithmeticTheory.LESS_EQ_ADD]) >>
  qspecl_then [`fn`, `bb`, `dfg`, `a`] mp_tac
    fnPlanLineageObserverTransportTheory.native_seeded_phi_body_dead_stack >>
  simp[arithmeticTheory.ADD_COMM] >>
  disch_then (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  metis_tac[arithmeticTheory.ADD_SYM]
QED

Theorem lineage_state_incoming_prefix_dead_stack:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb pred
   setup_ops start k qs v.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    ~MEM (Var v) ps.ps_stack /\
    ~MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0)) /\
    (!j. j < k ==> ~MEM v (EL j (non_param_insts bb)).inst_outputs) ==>
    ~MEM (Var v) qs.ps_stack /\
    (LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+k ==>
      ~MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
              venomExecPropsTheory.lookup_block_label] >>
  `fn_reachable fn lbl` by
    metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `bb <> HD fn.fn_blocks` by
    (irule fnPlanLineageObserverTransportTheory.ready_incoming_block_nonentry >>
     simp[] >> qexists_tac `pred` >> simp[]) >>
  `~MEM (Var v) (ps with <|ps_cleanup_height := h;
     ps_cleanup_promised := promised|>).ps_stack` by simp[] >>
  gvs[] >>
  qspecl_then [`fn`, `bb`] mp_tac
    fnPlanLineageObserverTransportTheory.native_incoming_prefix_dead_stack >>
  simp[arithmeticTheory.ADD_COMM] >>
  disch_then (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`pred`,
    `ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`] mp_tac) >>
  simp[] >> metis_tac[]
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
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >>
     gvs[codegen_ready_fn_def] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `!j before w. _` kall_tac >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac
       fnPlanLineageLivenessTheory.collect_phis_prefix >>
     metis_tac[listTheory.LENGTH_APPEND, arithmeticTheory.LESS_EQ_ADD]) >>
  `!j. j < LENGTH bb.bb_instructions ==>
    ~MEM v (EL j bb.bb_instructions).inst_outputs` by
    gvs[listTheory.EVERY_EL] >>
  drule_at (Pat `lookup_block _ _ = _`) lineage_state_incoming_prefix_dead_stack >>
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

(* Complete intermediate vertices are constrained, but only the executed
   prefix of the endpoint is nondefining. The endpoint may still be in PHIs. *)
Theorem lineage_history_incoming_prefix_dead_stack:
  !fn dfg ch growth spill_base lbl_ctr vertices a lbl ps pred v
   bb h promised setup_ops start k qs.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) (FST a) (SND a) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices a (lbl,ps) /\
    MEM (FST a) (cfg_succs_of (cfg_analyze fn) pred) /\
    ~MEM (Var v) (SND a).ps_stack /\
    (!ab. lookup_block (FST a) fn.fn_blocks = SOME ab ==>
      ~MEM v (input_vars_from pred ab.bb_instructions
        (live_vars_at (liveness_analyze fn) (FST a) 0))) /\
    EVERY (\vertex. !ib. lookup_block (FST vertex) fn.fn_blocks = SOME ib ==>
      EVERY (\inst. ~MEM v inst.inst_outputs) ib.bb_instructions) vertices /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    (!j. j < k ==> ~MEM v (EL j (non_param_insts bb)).inst_outputs) ==>
    ~MEM (Var v) qs.ps_stack /\
    (LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+k ==>
      ~MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_history_incoming_dead_stack >> simp[] >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    metis_tac[lineage_history_reconstruct, pairTheory.FST, pairTheory.SND] >>
  drule_all lineage_state_incoming_prefix_dead_stack >>
  simp[arithmeticTheory.ADD_COMM]
QED

(* An actual instruction-cut interval crossing at least one edge. The
   first edge's realization is explicit so the starting cut and its terminal
   state use the very same cleanup choice. No outputs before a, or after k,
   are constrained. Only completely traversed intermediate vertices use
   whole-block nondefinition. *)
Theorem lineage_history_suffix_prefix_dead_stack:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after
   setup_ops start a seed succ sp vertices last_lbl last_ps last_bb
   last_h last_promised last_setup last_start k qs v.
    codegen_ready_fn fn /\
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
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start a seed /\
    ~MEM (Var v) seed.ps_stack /\
    ~MEM v (live_vars_at (liveness_analyze fn) lbl
      (MAX (LENGTH (get_params bb.bb_instructions)+a)
        (LENGTH (collect_phis bb.bb_instructions)))) /\
    (!j. a <= j /\ j < LENGTH (non_param_insts bb) ==>
      ~MEM v (EL j (non_param_insts bb)).inst_outputs) /\
    lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) (succ,sp) /\
    sp.ps_stack = after.ps_stack /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr))
      vertices (succ,sp) (last_lbl,last_ps) /\
    EVERY (\vertex. !ib. lookup_block (FST vertex) fn.fn_blocks = SOME ib ==>
      EVERY (\inst. ~MEM v inst.inst_outputs) ib.bb_instructions) vertices /\
    lookup_block last_lbl fn.fn_blocks = SOME last_bb /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) last_lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn last_bb
         (last_ps with <|ps_cleanup_height := last_h;
           ps_cleanup_promised := last_promised|>)
     else ([],last_ps with <|ps_cleanup_height := last_h;
       ps_cleanup_promised := last_promised|>)) = (last_setup,last_start) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn last_lbl
      (bb_is_halting last_bb) (LENGTH (get_params last_bb.bb_instructions))
      (LENGTH last_bb.bb_instructions) (non_param_insts last_bb) last_start k qs /\
    (!j. j < k ==> ~MEM v (EL j (non_param_insts last_bb)).inst_outputs) ==>
    ~MEM (Var v) qs.ps_stack /\
    (LENGTH (collect_phis last_bb.bb_instructions) <=
       LENGTH (get_params last_bb.bb_instructions)+k ==>
      ~MEM v (live_vars_at (liveness_analyze fn) last_lbl
        (LENGTH (get_params last_bb.bb_instructions)+k)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_suffix_dead_stack >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ sp` by
    metis_tac[lineage_edge_step] >>
  `MEM succ (cfg_succs_of (cfg_analyze fn) lbl)` by
    metis_tac[lineage_edge_physical] >>
  `~MEM (Var v) sp.ps_stack` by simp[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze] >>
  `!sb. lookup_block succ fn.fn_blocks = SOME sb ==>
    ~MEM v (input_vars_from lbl sb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0))` by
    (rpt gen_tac >> strip_tac >>
     drule_all fnPlanLineageLivenessTheory.analyzed_live_out_edge_subset >>
     simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  drule_at (Pat `LRC _ _ _ _`) lineage_history_incoming_prefix_dead_stack >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
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
Theorem lineage_state_seeded_ordinary_stack_support:
  !fn dfg ch growth spill_base lbl_ctr lbl ps h promised bb ops after
   setup_ops start a seed k qs v.
    codegen_ready_fn fn /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
    (if bb = HD fn.fn_blocks then prepare_params_plan (liveness_analyze fn) fn
       (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    LENGTH (collect_phis bb.bb_instructions) <= a /\ a <= k /\
    k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start a seed /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    LIST_ELEM_COUNT (Var v) seed.ps_stack +
      (if Var v IN FDOM seed.ps_spilled then 1 else 0) <= 1 /\
    (MEM (Var v) seed.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+a))) /\
    (!j. a <= j /\ j < k ==> ~MEM v (EL j (non_param_insts bb)).inst_outputs) ==>
    MEM (Var v) qs.ps_stack ==>
    MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (get_params bb.bb_instructions)+k))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  `native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions)+a)
    (LENGTH bb.bb_instructions) (DROP a (non_param_insts bb)) seed (k-a) qs` by
    metis_tac[fnPlanLineageObserverTransportTheory.native_inst_prefix_between] >>
  `!j. j < k-a ==> (EL j (DROP a (non_param_insts bb))).inst_opcode <> PHI /\
    (EL j (DROP a (non_param_insts bb))).inst_opcode <> JMP /\
    ~is_param_opcode (EL j (DROP a (non_param_insts bb))).inst_opcode /\
    ~MEM v (EL j (DROP a (non_param_insts bb))).inst_outputs` by
    suspend "layout" >>
  `!j before w. j < k-a /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions)+a)
      (LENGTH bb.bb_instructions) (DROP a (non_param_insts bb)) seed j before /\
    MEM (Var w) (compute_operands (EL j (DROP a (non_param_insts bb)))) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by
    suspend "available" >>
  `LENGTH (get_params bb.bb_instructions)+k =
    LENGTH (get_params bb.bb_instructions)+a+(k-a)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `native_inst_prefix _ _ _ _ _ _ _ _ (DROP _ _) seed _ qs`
    (mp_then (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac
      fnPlanLineageObserverTransportTheory.native_stack_supported_ordinary_suffix) >>
  disch_then (qspec_then `v` mp_tac) >>
  gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Resume lineage_state_seeded_ordinary_stack_support[layout]:
  rpt gen_tac >> strip_tac >>
  `a+j < k /\ a+j < LENGTH (non_param_insts bb)` by decide_tac >>
  `EL j (DROP a (non_param_insts bb)) = EL (a+j) (non_param_insts bb)` by
    gvs[listTheory.EL_DROP] >>
  `!i. a <= i /\ i < LENGTH (non_param_insts bb) ==>
    (EL i (non_param_insts bb)).inst_opcode <> PHI /\
    ((EL i (non_param_insts bb)).inst_opcode = JMP ==>
      SUC i = LENGTH (non_param_insts bb))` by
    (drule fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
     disch_then (qspecl_then [`bb`,`a`] mp_tac) >> simp[]) >>
  `MEM (EL (a+j) (non_param_insts bb)) (non_param_insts bb)` by
    metis_tac[listTheory.EL_MEM] >>
  `~is_param_opcode (EL (a+j) (non_param_insts bb)).inst_opcode` by
    (qpat_x_assum `MEM (EL _ _) (non_param_insts bb)` mp_tac >>
     simp[non_param_insts_def, listTheory.MEM_FILTER]) >>
  `a <= a+j` by decide_tac >>
  first_x_assum (qspec_then `a+j` mp_tac) >> simp[] >>
  gvs[arithmeticTheory.ADD_COMM] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Resume lineage_state_seeded_ordinary_stack_support[available]:
  `?entry. fn_entry_label fn = SOME entry` by metis_tac[lineage_state_has_entry] >>
  `!u. MEM u (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+a)) ==>
    MEM (Var u) seed.ps_stack \/ Var u IN FDOM seed.ps_spilled` by
    (rpt strip_tac >> irule lineage_state_ordinary_prefix_live_available >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> gvs[] >>
     metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ j before`)
    fnPlanLineageObserverTransportTheory.native_ordinary_suffix_computed_available >>
  disch_then (qspec_then `w` mp_tac) >> simp[] >>
  disch_then irule >> rpt strip_tac >>
  gvs[] >> metis_tac[arithmeticTheory.LESS_TRANS]
QED

Finalise lineage_state_seeded_ordinary_stack_support

Theorem lineage_state_incoming_ordinary_stack_support:
  !fn dfg ch growth spill_base lbl_ctr entry pred pb pred_input pred_ops pred_after
   lbl ps h promised bb ops after setup_ops start k qs v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb pred_input =
      SOME (pred_ops,pred_after) /\
    (MEM (Var v) pred_after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) pred_after.ps_stack +
      (if Var v IN FDOM pred_after.ps_spilled then 1 else 0) <= 1 /\
    ps.ps_stack = pred_after.ps_stack /\ ps.ps_spilled = pred_after.ps_spilled /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (setup_ops,start) /\
    LENGTH (collect_phis bb.bb_instructions) <= k /\ k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
    EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions ==>
    MEM (Var v) qs.ps_stack ==>
    MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (get_params bb.bb_instructions)+k))
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl /\
    cfg_reachable_of (cfg_analyze fn) lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `bb <> HD fn.fn_blocks` by
    (irule fnPlanLineageObserverTransportTheory.ready_incoming_block_nonentry >>
     simp[] >> qexists_tac `pred` >> simp[]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >>
     metis_tac[codegen_ready_fn_def]) >>
  qabbrev_tac `p = LENGTH (collect_phis bb.bb_instructions)` >>
  `k = p+(k-p)` by (gvs[Abbr `p`] >> decide_tac) >>
  `?seed. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) start p seed` by
    (qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs` mp_tac >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_split]) >>
  `MEM (Var v) seed.ps_stack ==> MEM v
    (live_vars_at (liveness_analyze fn) lbl (LENGTH (get_params bb.bb_instructions)+p))` by
    suspend "seed_support" >>
  `LIST_ELEM_COUNT (Var v) seed.ps_stack +
    (if Var v IN FDOM seed.ps_spilled then 1 else 0) <= 1` by
    suspend "seed_bound" >>
  strip_tac >> irule lineage_state_seeded_ordinary_stack_support >>
  simp[] >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  simp[] >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  simp[] >>
  qexistsl_tac [`p`,`qs`,`seed`] >>
  gvs[Abbr `p`, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  `j < LENGTH bb.bb_instructions` by decide_tac >>
  metis_tac[listTheory.EL_MEM]
QED

Resume lineage_state_incoming_ordinary_stack_support[seed_support]:
  `lbl <> entry` by
    (gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
       listTheory.NULL_EQ] >>
     strip_tac >>
     drule_all fnPlanLineageEntryProductionTheory.ready_entry_static_boundary >>
     strip_tac >>
     gvs[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]) >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    (drule (codegen_ready_fn_def |> iffLR) >> strip_tac >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `EVERY (\inst. ~MEM v inst.inst_outputs) (collect_phis bb.bb_instructions)` by
    (gvs[listTheory.EVERY_MEM] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  gvs[Abbr `p`] >> strip_tac >>
  irule fnPlanLineageObserverTransportTheory.native_incoming_phi_body_stack_support >>
  simp[] >>
  qexistsl_tac [`pred_after`,`dfg`,`seed`,`F`,
    `ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`,
    `pred_ops`,`pb`,`pred`,`pred_input`,`setup_ops`,`start`] >>
  simp[]
QED

Resume lineage_state_incoming_ordinary_stack_support[seed_bound]:
  `LIST_ELEM_COUNT (Var v) start.ps_stack +
    (if Var v IN FDOM start.ps_spilled then 1 else 0) <= 1` by
    (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1` >> gvs[] >>
     drule fnPlanLineageObserverTransportTheory.clean_stack_plan_resource_nonincrease >>
     disch_then (qspec_then `v` mp_tac) >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!j before w. j < p /\ LENGTH (collect_phis bb.bb_instructions) <= j /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) start j before ==>
    (MEM w (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (get_params bb.bb_instructions)+j)) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled) /\
    (MEM (Var w) (compute_operands (EL j (non_param_insts bb))) ==>
      MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled)` by
    (simp[Abbr `p`] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  qpat_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ p seed`
    (mp_then Any mp_tac fnPlanLineageObserverTransportTheory.native_inst_prefix_nondefining_observer_upper) >>
  disch_then (qspecl_then [`bb`,`v`] mp_tac) >> simp[] >>
  gvs[] >> metis_tac[]
QED

Finalise lineage_state_incoming_ordinary_stack_support

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

Theorem lineage_state_supported_outgoing_production:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb h promised ops after succ v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    (!setup_ops start k qs.
      (if bb = HD fn.fn_blocks then prepare_params_plan (liveness_analyze fn) fn
         (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
       else if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
         clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
           (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
       else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
        (setup_ops,start) /\
      LENGTH (collect_phis bb.bb_instructions) <= k /\ k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs ==>
      (MEM (Var v) qs.ps_stack ==>
        MEM v (live_vars_at (liveness_analyze fn) lbl
          (LENGTH (get_params bb.bb_instructions)+k))) /\
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1) ==>
    (((MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `bb = HD fn.fn_blocks ==> LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1` by
    (strip_tac >>
     `fn.fn_blocks <> []` by metis_tac[listTheory.MEM] >>
     drule_all fnPlanLineageEntryProductionTheory.ready_entry_static_boundary >>
     strip_tac >> gvs[]) >>
  `~bb_is_halting bb` by
    metis_tac[fnPlanLineageObserverTransportTheory.ready_edge_source_nonhalting] >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
    (gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def,
      venomWfTheory.bb_well_formed_def] >> metis_tac[]) >>
  drule_all fnPlanLineageObserverTransportTheory.ready_block_terminal_factor >>
  strip_tac >> gvs[] >>
  `MEM (Var v) before.ps_stack ==>
     MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
       (PRE (LENGTH bb.bb_instructions)))` by metis_tac[arithmeticTheory.ADD_COMM] >>
  `LIST_ELEM_COUNT (Var v) before.ps_stack +
    (if Var v IN FDOM before.ps_spilled then 1 else 0) <= 1` by metis_tac[] >>
  `!w. MEM (Var w) (compute_operands (LAST bb.bb_instructions)) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by
    (rpt strip_tac >> irule lineage_state_ordinary_prefix_available >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> gvs[rich_listTheory.EL_PRE_LENGTH]) >>
  reverse conj_tac >- suspend "terminal_bound" >>
  qspecl_then [`fn`,`bb`] mp_tac
    fnPlanLineageObserverTransportTheory.native_ready_terminal_stack_support >>
  simp[] >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Resume lineage_state_supported_outgoing_production[terminal_bound]:
  `!w. MEM w (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions) + PRE (LENGTH (non_param_insts bb)) )) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by
    (rpt strip_tac >> irule lineage_state_ordinary_prefix_live_available >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> gvs[] >> metis_tac[]) >>
  `DROP (PRE (LENGTH (non_param_insts bb))) (non_param_insts bb) =
    [LAST bb.bb_instructions]` by
    (`bb.bb_instructions = get_params bb.bb_instructions ++ non_param_insts bb` by
       metis_tac[fnPlanLineageCallersTheory.ready_block_parameter_suffix] >>
     `non_param_insts bb <> []` by (strip_tac >> gvs[]) >>
     `LAST bb.bb_instructions = LAST (non_param_insts bb)` by
       metis_tac[rich_listTheory.LAST_APPEND_NOT_NIL] >>
     qspecl_then [`non_param_insts bb`,`LENGTH (non_param_insts bb)`] mp_tac
       rich_listTheory.DROP_PREn_LAST_CONS >> simp[arithmeticTheory.PRE_SUB1]) >>
  irule fnPlanLineageObserverTransportTheory.native_indexed_step_nondefining_observer_bound >>
  simp[] >> goal_assum (drule_at (Pat `DROP _ _ = _`)) >> simp[] >>
  qexistsl_tac [`before`,`dfg`,`fn`,`chunk`] >> gvs[] >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def] >>
     metis_tac[rich_listTheory.LAST_MEM]) >>
  simp[venomExecProofsTheory.terminator_no_outputs]
QED

Finalise lineage_state_supported_outgoing_production

Theorem lineage_state_body_seeded_ordinary_exit_production:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb v h promised ops after
   setup_ops start seed succ.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
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
      (LENGTH (collect_phis bb.bb_instructions)) seed /\
    ~MEM (Var v) seed.ps_stack /\ Var v NOTIN FDOM seed.ps_spilled /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    (MEM (Var v) after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `((MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1`
    suffices_by metis_tac[] >>
  irule lineage_state_supported_outgoing_production >> simp[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >> simp[] >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    lineage_state_body_seeded_ordinary_production >> simp[] >>
  disch_then (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs`)) >>
  simp[] >> metis_tac[]
QED

Theorem lineage_state_fresh_phi_exit_demand_support:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb v h promised ops after succ.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    (MEM (Var v) after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (irule lineage_state_block_fresh_output_resource_bound >> metis_tac[]) >>
  `((MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)))`
    suffices_by metis_tac[] >>
  match_mp_tac (cj 1 lineage_state_supported_outgoing_production) >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  simp[] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    lineage_state_fresh_phi_ordinary_joint >> simp[] >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem lineage_history_first_phi_exit_demand_support:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb v h promised ops after succ.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    (MEM (Var v) after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    (drule lineage_history_reconstruct >> simp[] >>
     disch_then irule >> simp[lineage_state_entry]) >>
  `?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM phi bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  drule_all lineage_history_first_arrival_output_absent >> strip_tac >>
  irule lineage_state_fresh_phi_exit_demand_support >> metis_tac[]
QED

Theorem lineage_state_fresh_ordinary_exit_demand_support:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb inst v h promised ops after succ.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ MEM inst (non_param_insts bb) /\
    inst.inst_opcode <> PHI /\ MEM v inst.inst_outputs /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    (MEM (Var v) after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (irule lineage_state_block_fresh_output_resource_bound >>
      metis_tac[non_param_insts_def, listTheory.MEM_FILTER]) >>
  `((MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)))`
    suffices_by metis_tac[] >>
  match_mp_tac (cj 1 lineage_state_supported_outgoing_production) >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  simp[] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
        lineage_state_fresh_ordinary_demand_support >>
      simp[] >> disch_then drule >> simp[] >> metis_tac[]) >>
  drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
    lineage_state_fresh_ordinary_resource_bound >>
  simp[] >> disch_then drule >> gvs[] >> metis_tac[]
QED

Theorem lineage_history_first_ordinary_exit_demand_support:
  !fn dfg ch growth spill_base lbl_ctr entry vertices lbl ps bb inst v h promised ops after succ.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\ MEM inst (non_param_insts bb) /\
    inst.inst_opcode <> PHI /\ MEM v inst.inst_outputs /\
    ~MEM lbl (MAP FST vertices) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\ ~bb_is_halting bb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    (MEM (Var v) after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst bb.bb_instructions` by
    gvs[non_param_insts_def, listTheory.MEM_FILTER] >>
  drule_all lineage_history_first_arrival_output_absent >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    (drule lineage_history_reconstruct >> simp[] >>
     disch_then irule >> simp[lineage_state_entry]) >>
  irule lineage_state_fresh_ordinary_exit_demand_support >> metis_tac[]
QED

Theorem lineage_state_incoming_block_exit_support:
  !fn dfg ch growth spill_base lbl_ctr entry pred pb pred_input pred_ops pred_after
   lbl ps h promised bb ops after succ v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb pred_input =
      SOME (pred_ops,pred_after) /\
    (MEM (Var v) pred_after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) pred_after.ps_stack +
      (if Var v IN FDOM pred_after.ps_spilled then 1 else 0) <= 1 /\
    ps.ps_stack = pred_after.ps_stack /\ ps.ps_spilled = pred_after.ps_spilled /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      SOME (ops,after) /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) /\
    EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions ==>
    (MEM (Var v) after.ps_stack ==>
      MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (irule lineage_state_block_nondefining_observer_upper >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  `bb <> HD fn.fn_blocks` by
    metis_tac[fnPlanLineageObserverTransportTheory.ready_incoming_block_nonentry] >>
  `~bb_is_halting bb` by
    metis_tac[fnPlanLineageObserverTransportTheory.ready_edge_source_nonhalting] >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode /\
    inst_wf (LAST bb.bb_instructions)` by suspend "terminal" >>
  `bb = HD fn.fn_blocks ==> LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1`
    by simp[] >>
  drule_all fnPlanLineageObserverTransportTheory.ready_block_terminal_factor >>
  strip_tac >>
  `MEM (Var v) before.ps_stack ==> MEM v
    (live_vars_at (liveness_analyze fn) bb.bb_label (PRE (LENGTH bb.bb_instructions)))` by
    suspend "prefix_support" >>
  `LIST_ELEM_COUNT (Var v) before.ps_stack +
    (if Var v IN FDOM before.ps_spilled then 1 else 0) <= 1` by suspend "prefix_bound" >>
  `!w. MEM (Var w) (compute_operands (LAST bb.bb_instructions)) ==>
    MEM (Var w) before.ps_stack \/ Var w IN FDOM before.ps_spilled` by suspend "available" >>
  metis_tac[fnPlanLineageObserverTransportTheory.native_ready_terminal_stack_support]
QED

Resume lineage_state_incoming_block_exit_support[terminal]:
  `bb_well_formed bb` by
    (gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def] >> metis_tac[]) >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def,
         venomWfTheory.bb_well_formed_def] >> metis_tac[rich_listTheory.LAST_MEM]) >>
  gvs[venomWfTheory.bb_well_formed_def]
QED

Resume lineage_state_incoming_block_exit_support[prefix_support]:
  strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (get_params bb.bb_instructions) + PRE (LENGTH (non_param_insts bb))))`
    suffices_by metis_tac[] >>
  irule lineage_state_incoming_ordinary_stack_support >> simp[] >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >> simp[] >>
  suspend "compose_prefix"
QED

Resume lineage_state_incoming_block_exit_support[compose_prefix]:
  qexistsl_tac [`pb`,`pred`,`pred_after`,`pred_input`,`pred_ops`,
    `before`,`setup_ops`,`start`] >> gvs[]
QED

Resume lineage_state_incoming_block_exit_support[prefix_bound]:
  `LIST_ELEM_COUNT (Var v) start.ps_stack +
    (if Var v IN FDOM start.ps_spilled then 1 else 0) <= 1` by
    (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1` >> gvs[]
     >- (drule fnPlanLineageObserverTransportTheory.clean_stack_plan_resource_nonincrease >>
         disch_then (qspec_then `v` mp_tac) >> simp[] >>
         metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[]) >>
  drule fnPlanLineageObserverTransportTheory.native_inst_prefix_nondefining_observer_bound >>
  disch_then (qspecl_then [`bb`,`v`,`1`] mp_tac) >> simp[] >>
  disch_then irule >> rpt gen_tac >> strip_tac >>
  conj_tac >- (strip_tac >> irule lineage_state_ordinary_prefix_live_available >>
    goal_assum (drule_at Any) >> simp[] >>
    goal_assum (drule_at Any) >> simp[] >>
    goal_assum (drule_at Any) >> simp[] >>
    metis_tac[arithmeticTheory.LESS_TRANS]) >>
  suspend "bound_computed"
QED

Resume lineage_state_incoming_block_exit_support[available]:
  rpt strip_tac >> irule lineage_state_ordinary_prefix_available >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `setup_ops` >> gvs[rich_listTheory.EL_PRE_LENGTH]
QED

Resume lineage_state_incoming_block_exit_support[bound_computed]:
  `j < LENGTH (non_param_insts bb)` by decide_tac >>
  `EL j (non_param_insts bb) =
    EL (LENGTH (get_params bb.bb_instructions)+j) bb.bb_instructions` by
    metis_tac[fnPlanLineageCallersTheory.ready_block_suffix_index] >>
  strip_tac >> irule lineage_state_ordinary_prefix_available >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ch`,`growth`,`lbl_ctr`,`setup_ops`,`spill_base`] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Finalise lineage_state_incoming_block_exit_support

(* LRC records executed sources, not its endpoint.  Transport a single actual
   incoming execution witness; no support invariant is assumed at every vertex. *)
Theorem lineage_history_incoming_stack_support:
  !fn dfg ch growth spill_base lbl_ctr entry.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry ==>
    !vertices a b v.
      lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) (FST a) (SND a) /\
      LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices a b /\
      EVERY (\vertex. !bb. lookup_block (FST vertex) fn.fn_blocks = SOME bb ==>
        EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions) vertices /\
      (?pred pb input ops after.
        cfg_reachable_of (cfg_analyze fn) pred /\
        lookup_block pred fn.fn_blocks = SOME pb /\
        generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb input =
          SOME (ops,after) /\
        (MEM (Var v) after.ps_stack ==> MEM v
          (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))) /\
        LIST_ELEM_COUNT (Var v) after.ps_stack +
          (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1 /\
        (SND a).ps_stack = after.ps_stack /\ (SND a).ps_spilled = after.ps_spilled /\
        MEM (FST a) (cfg_succs_of (cfg_analyze fn) pred)) ==>
      ?pred pb input ops after.
        cfg_reachable_of (cfg_analyze fn) pred /\
        lookup_block pred fn.fn_blocks = SOME pb /\
        generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb input =
          SOME (ops,after) /\
        (MEM (Var v) after.ps_stack ==> MEM v
          (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))) /\
        LIST_ELEM_COUNT (Var v) after.ps_stack +
          (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1 /\
        (SND b).ps_stack = after.ps_stack /\ (SND b).ps_spilled = after.ps_spilled /\
        MEM (FST b) (cfg_succs_of (cfg_analyze fn) pred)
Proof
  rpt gen_tac >> strip_tac >> Induct >> simp[listTheory.LRC_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  PairCases_on `h` >> PairCases_on `z` >> gvs[] >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) z0 z1` by
    metis_tac[lineage_edge_step] >>
  drule lineage_edge_physical >> strip_tac >>
  suspend "step"
QED

Resume lineage_history_incoming_stack_support[step]:
  `EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions` by metis_tac[] >>
  `(MEM (Var v) after'.ps_stack ==> MEM v
      (live_vars_at (liveness_analyze fn) h0 (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after'.ps_stack +
      (if Var v IN FDOM after'.ps_spilled then 1 else 0) <= 1` by
    (irule lineage_state_incoming_block_exit_support >> simp[] >>
     conj_tac >- (qexists_tac `z0` >> simp[]) >>
     goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ h0 h1`)) >> simp[] >>
     goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ bb _ = _`)) >> simp[] >>
     suspend "incoming") >>
  first_x_assum irule >> simp[] >>
  qexists_tac `(z0,z1)` >> simp[] >>
  qexistsl_tac [`h0`,`bb`,
    `h1 with <|ps_cleanup_height := ch'; ps_cleanup_promised := promised|>`,
    `ops'`,`after'`] >> simp[] >>
  metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def]
QED

Resume lineage_history_incoming_stack_support[incoming]:
  qexistsl_tac [`pb`,`pred`,`after`,`input`,`ops`] >> simp[]
QED

Finalise lineage_history_incoming_stack_support

Theorem lineage_state_fresh_phi_return_absent:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb v segment qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    segment <> [] /\ ~MEM lbl (MAP FST (TL segment)) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) segment (lbl,ps) (lbl,qs) ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `segment` >> gvs[listTheory.LRC_def] >>
  PairCases_on `z` >> gvs[] >>
  drule lineage_edge_physical >> strip_tac >>
  gvs[] >> suspend "transport"
QED

Resume lineage_state_fresh_phi_return_absent[transport]:
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `collect_phis bb.bb_instructions <> []` by (strip_tac >> gvs[]) >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl)` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, listTheory.EVERY_MEM] >>
     metis_tac[listTheory.NULL_EQ, arithmeticTheory.NOT_LESS_EQUAL]) >>
  `~bb_is_halting bb` by
    metis_tac[fnPlanLineageObserverTransportTheory.ready_edge_source_nonhalting] >>
  `(MEM (Var v) after.ps_stack ==> MEM v
      (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1` by
    (irule lineage_state_fresh_phi_exit_demand_support >>
     metis_tac[]) >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem]) >>
  `EVERY (\vertex. !other. lookup_block (FST vertex) fn.fn_blocks = SOME other ==>
    EVERY (\i. ~MEM v i.inst_outputs) other.bb_instructions) t` by
    (simp[Once listTheory.EVERY_MEM] >> rpt strip_tac >>
     `FST vertex <> lbl` by
       (strip_tac >> qpat_x_assum `~MEM lbl (MAP FST t)` mp_tac >>
        simp[listTheory.MEM_MAP] >> qexists_tac `vertex` >> simp[]) >>
     metis_tac[fnPlanLineagePathTheory.ssa_output_other_block_no_outputs]) >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) z0 z1` by
    metis_tac[lineage_edge_step] >>
  qpat_assum `LRC _ t _ _`
    (mp_then (Pat `LRC _ _ _ _`) mp_tac lineage_history_incoming_stack_support) >>
  disch_then (qspecl_then [`entry`,`v`] mp_tac) >> simp[] >>
  (impl_tac >- (qexistsl_tac [`lbl`,`bb`,
    `ps with <|ps_cleanup_height := ch'; ps_cleanup_promised := promised|>`,`ops`,`after`] >>
    simp[] >> metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def])) >>
  strip_tac >> suspend "reset"
QED

Resume lineage_state_fresh_phi_return_absent[reset]:
  `LIST_ELEM_COUNT (Var v) after'.ps_stack <= 1` by
    (Cases_on `Var v IN FDOM after'.ps_spilled` >> gvs[]) >>
  qpat_assum `generate_block_plan _ _ _ _ pb input = _`
    (mp_then (Pat `generate_block_plan _ _ _ _ _ _ = _`) mp_tac
      fnPlanLineageObserverTransportTheory.analyzed_supported_join_phi_output_absent) >>
  metis_tac[]
QED

Finalise lineage_state_fresh_phi_return_absent

Theorem lineage_history_first_return_phi_output_absent:
  !fn dfg ch growth spill_base lbl_ctr entry prefix lbl ps bb v segment qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    ~MEM lbl (MAP FST prefix) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) prefix
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    segment <> [] /\ ~MEM lbl (MAP FST (TL segment)) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) segment (lbl,ps) (lbl,qs) ==>
    ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM phi bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  drule_all lineage_history_first_arrival_output_absent >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    (qpat_assum `LRC _ prefix _ _` (mp_then Any mp_tac lineage_history_reconstruct) >> simp[] >>
     disch_then irule >> simp[lineage_state_entry]) >>
  irule lineage_state_fresh_phi_return_absent >> metis_tac[]
QED

Theorem lineage_history_last_label_split:
  !vertices lbl. MEM lbl (MAP FST vertices) ==>
    ?pre old tail. vertices = pre ++ (lbl,old)::tail /\ ~MEM lbl (MAP FST tail)
Proof
  Induct >- simp[] >> rpt gen_tac >> rename1 `MEM lbl (MAP FST (vertex::rest))` >>
  Cases_on `MEM lbl (MAP FST rest)`
  >- (strip_tac >> first_x_assum drule >> strip_tac >>
      qexistsl_tac [`vertex::pre`,`old`,`tail`] >> simp[]) >>
  Cases_on `vertex` >> simp[] >> strip_tac >>
  qexistsl_tac [`[]`,`r`,`rest`] >> gvs[]
QED

Theorem lineage_history_phi_output_absent[local]:
  !vertices fn dfg ch growth spill_base lbl_ctr entry lbl ps bb v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled
Proof
  measureInduct_on `LENGTH vertices` >> rpt gen_tac >> strip_tac >>
  Cases_on `MEM lbl (MAP FST vertices)`
  >- suspend "return" >>
  `?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs` by
    (gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM phi bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  drule_all lineage_history_first_arrival_output_absent >> simp[]
QED

Resume lineage_history_phi_output_absent[return]:
  `?pre old tail. vertices = pre ++ (lbl,old)::tail /\ ~MEM lbl (MAP FST tail)` by
    suspend "last_split" >>
  gvs[fnPlanLineageCallTraceTheory.LRC_APPEND] >>
  suspend "apply_return"
QED

Resume lineage_history_phi_output_absent[last_split]:
  metis_tac[lineage_history_last_label_split]
QED

Resume lineage_history_phi_output_absent[apply_return]:
  `y = (lbl,old)` by
    (qpat_assum `LRC _ ((lbl,old)::tail) _ _` mp_tac >>
     pure_rewrite_tac[Once listTheory.LRC_def] >> metis_tac[]) >> gvs[] >>
  `~MEM (Var v) old.ps_stack /\ Var v NOTIN FDOM old.ps_spilled` by
    (first_x_assum (qspec_then `pre` mp_tac) >> simp[] >>
     disch_then (fn th => qpat_assum `LRC _ pre _ _`
       (mp_then (Pat `LRC _ _ _ _`) mp_tac th)) >> simp[] >> metis_tac[]) >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl old` by
    (qpat_assum `LRC _ pre _ _` (mp_then Any mp_tac lineage_history_reconstruct) >>
     simp[] >> disch_then irule >> simp[lineage_state_entry]) >>
  irule lineage_state_fresh_phi_return_absent >>
  goal_assum (drule_at (Pat `LRC _ _ _ _`)) >> simp[] >> metis_tac[]
QED

Finalise lineage_history_phi_output_absent

Theorem lineage_state_phi_output_absent:
  !fn dfg ch growth spill_base lbl_ctr entry lbl ps bb v.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions))) /\
    lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule lineage_state_history >> strip_tac >> gvs[] >>
  irule lineage_history_phi_output_absent >> metis_tac[]
QED

Theorem ready_ordinary_output_phi_prefix:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= r /\ r < LENGTH bb.bb_instructions /\
  MEM v (EL r bb.bb_instructions).inst_outputs ==>
  !i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    (EL i bb.bb_instructions).inst_outputs <> [] /\
    ~MEM v (EL i bb.bb_instructions).inst_outputs
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qspec_then `bb.bb_instructions` (qx_choose_then `tail` assume_tac)
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  `EL i bb.bb_instructions = EL i (collect_phis bb.bb_instructions)` by
    (qpat_assum `bb.bb_instructions = _ ++ _`
      (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     simp[rich_listTheory.EL_APPEND1]) >>
  `(EL i bb.bb_instructions).inst_opcode = PHI /\
    i < LENGTH bb.bb_instructions` by
    (conj_tac >- metis_tac[livenessTransferProofsTheory.collect_phis_mem, listTheory.EL_MEM] >>
     gvs[] >> decide_tac) >> simp[] >>
  `MEM bb fn.fn_blocks /\ ssa_form fn /\ inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def] >>
     metis_tac[livenessProofsTheory.collect_phis_mem,
       venomExecPropsTheory.lookup_block_MEM, rich_listTheory.EL_MEM]) >>
  conj_tac
  >- (drule_all cfgNormBaseTheory.inst_wf_phi_well_formed >>
      Cases_on `(EL i bb.bb_instructions).inst_outputs` >> gvs[]) >>
  strip_tac >> `i = r` by metis_tac[removeUnusedProofsTheory.ssa_form_position] >> decide_tac
QED

Theorem lineage_state_incoming_ordinary_output_body_absent:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  cfg_reachable_of (cfg_analyze fn) pred /\ fn_reachable fn lbl /\ lbl <> entry /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block pred fn.fn_blocks = SOME pb /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,after) /\
  incoming = ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
  incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled /\
  (MEM (Var v) after.ps_stack ==>
    MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))) /\
  LIST_ELEM_COUNT (Var v) after.ps_stack +
    (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1 /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming
   else ([],incoming)) = (setup_ops,start) /\
  fnPlanLineageEntryProduction$native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn)
    fn lbl halt 0 (LENGTH bb.bb_instructions) bb.bb_instructions start
      (LENGTH (collect_phis bb.bb_instructions)) endpoint /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  LENGTH (collect_phis bb.bb_instructions) <= r /\ r < LENGTH bb.bb_instructions /\
  MEM v (EL r bb.bb_instructions).inst_outputs ==>
  ~MEM (Var v) endpoint.ps_stack /\ Var v NOTIN FDOM endpoint.ps_spilled
Proof
  strip_tac >>
  `!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    EL i bb.bb_instructions = EL i (collect_phis bb.bb_instructions) /\
    (EL i bb.bb_instructions).inst_opcode = PHI` by
    suspend "phi_prefix" >>
  `EVERY (\inst. ~MEM v inst.inst_outputs) (collect_phis bb.bb_instructions)` by
    suspend "ssa" >>
  conj_tac
  >- (`~MEM v (live_vars_at (liveness_analyze fn) lbl
          (LENGTH (collect_phis bb.bb_instructions)))` by
        (irule fnPlanLineageReturnCutTheory.ordinary_output_post_phi_demand_exclusion >>
         metis_tac[]) >>
      mp_tac fnPlanLineageObserverTransportTheory.native_incoming_phi_body_stack_support >>
      asm_rewrite_tac[] >> metis_tac[]) >>
  `Var v NOTIN FDOM ps.ps_spilled` by
    (drule_all lineage_state_defining_outputs_spill_absent >>
     simp[listTheory.EVERY_MEM] >> metis_tac[listTheory.EL_MEM]) >>
  `start.ps_spilled = ps.ps_spilled` by
    (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1` >> gvs[] >>
     imp_res_tac fnPlanLineageInventoryTheory.clean_stack_plan_spilled_unchanged >> gvs[]) >>
  drule fnPlanLineageObserverTransportTheory.native_phi_interval_spilled_unchanged >>
  impl_tac >- metis_tac[] >> simp[]
QED

Resume lineage_state_incoming_ordinary_output_body_absent[phi_prefix]:
  qspec_then `bb.bb_instructions` (qx_choose_then `tail` assume_tac)
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  rpt strip_tac >>
  `EL i bb.bb_instructions = EL i (collect_phis bb.bb_instructions)` by
    (qpat_assum `bb.bb_instructions = _ ++ _`
      (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     simp[rich_listTheory.EL_APPEND1]) >>
  metis_tac[ready_ordinary_output_phi_prefix]
QED

Resume lineage_state_incoming_ordinary_output_body_absent[ssa]:
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  `?i. i < LENGTH (collect_phis bb.bb_instructions) /\
    EL i (collect_phis bb.bb_instructions) = inst` by metis_tac[listTheory.MEM_EL] >>
  `EL i bb.bb_instructions = inst` by metis_tac[] >>
  metis_tac[ready_ordinary_output_phi_prefix]
QED

Finalise lineage_state_incoming_ordinary_output_body_absent

Theorem lineage_history_ordinary_output_body_absent[local]:
  !vertices fn dfg ch growth spill_base lbl_ctr fn_ops ps_end entry lbl ps bb
   h promised setup_ops start endpoint r v halt.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    LRC (lineage_edge (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) vertices
      (entry,init_cleanup_plan_state ch growth spill_base lbl_ctr) (lbl,ps) /\
    generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
      ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
      clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
        (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
       (setup_ops,start) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      halt 0 (LENGTH bb.bb_instructions) bb.bb_instructions start
      (LENGTH (collect_phis bb.bb_instructions)) endpoint /\
    LENGTH (collect_phis bb.bb_instructions) <= r /\ r < LENGTH bb.bb_instructions /\
    MEM v (EL r bb.bb_instructions).inst_outputs ==>
    ~MEM (Var v) endpoint.ps_stack /\ Var v NOTIN FDOM endpoint.ps_spilled
Proof
  measureInduct_on `LENGTH vertices` >> rpt gen_tac >> strip_tac >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps` by
    (drule lineage_history_reconstruct >> simp[] >>
     disch_then irule >> simp[lineage_state_entry]) >>
  Cases_on `MEM lbl (MAP FST vertices)`
  >- suspend "return" >>
  `~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by
    (irule lineage_history_first_arrival_output_absent >>
     goal_assum (drule_at (Pat `LRC _ _ _ _`)) >> simp[] >>
     metis_tac[listTheory.EL_MEM]) >>
  suspend "first_body"
QED

Resume lineage_history_ordinary_output_body_absent[first_body]:
  `LIST_ELEM_COUNT (Var v) ps.ps_stack = 0` by
    simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff] >>
  `~MEM (Var v) start.ps_stack /\ Var v NOTIN FDOM start.ps_spilled` by
    (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1` >> gvs[] >>
     drule fnPlanLineageObserverTransportTheory.clean_stack_plan_resource_nonincrease >>
     disch_then (qspec_then `v` mp_tac) >>
     simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff,
       fnPlanLineageObserverTransportTheory.indicator_zero_iff,
       fnPlanLineageObserverTransportTheory.resource_zero_iff_absent]) >>
  `!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    (EL i bb.bb_instructions).inst_outputs <> [] /\
    ~MEM v (EL i bb.bb_instructions).inst_outputs` by
    (metis_tac[ready_ordinary_output_phi_prefix]) >>
  conj_tac
  >- (drule fnPlanLineageObserverTransportTheory.native_phi_interval_stack_absent >>
      disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  drule fnPlanLineageObserverTransportTheory.native_phi_interval_spilled_unchanged >>
  impl_tac >- metis_tac[] >> simp[]
QED

Resume lineage_history_ordinary_output_body_absent[return]:
  `?pre old tail. vertices = pre ++ (lbl,old)::tail /\ ~MEM lbl (MAP FST tail)` by
    metis_tac[lineage_history_last_label_split] >>
  gvs[fnPlanLineageCallTraceTheory.LRC_APPEND] >>
  `y = (lbl,old)` by
    (qpat_assum `LRC _ ((lbl,old)::tail) _ _` mp_tac >>
     pure_rewrite_tac[Once listTheory.LRC_def] >> metis_tac[]) >> gvs[] >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl old` by
    (qpat_assum `LRC _ pre _ _` (mp_then Any mp_tac lineage_history_reconstruct) >>
     simp[] >> disch_then irule >> simp[lineage_state_entry]) >>
  qpat_x_assum `LRC _ ((lbl,old)::tail) _ _` mp_tac >>
  pure_rewrite_tac[Once listTheory.LRC_def] >> strip_tac >>
  PairCases_on `z` >> gvs[] >>
  drule lineage_edge_physical >> strip_tac >> gvs[] >>
  suspend "previous_body"
QED

Resume lineage_history_ordinary_output_body_absent[previous_body]:
  `bb <> HD fn.fn_blocks` by
    (strip_tac >> gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def, AllCaseEqs()] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >>
     metis_tac[codegen_ready_fn_def]) >>
  drule_all lineage_state_block_native_run >> strip_tac >> gvs[] >>
  `?seed. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions start'
    (LENGTH (collect_phis bb.bb_instructions)) seed` by
    (qpat_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (LENGTH bb.bb_instructions) after` mp_tac >>
     `LENGTH bb.bb_instructions = LENGTH (collect_phis bb.bb_instructions) +
       (LENGTH bb.bb_instructions - LENGTH (collect_phis bb.bb_instructions))` by decide_tac >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     disch_then (mp_then Any strip_assume_tac
       fnPlanLineageEntryProductionTheory.native_inst_prefix_split) >>
     `LENGTH (collect_phis bb.bb_instructions) +
       (LENGTH bb.bb_instructions - LENGTH (collect_phis bb.bb_instructions)) =
       LENGTH bb.bb_instructions` by decide_tac >>
     qexists_tac `mid` >> gvs[]) >>
  `~MEM (Var v) seed.ps_stack /\ Var v NOTIN FDOM seed.ps_spilled` by
    (first_x_assum (qspec_then `pre` mp_tac) >> simp[] >>
     disch_then (fn th => qpat_assum `LRC _ pre _ _`
       (mp_then (Pat `LRC _ _ _ _`) mp_tac th)) >> simp[] >> metis_tac[]) >>
  suspend "outgoing"
QED

Resume lineage_history_ordinary_output_body_absent[outgoing]:
  `~bb_is_halting bb` by
    metis_tac[fnPlanLineageObserverTransportTheory.ready_edge_source_nonhalting] >>
  `(MEM (Var v) after.ps_stack ==> MEM v
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))) /\
    LIST_ELEM_COUNT (Var v) after.ps_stack +
      (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1` by
    (irule lineage_state_body_seeded_ordinary_exit_production >> simp[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >> goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
     qexists_tac `seed` >> fs[]) >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `EVERY (\vertex. !other. lookup_block (FST vertex) fn.fn_blocks = SOME other ==>
    EVERY (\i. ~MEM v i.inst_outputs) other.bb_instructions) tail` by
    (simp[Once listTheory.EVERY_MEM] >> rpt strip_tac >>
     `FST vertex <> bb.bb_label` by
       (strip_tac >> qpat_x_assum `~MEM bb.bb_label (MAP FST tail)` mp_tac >>
        simp[listTheory.MEM_MAP] >> qexists_tac `vertex` >> simp[]) >>
     metis_tac[fnPlanLineagePathTheory.ssa_output_other_block_no_outputs, listTheory.EL_MEM]) >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) z0 z1` by
    metis_tac[lineage_edge_step] >>
  qpat_assum `LRC _ tail _ _`
    (mp_then (Pat `LRC _ _ _ _`) mp_tac lineage_history_incoming_stack_support) >>
  disch_then (qspecl_then [`entry`,`v`] mp_tac) >> simp[] >>
  (impl_tac >- (qexistsl_tac [`bb.bb_label`,`bb`,
    `old with <|ps_cleanup_height := ch'; ps_cleanup_promised := promised'|>`,`ops`,`after`] >>
    simp[] >> metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def])) >>
  strip_tac >> suspend "reset"
QED

Resume lineage_history_ordinary_output_body_absent[reset]:
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    metis_tac[fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule (codegen_ready_fn_def |> iffLR) >> strip_tac >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  irule lineage_state_incoming_ordinary_output_body_absent >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ pb input = _`)) >>
  simp[] >> metis_tac[]
QED

Finalise lineage_history_ordinary_output_body_absent


Theorem lineage_state_ordinary_output_body_absent:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
   else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
     (setup_ops,start) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    halt 0 (LENGTH bb.bb_instructions) bb.bb_instructions start
    (LENGTH (collect_phis bb.bb_instructions)) endpoint /\
  LENGTH (collect_phis bb.bb_instructions) <= r /\ r < LENGTH bb.bb_instructions /\
  MEM v (EL r bb.bb_instructions).inst_outputs ==>
  ~MEM (Var v) endpoint.ps_stack /\ Var v NOTIN FDOM endpoint.ps_spilled
Proof
  strip_tac >> drule lineage_state_history >> strip_tac >> gvs[] >>
  irule lineage_history_ordinary_output_body_absent >> metis_tac[]
QED


Theorem lineage_state_native_post_phi_available:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
   else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
     (setup_ops,start) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions start
    (LENGTH (collect_phis bb.bb_instructions)) seed ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) ==>
    MEM (Var v) seed.ps_stack \/ Var v IN FDOM seed.ps_spilled
Proof
  strip_tac >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  simp[Once lineage_state_cases] >> strip_tac >> gvs[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl' /\ fn_reachable fn lbl` by
    metis_tac[dfs_block_state_reachable, fn_reachable_cfg_analyze] >>
  `MEM lbl' (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >> metis_tac[codegen_ready_fn_def]) >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1`
  >- suspend "singleton" >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl)` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
     rename1 `tail <> []` >> Cases_on `tail` >> gvs[]) >>
  gvs[] >> rpt strip_tac >>
  irule incoming_join_native_post_phi_available >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  qexists_tac `bb` >> simp[] >>
  goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Resume lineage_state_native_post_phi_available[singleton]:
  `cfg_preds_of (cfg_analyze fn) lbl = [lbl']` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
     rename1 `LENGTH tail = 0` >> Cases_on `tail` >> gvs[]) >>
  `MEM bb fn.fn_blocks` by metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  `NULL (collect_phis bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, listTheory.EVERY_MEM] >>
     first_x_assum (qspec_then `bb` mp_tac) >> simp[]) >>
  gvs[listTheory.NULL_EQ, native_inst_prefix_zero] >>
  `EVERY (\v. MEM (Var v) ps_after.ps_stack \/ Var v IN FDOM ps_after.ps_spilled)
    (live_vars_at (liveness_analyze fn) lbl' (LENGTH bb'.bb_instructions))` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     metis_tac[lineage_state_live_out_available]) >>
  drule_at (Pat `clean_stack_plan _ _ _ _ _ = _`) analyzed_single_pred_clean_available >>
  simp[] >> disch_then (qspecl_then [`lbl'`,`bb'`,`bb.bb_label`,`ps_after`] mp_tac) >>
  simp[listTheory.EVERY_MEM]
QED

Finalise lineage_state_native_post_phi_available

Theorem lineage_state_ordinary_instruction_outputs_absent:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
   else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
     (setup_ops,start) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions start r before /\
  LENGTH (collect_phis bb.bb_instructions) <= r /\ r < LENGTH bb.bb_instructions /\
  MEM v (EL r bb.bb_instructions).inst_outputs ==>
  ~MEM (Var v) before.ps_stack /\ Var v NOTIN FDOM before.ps_spilled
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `p = LENGTH (collect_phis bb.bb_instructions)` >>
  `r = p + (r-p)` by decide_tac >>
  `?seed. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions start p seed /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) p (LENGTH bb.bb_instructions) (DROP p bb.bb_instructions) seed (r-p) before` by
    (qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ r before` mp_tac >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     strip_tac >>
     drule (Q.SPECL [`r-p`,`p`] fnPlanLineageEntryProductionTheory.native_inst_prefix_split) >>
     simp[] >> `p+(r-p) = r` by decide_tac >> gvs[]) >>
  `~MEM (Var v) seed.ps_stack /\ Var v NOTIN FDOM seed.ps_spilled` by
    (irule lineage_state_ordinary_output_body_absent >>
     goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
     simp[Abbr `p`] >> metis_tac[]) >>
  drule fnPlanLineageObserverTransportTheory.native_ordinary_interval_absent >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  impl_tac >- suspend "interval" >> simp[]
QED

Resume lineage_state_ordinary_instruction_outputs_absent[interval]:
  conj_tac >- suspend "layout" >> suspend "available"
QED

Resume lineage_state_ordinary_instruction_outputs_absent[layout]:
  `bb <> HD fn.fn_blocks` by
    (strip_tac >> gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def, AllCaseEqs()] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >> metis_tac[codegen_ready_fn_def]) >>
  rpt gen_tac >> strip_tac >>
  `p+j < r /\ p+j < LENGTH bb.bb_instructions /\ p <= p+j` by decide_tac >>
  `EL j (DROP p bb.bb_instructions) = EL (p+j) bb.bb_instructions` by
    simp[listTheory.EL_DROP, arithmeticTheory.ADD_COMM] >>
  `inst_wf (EL (p+j) bb.bb_instructions) /\ codegen_ready_inst (EL (p+j) bb.bb_instructions)` by
    (`MEM (EL (p+j) bb.bb_instructions) bb.bb_instructions` by
       (irule listTheory.EL_MEM >> decide_tac) >>
     gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM] >>
     metis_tac[]) >>
  `!i. p <= i /\ i < LENGTH bb.bb_instructions ==>
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    ((EL i bb.bb_instructions).inst_opcode = JMP ==> SUC i = LENGTH bb.bb_instructions)` by
    (qspecl_then [`fn`,`bb`,`p`] mp_tac
       fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
     simp[Abbr `p`]) >>
  `(EL (p+j) bb.bb_instructions).inst_opcode <> JMP /\
    (EL (p+j) bb.bb_instructions).inst_opcode <> PHI` by
    (first_x_assum (qspec_then `p+j` mp_tac) >> simp[] >> decide_tac) >>
  gvs[] >> conj_tac >- gvs[codegen_ready_inst_def] >>
  conj_tac
  >- (strip_tac >> gvs[venomWfTheory.inst_wf_def] >>
      Cases_on `(EL (p+j) bb.bb_instructions).inst_outputs` >> gvs[]) >>
  strip_tac >> `ssa_form fn` by metis_tac[codegen_ready_fn_def] >>
  `j+p < LENGTH bb.bb_instructions` by decide_tac >>
  `j+p = r` by metis_tac[removeUnusedProofsTheory.ssa_form_position] >> decide_tac
QED

Resume lineage_state_ordinary_instruction_outputs_absent[available]:
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >> metis_tac[codegen_ready_fn_def]) >>
  `!w. MEM w (live_vars_at (liveness_analyze fn) bb.bb_label p) ==>
    MEM (Var w) seed.ps_stack \/ Var w IN FDOM seed.ps_spilled` by
    (metis_tac[lineage_state_native_post_phi_available]) >>
  rpt gen_tac >> strip_tac >>
  irule fnPlanLineageObserverTransportTheory.native_ordinary_suffix_computed_available >>
  qexists_tac `bb` >> simp[] >>
  goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  `!i. p <= i /\ i < LENGTH bb.bb_instructions ==>
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    ((EL i bb.bb_instructions).inst_opcode = JMP ==> SUC i = LENGTH bb.bb_instructions)` by
    (qspecl_then [`fn`,`bb`,`p`] mp_tac
       fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
     simp[Abbr `p`]) >>
  gen_tac >> disch_tac >>
  `p+i < r /\ p+i < LENGTH bb.bb_instructions /\ p <= p+i` by decide_tac >>
  `EL i (DROP p bb.bb_instructions) = EL (p+i) bb.bb_instructions` by
    simp[listTheory.EL_DROP, arithmeticTheory.ADD_COMM] >>
  first_x_assum (qspec_then `p+i` mp_tac) >> gvs[] >> decide_tac
QED

Finalise lineage_state_ordinary_instruction_outputs_absent

Theorem lineage_state_phi_instruction_outputs_absent:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
   else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
     (setup_ops,start) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions start r before /\
  r < LENGTH (collect_phis bb.bb_instructions) /\
  MEM v (EL r bb.bb_instructions).inst_outputs ==>
  ~MEM (Var v) before.ps_stack /\ Var v NOTIN FDOM before.ps_spilled
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ fn_reachable fn lbl` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem,
      venomExecPropsTheory.lookup_block_label, lineage_state_reachable,
      fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >>
     metis_tac[codegen_ready_fn_def]) >>
  `!i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    EL i bb.bb_instructions = EL i (collect_phis bb.bb_instructions) /\
    (EL i bb.bb_instructions).inst_opcode = PHI` by suspend "layout" >>
  `~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by
    (irule lineage_state_phi_output_absent >>
     goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
     simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[rich_listTheory.EL_MEM]) >>
  conj_tac >- suspend "stack" >>
  `start.ps_spilled = ps.ps_spilled` by
    (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1` >> gvs[] >>
     imp_res_tac fnPlanLineageInventoryTheory.clean_stack_plan_spilled_unchanged >> gvs[]) >>
  drule fnPlanLineageObserverTransportTheory.native_phi_interval_spilled_unchanged >>
  impl_tac >- (rpt strip_tac >> metis_tac[arithmeticTheory.LESS_TRANS]) >> simp[]
QED

Resume lineage_state_phi_instruction_outputs_absent[layout]:
  qspec_then `bb.bb_instructions` (qx_choose_then `tail` assume_tac)
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  rpt strip_tac >>
  `EL i bb.bb_instructions = EL i (collect_phis bb.bb_instructions)` by
    (qpat_assum `bb.bb_instructions = _ ++ _`
      (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [th]) >>
     simp[rich_listTheory.EL_APPEND1]) >>
  metis_tac[livenessTransferProofsTheory.collect_phis_mem, listTheory.EL_MEM]
QED

Resume lineage_state_phi_instruction_outputs_absent[stack]:
  irule (cj 1 fnPlanLineageObserverTransportTheory.native_setup_prefix_dead_stack) >>
  qexistsl_tac [`bb`,`dfg`,`fn`,`r`] >> simp[] >>
  qexistsl_tac [`ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`,`setup_ops`,`start`] >>
  simp[] >> rpt strip_tac >> rename1 `i < r` >>
  `i < LENGTH bb.bb_instructions /\ r < LENGTH bb.bb_instructions` by
    (qspec_then `bb.bb_instructions` strip_assume_tac
       fnPlanLineageLivenessTheory.collect_phis_prefix >>
     `LENGTH bb.bb_instructions = LENGTH (collect_phis bb.bb_instructions) + LENGTH rest` by
       metis_tac[listTheory.LENGTH_APPEND] >> decide_tac) >>
  `i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `MEM v (EL i bb.bb_instructions).inst_outputs` by metis_tac[] >>
  `ssa_form fn` by metis_tac[codegen_ready_fn_def] >>
  `i = r` by metis_tac[removeUnusedProofsTheory.ssa_form_position] >> decide_tac
QED

Finalise lineage_state_phi_instruction_outputs_absent

Theorem lineage_state_nonentry_prefix_unit_bound:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
    (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) = SOME (ops,after) /\
  (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
   else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
     (setup_ops,start) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions start k qs /\
  k <= LENGTH bb.bb_instructions /\
  LIST_ELEM_COUNT (Var v) ps.ps_stack + (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 ==>
  LIST_ELEM_COUNT (Var v) qs.ps_stack + (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  strip_tac >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >>
     metis_tac[codegen_ready_fn_def, livenessTransferProofsTheory.lookup_block_mem]) >>
  drule_all lineage_state_block_native_run >> strip_tac >> gvs[] >>
  `LIST_ELEM_COUNT (Var v) start.ps_stack +
    (if Var v IN FDOM start.ps_spilled then 1 else 0) <= 1` by
    (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1` >> gvs[] >>
     drule fnPlanLineageObserverTransportTheory.clean_stack_plan_resource_nonincrease >>
     disch_then (qspec_then `v` mp_tac) >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k qs`
    (mp_then Any (qspec_then `bb` mp_tac)
      fnPlanLineageObserverTransportTheory.native_inst_prefix_fresh_cuts_resource_bound) >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >>
  impl_tac >- suspend "premises" >> simp[]
QED

Resume lineage_state_nonentry_prefix_unit_bound[premises]:
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `j < LENGTH (collect_phis bb.bb_instructions)`
      >- (irule lineage_state_phi_instruction_outputs_absent >>
          goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
          simp[] >> metis_tac[]) >>
      irule lineage_state_ordinary_instruction_outputs_absent >>
      goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
      simp[] >> metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  rpt gen_tac >> strip_tac >>
  `j < LENGTH bb.bb_instructions` by decide_tac >>
  qpat_x_assum `!j before w. _` (qspecl_then [`j`,`before`,`w`] mp_tac) >> simp[]
QED

Finalise lineage_state_nonentry_prefix_unit_bound

Theorem lineage_state_entry_initial:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME lbl /\
  lineage_state lv dfg (cfg_analyze fn) fn ps0 lbl ps ==> ps = ps0
Proof
  strip_tac >> qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  simp[Once lineage_state_cases] >> strip_tac >> gvs[] >>
  `fn.fn_blocks <> [] /\ lbl = (HD fn.fn_blocks).bb_label` by
    (gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
         listTheory.NULL_EQ, AllCaseEqs()]) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  metis_tac[fnPlanLineageObserverTransportTheory.ready_incoming_block_nonentry]
QED

Theorem lineage_dfs_entry_block_outgoing_core:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME lbl /\
  lineage_state lv dfg (cfg_analyze fn) fn ps0 lbl psL /\
  dfs_block_state lv dfg (cfg_analyze fn) fn ps0 lbl psD /\
  generate_block_plan lv dfg (cfg_analyze fn) fn bb psD = SOME (ops,afterD)
  ==> ?afterL prefixL prefixD out.
    generate_block_plan lv dfg (cfg_analyze fn) fn bb psL = SOME (ops,afterL) /\
    prefixL = [] /\ prefixD = [] /\
    afterL = out with ps_stack := prefixL ++ out.ps_stack /\
    afterD = out with ps_stack := prefixD ++ out.ps_stack /\
    (!v. MEM v (live_vars_at lv lbl (LENGTH bb.bb_instructions)) ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)
Proof
  strip_tac >>
  drule dfs_block_state_lineage_state >> strip_tac >>
  `psL = ps0 /\ psD = ps0` by metis_tac[lineage_state_entry_initial] >>
  gvs[] >> qexistsl_tac [`afterD`,`[]`,`[]`,`afterD`] >> simp[]
QED

Theorem lineage_dfs_entry_block_replay:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME lbl /\
  lineage_state lv dfg (cfg_analyze fn) fn ps0 lbl psL /\
  dfs_block_state lv dfg (cfg_analyze fn) fn ps0 lbl psD /\
  generate_block_plan lv dfg (cfg_analyze fn) fn bb psD = SOME (ops,afterD)
  ==> ?afterL.
    generate_block_plan lv dfg (cfg_analyze fn) fn bb psL = SOME (ops,afterL) /\
    afterL.ps_alloc = afterD.ps_alloc /\ afterL.ps_spilled = afterD.ps_spilled
Proof
  strip_tac >> drule_all lineage_dfs_entry_block_outgoing_core >> strip_tac >>
  qexists_tac `afterL` >> simp[]
QED

Theorem lineage_state_block_unit_preservation:
  codegen_ready_fn fn /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
    (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) = SOME (ops,after) /\
  LIST_ELEM_COUNT (Var v) ps.ps_stack + (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 ==>
  LIST_ELEM_COUNT (Var v) after.ps_stack + (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  strip_tac >>
  `?entry. fn_entry_label fn = SOME entry` by metis_tac[lineage_state_has_entry] >>
  Cases_on `lbl = entry`
  >- (`ps = init_cleanup_plan_state ch growth spill_base lbl_ctr` by
        metis_tac[lineage_state_entry_initial] >>
      irule lineage_state_block_fresh_output_resource_bound >>
      goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >> simp[] >>
      metis_tac[]) >>
  drule_all lineage_state_block_native_run >> strip_tac >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >> metis_tac[codegen_ready_fn_def]) >>
  gvs[] >> irule lineage_state_nonentry_prefix_unit_bound >>
  goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem lineage_state_unit_resources:
  !fn dfg ch growth spill_base lbl_ctr fn_ops ps_end.
    codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
      ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) ==>
    !lbl ps. lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps ==>
    !v. LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac lineage_state_strongind >>
  conj_tac >- simp[init_cleanup_plan_state_def, init_plan_state_def,
                   rich_listTheory.LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> strip_tac >> gen_tac >> gvs[] >>
  metis_tac[lineage_state_block_unit_preservation]
QED

Theorem lineage_state_successful_exit_unit_resources:
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
    (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) = SOME (ops,after) ==>
  !v. LIST_ELEM_COUNT (Var v) after.ps_stack +
    (if Var v IN FDOM after.ps_spilled then 1 else 0) <= 1
Proof
  strip_tac >> gen_tac >> irule lineage_state_block_unit_preservation >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >> simp[] >>
  metis_tac[lineage_state_unit_resources]
QED

Theorem lineage_state_prefix_unit_resources:
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
    (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) = SOME (ops,after) /\
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
    (LENGTH bb.bb_instructions) (non_param_insts bb) start k qs /\
  k <= LENGTH (non_param_insts bb) ==>
  !v. LIST_ELEM_COUNT (Var v) qs.ps_stack +
    (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  strip_tac >> gen_tac >>
  `?entry. fn_entry_label fn = SOME entry` by metis_tac[lineage_state_has_entry] >>
  Cases_on `lbl = entry`
  >- (`ps = init_cleanup_plan_state ch growth spill_base lbl_ctr` by
        metis_tac[lineage_state_entry_initial] >>
      `~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by
        simp[init_cleanup_plan_state_def, init_plan_state_def] >>
      gvs[] >> irule lineage_state_fresh_input_prefix_resource_bound >>
      goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (irule fnPlanLineageJoinEntryTheory.nonentry_block_no_params >>
     metis_tac[codegen_ready_fn_def, livenessTransferProofsTheory.lookup_block_mem]) >>
  gvs[] >> irule lineage_state_nonentry_prefix_unit_bound >>
  goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[lineage_state_unit_resources]
QED

Theorem lineage_state_phi_schedule_unit_resources:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  phi_schedule_run
    (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) lbl (SUC i), halting))
      (collect_phis bb.bb_instructions)) ps = (ops,qs) ==>
  !v. LIST_ELEM_COUNT (Var v) qs.ps_stack +
    (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  strip_tac >> gen_tac >>
  drule fnPlanLineageObserverTransportTheory.phi_schedule_run_resource_bound >>
  disch_then (qspec_then `v` mp_tac) >>
  simp[indexedListsTheory.MAP_MAPi, combinTheory.o_DEF] >>
  `ALL_DISTINCT (MAP (\inst. HD inst.inst_outputs) (collect_phis bb.bb_instructions))` by
    (irule fnPlanLineagePhiSuffixResourcesTheory.ready_phi_write_names_distinct >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  `LIST_ELEM_COUNT v (MAP (\inst. HD inst.inst_outputs) (collect_phis bb.bb_instructions)) <= 1` by
    metis_tac[fnPlanLineageInventoryTheory.all_distinct_elem_count_le_one] >>
  Cases_on `MEM v (MAP (\inst. HD inst.inst_outputs) (collect_phis bb.bb_instructions))`
  >- (`MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis bb.bb_instructions)))` by
        (gvs[listTheory.MEM_MAP, listTheory.MEM_FLAT] >>
         `venomWf$inst_wf inst /\ inst.inst_opcode = PHI` by
           (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM] >>
            metis_tac[livenessTransferProofsTheory.collect_phis_mem,
                      venomExecPropsTheory.lookup_block_MEM]) >>
         `LENGTH inst.inst_outputs = 1` by gvs[venomWfTheory.inst_wf_def] >>
         Cases_on `inst.inst_outputs` >> gvs[] >> metis_tac[listTheory.MEM]) >>
      `~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by
        metis_tac[lineage_state_phi_output_absent] >>
      `LIST_ELEM_COUNT (Var v) ps.ps_stack = 0` by
        simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff] >>
      simp[] >> decide_tac) >>
  `LIST_ELEM_COUNT v (MAP (\inst. HD inst.inst_outputs) (collect_phis bb.bb_instructions)) = 0` by
    simp[fnPlanLineageObserverTransportTheory.elem_count_zero_iff] >>
  `LIST_ELEM_COUNT (Var v) ps.ps_stack + (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1` by
    metis_tac[lineage_state_unit_resources] >> simp[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem lineage_state_join_phi_schedule_ordinary_output_absent:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <> 1 /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  phi_schedule_run
    (MAPi (\j inst. (inst,live_vars_at (liveness_analyze fn) lbl (j+1),halt))
      (collect_phis bb.bb_instructions)) ps = (ops,endpoint) /\
  LENGTH (collect_phis bb.bb_instructions) <= r /\ r < LENGTH bb.bb_instructions /\
  MEM v (EL r bb.bb_instructions).inst_outputs ==>
  ~MEM (Var v) endpoint.ps_stack /\ Var v NOTIN FDOM endpoint.ps_spilled
Proof
  strip_tac >>
  `native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl halt 0
    (LENGTH bb.bb_instructions) bb.bb_instructions ps
    (LENGTH (collect_phis bb.bb_instructions)) endpoint` by
    (irule fnPlanLineageObserverTransportTheory.ready_phi_schedule_native_inst_prefix >>
     metis_tac[]) >>
  irule lineage_state_ordinary_output_body_absent >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >> simp[] >>
  qexistsl_tac [`ps.ps_cleanup_height`,`halt`,`ps.ps_cleanup_promised`,`r`] >>
  simp[] >> metis_tac[]
QED

(* With no PHIs the incoming join target is predecessor-independent.  Unit
   resources exclude live copies from each otherwise arbitrary residual. *)
Theorem lineage_dfs_empty_phi_join_seed_actual:
  codegen_ready_fn fn /\ fn_entry_label fn <> SOME lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  collect_phis bb.bb_instructions = [] /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psD ==>
  ?prefixL prefixD.
    psL.ps_stack = prefixL ++ MAP Var (live_vars_at (liveness_analyze fn) lbl 0) /\
    psD.ps_stack = prefixD ++ MAP Var (live_vars_at (liveness_analyze fn) lbl 0) /\
    psL.ps_spilled = FEMPTY /\ psD.ps_spilled = FEMPTY /\
    psL = psD with ps_stack :=
      prefixL ++ MAP Var (live_vars_at (liveness_analyze fn) lbl 0) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)
Proof
  strip_tac >>
  drule_all lineage_state_join_boundary >>
  simp[livenessDefsTheory.input_vars_from_def] >> strip_tac >>
  drule_all dfs_block_state_join_boundary >>
  simp[livenessDefsTheory.input_vars_from_def] >> strip_tac >>
  rename1 `psL.ps_stack = prefixL ++ _` >>
  rename1 `psD.ps_stack = prefixD ++ _` >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psD` by
    metis_tac[dfs_block_state_lineage_state] >>
  `psL = psD with ps_stack := psL.ps_stack` by
    metis_tac[lineage_state_actual_dfs_fields] >>
  qexists_tac `prefixD` >> simp[] >>
  conj_tac >- metis_tac[] >>
  gen_tac >> strip_tac >>
  `MEM (Var v) (MAP Var (live_vars_at (liveness_analyze fn) lbl 0))` by
    simp[listTheory.MEM_MAP] >>
  `LIST_ELEM_COUNT (Var v) psL.ps_stack +
    (if Var v IN FDOM psL.ps_spilled then 1 else 0) <= 1` by
    metis_tac[lineage_state_unit_resources] >>
  `LIST_ELEM_COUNT (Var v) psD.ps_stack +
    (if Var v IN FDOM psD.ps_spilled then 1 else 0) <= 1` by
    metis_tac[lineage_state_unit_resources] >>
  metis_tac[fnPlanLineageNativeResourcesTheory.resource_suffix_cancel]
QED

Theorem lineage_dfs_join_phi_common_suffix_actual:
  !fn entry succ sb dfg ch growth spill_base lbl_ctr fn_ops ps_end psL psD halting.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
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
        (LENGTH (collect_phis sb.bb_instructions))) ==> LIST_ELEM_COUNT (Var v) suffix = 1) /\
    EVERY (\v. ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD /\
      Var v NOTIN FDOM psL.ps_spilled /\ Var v NOTIN FDOM psD.ps_spilled)
      (live_vars_at (liveness_analyze fn) succ (LENGTH (collect_phis sb.bb_instructions))) /\
    (!j v. LENGTH (collect_phis sb.bb_instructions) <= j /\
      j < LENGTH sb.bb_instructions /\
      (MEM (Var v) (compute_operands (EL j sb.bb_instructions)) \/
       MEM v (live_vars_at (liveness_analyze fn) succ (SUC j)) \/
       MEM v (EL j sb.bb_instructions).inst_outputs) ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_actual_dfs_alloc >> strip_tac >>
  `?prefixL prefixD suffix ops al.
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
        (LENGTH (collect_phis sb.bb_instructions))) ==> LIST_ELEM_COUNT (Var v) suffix = 1)` by
    (Cases_on `collect_phis sb.bb_instructions = []`
     >- suspend "empty_seed"
     >> irule lineage_dfs_join_phi_common_suffix >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[listTheory.NULL_EQ]) >>
  `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psD` by
    metis_tac[dfs_block_state_lineage_state] >>
  qexistsl_tac [`prefixL`,`prefixD`,`suffix`,`ops`,`al`] >> simp[listTheory.EVERY_MEM] >>
  conj_asm1_tac >- suspend "live_exclusion" >>
  suspend "ordinary_footprint"
QED

Resume lineage_dfs_join_phi_common_suffix_actual[empty_seed]:
  `fn_entry_label fn <> SOME succ` by simp[] >>
  drule_all lineage_dfs_empty_phi_join_seed_actual >> strip_tac >>
  qexistsl_tac [`prefixL`,`prefixD`,
    `MAP Var (live_vars_at (liveness_analyze fn) succ 0)`,`[]`,`psD.ps_alloc`] >>
  simp[fnPlanLineagePhiTemporalTheory.phi_schedule_run_def,
    plan_state_component_equality, listTheory.MEM_MAP] >>
  gen_tac >> strip_tac >>
  `MEM (Var v) (MAP Var (live_vars_at (liveness_analyze fn) succ 0))` by
    simp[listTheory.MEM_MAP] >>
  `LIST_ELEM_COUNT (Var v) psL.ps_stack +
    (if Var v IN FDOM psL.ps_spilled then 1 else 0) <= 1` by
    metis_tac[lineage_state_unit_resources] >>
  metis_tac[fnPlanLineageNativeResourcesTheory.resource_suffix_cancel]
QED

Resume lineage_dfs_join_phi_common_suffix_actual[live_exclusion]:
  rpt strip_tac >>
  `LIST_ELEM_COUNT (Var v) (prefixL ++ suffix) +
    (if Var v IN FDOM psL.ps_spilled then 1 else 0) <= 1` by
    (qpat_assum `phi_schedule_run _ psL = _`
       (mp_then Any mp_tac lineage_state_phi_schedule_unit_resources) >>
     simp[] >> metis_tac[]) >>
  `LIST_ELEM_COUNT (Var v) (prefixD ++ suffix) +
    (if Var v IN FDOM psD.ps_spilled then 1 else 0) <= 1` by
    (qpat_assum `phi_schedule_run _ psD = _`
       (mp_then Any mp_tac lineage_state_phi_schedule_unit_resources) >>
     simp[] >> metis_tac[]) >>
  metis_tac[fnPlanLineageNativeResourcesTheory.resource_suffix_cancel]
QED

Resume lineage_dfs_join_phi_common_suffix_actual[ordinary_footprint]:
  `!r v. LENGTH (collect_phis sb.bb_instructions) <= r /\ r < LENGTH sb.bb_instructions /\
      MEM v (EL r sb.bb_instructions).inst_outputs ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD` by suspend "output_exclusion" >>
  `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `fn_reachable fn sb.bb_label` by
    metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  qpat_x_assum `sb.bb_label = succ` (SUBST_ALL_TAC o SYM) >>
  rpt gen_tac >> strip_tac
  >- (drule_all fnPlanLineageCallersTheory.interval_computed_query_origin >>
      strip_tac >- metis_tac[] >>
      `k < LENGTH sb.bb_instructions` by decide_tac >> metis_tac[])
  >- (`LENGTH (collect_phis sb.bb_instructions) <= SUC j /\
        SUC j <= LENGTH sb.bb_instructions` by decide_tac >>
      drule_all fnPlanLineageCallersTheory.interval_live_origin >>
      strip_tac >- metis_tac[] >>
      `k < LENGTH sb.bb_instructions` by decide_tac >> metis_tac[]) >>
  metis_tac[]
QED

Resume lineage_dfs_join_phi_common_suffix_actual[output_exclusion]:
  rpt gen_tac >> strip_tac >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) succ) <> 1` by decide_tac >>
  fs[arithmeticTheory.ADD1] >>
  qpat_assum `phi_schedule_run _ psL = _`
    (mp_then Any (drule_all_then strip_assume_tac)
      lineage_state_join_phi_schedule_ordinary_output_absent) >>
  qpat_assum `phi_schedule_run _ psD = _`
    (mp_then Any (drule_all_then strip_assume_tac)
      lineage_state_join_phi_schedule_ordinary_output_absent) >>
  gvs[]
QED

Finalise lineage_dfs_join_phi_common_suffix_actual

Theorem lineage_dfs_join_ordinary_paired_interval_actual:
  !fn entry succ sb dfg ch growth spill_base lbl_ctr fn_ops ps_end psL psD halting.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psD ==>
  ?prefixL prefixD suffix phi_ops al p0 xs.
    p0 = psD with <|ps_stack := suffix; ps_alloc := al|> /\
    xs = DROP (LENGTH (collect_phis sb.bb_instructions)) sb.bb_instructions /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) psL =
      (phi_ops, psL with <|ps_stack := prefixL ++ suffix; ps_alloc := al|>) /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) psD =
      (phi_ops, psD with <|ps_stack := prefixD ++ suffix; ps_alloc := al|>) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
       (LENGTH (collect_phis sb.bb_instructions))) ==> MEM (Var v) p0.ps_stack) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions)) ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD) /\
    (!k. k <= LENGTH xs /\
      (!j. j < k ==> (EL j xs).inst_opcode <> JMP /\ (EL j xs).inst_opcode <> PHI) ==>
      ?ops q.
        native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ halting
          (LENGTH (collect_phis sb.bb_instructions)) (LENGTH sb.bb_instructions) xs
          p0 k ops q /\
        native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ halting
          (LENGTH (collect_phis sb.bb_instructions)) (LENGTH sb.bb_instructions) xs
          (p0 with ps_stack := prefixL ++ p0.ps_stack) k ops
          (q with ps_stack := prefixL ++ q.ps_stack) /\
        native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ halting
          (LENGTH (collect_phis sb.bb_instructions)) (LENGTH sb.bb_instructions) xs
          (p0 with ps_stack := prefixD ++ p0.ps_stack) k ops
          (q with ps_stack := prefixD ++ q.ps_stack))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_dfs_join_phi_common_suffix_actual >>
  disch_then (qspec_then `halting` strip_assume_tac) >>
  `fn_entry_label fn <> SOME succ` by simp[] >>
  drule_all fnPlanLineagePhiScheduleTheory.ready_nonentry_block_suffix >> strip_tac >>
  `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `fn_reachable fn sb.bb_label` by
    metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `0 < LENGTH sb.bb_instructions /\
    LENGTH (collect_phis sb.bb_instructions) <= PRE (LENGTH sb.bb_instructions)` by
    (qpat_x_assum `sb.bb_instructions = _ ++ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> Cases_on `rest` >> gvs[]) >>
  `SUC (PRE (LENGTH sb.bb_instructions)) = LENGTH sb.bb_instructions` by decide_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions)) ==>
    ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD` by
    (rpt strip_tac >>
     qpat_assum `!j v. _`
       (qspecl_then [`PRE (LENGTH sb.bb_instructions)`,`v`] mp_tac) >>
     simp[]) >>
  qexistsl_tac [`prefixL`,`prefixD`,`suffix`,`ops`,`al`,
    `psD with <|ps_stack := suffix; ps_alloc := al|>`,
    `DROP (LENGTH (collect_phis sb.bb_instructions)) sb.bb_instructions`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
  qpat_x_assum `sb.bb_label = succ` (SUBST_ALL_TAC o SYM) >>
  irule fnPlanLineageEntryProductionTheory.analyzed_ordinary_paired_interval_replay >>
  simp[] >> gen_tac >> strip_tac >>
  `LENGTH (collect_phis sb.bb_instructions) + j < LENGTH sb.bb_instructions` by
    (fs[] >> decide_tac) >>
  simp[listTheory.EVERY_MEM,listTheory.EL_DROP] >> rpt strip_tac >>
  qpat_assum `!j v. _` (qspecl_then [`LENGTH (collect_phis sb.bb_instructions) + j`,`v`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem lineage_dfs_join_physical_start_actual:
  !fn entry succ sb dfg ch growth spill_base lbl_ctr fn_ops ps_end psL psD.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psD ==>
  ?prefixL prefixD suffix phi_ops al p0 xs qL qD.
    p0 = psD with <|ps_stack := suffix; ps_alloc := al|> /\
    xs = DROP (LENGTH (collect_phis sb.bb_instructions)) sb.bb_instructions /\
    get_params sb.bb_instructions = [] /\ xs <> [] /\
    qL = p0 with ps_stack := prefixL ++ p0.ps_stack /\
    qD = p0 with ps_stack := prefixD ++ p0.ps_stack /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
       (LENGTH (collect_phis sb.bb_instructions))) ==> MEM (Var v) p0.ps_stack) /\
    (!p q. (p = psL /\ q = qL) \/ (p = psD /\ q = qD) ==>
      phi_schedule_run
        (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i),
          bb_is_halting sb)) (collect_phis sb.bb_instructions)) p = (phi_ops,q) /\
      generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb p =
        case generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
          succ (bb_is_halting sb) 0 (LENGTH sb.bb_instructions)
          (LENGTH (collect_phis sb.bb_instructions)) xs q of
          NONE => NONE
        | SOME (tail_ops,out) => if revert_block_spills sb (phi_ops ++ tail_ops)
            then NONE else SOME ([SOLabel succ] ++ phi_ops ++ tail_ops,out)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions)) ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD) /\
    (!k. k <= LENGTH xs /\
      (!j. j < k ==> (EL j xs).inst_opcode <> JMP /\ (EL j xs).inst_opcode <> PHI) ==>
      ?ops q.
        native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
          (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
          (LENGTH sb.bb_instructions) xs p0 k ops q /\
        native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
          (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
          (LENGTH sb.bb_instructions) xs qL k ops
          (q with ps_stack := prefixL ++ q.ps_stack) /\
        native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
          (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
          (LENGTH sb.bb_instructions) xs qD k ops
          (q with ps_stack := prefixD ++ q.ps_stack) /\
        (!v. MEM v (live_vars_at (liveness_analyze fn) succ
          (LENGTH (collect_phis sb.bb_instructions) + k)) ==>
          MEM (Var v) q.ps_stack \/ Var v IN FDOM q.ps_spilled))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_dfs_join_ordinary_paired_interval_actual >>
  disch_then (qspec_then `bb_is_halting sb` strip_assume_tac) >>
  `fn_entry_label fn <> SOME succ` by simp[] >>

  `psL with <|ps_stack := prefixL ++ suffix; ps_alloc := al|> =
   p0 with ps_stack := prefixL ++ p0.ps_stack` by
    (drule_all lineage_state_actual_dfs_fields >> disch_then (fn th => simp[Once th])) >>
  `psD with <|ps_stack := prefixD ++ suffix; ps_alloc := al|> =
   p0 with ps_stack := prefixD ++ p0.ps_stack` by simp[] >>
  qexistsl_tac [`prefixL`,`prefixD`,`suffix`,`phi_ops`,`al`,`p0`,`xs`,
    `p0 with ps_stack := prefixL ++ p0.ps_stack`,
    `p0 with ps_stack := prefixD ++ p0.ps_stack`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  `get_params sb.bb_instructions = [] /\ xs <> []` by
    (drule_all fnPlanLineagePhiScheduleTheory.ready_nonentry_block_suffix >>
     strip_tac >>
     qpat_x_assum `sb.bb_instructions = _ ++ _`
       (mp_tac o Q.AP_TERM `DROP (LENGTH (collect_phis sb.bb_instructions))`) >>
     simp_tac (srw_ss()) [listTheory.DROP_APPEND] >> metis_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >> conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- REFL_TAC >> conj_tac >- REFL_TAC >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "block_equations" >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qpat_x_assum `p0 = _` kall_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!k. _ ==> ?ops q. _` (qspec_then `k` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`ops`,`q`] >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >> suspend "core_coverage"
QED

Resume lineage_dfs_join_physical_start_actual[block_equations]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qpat_x_assum `q = _` SUBST_ALL_TAC >>
  conj_asm1_tac >- metis_tac[] >>
  qpat_x_assum `p0 = _` kall_tac >>
  drule_all fnPlanLineagePhiScheduleTheory.generate_join_block_plan_phi_schedule >>
  disch_then (qspec_then `dfg` strip_assume_tac) >>
  qpat_x_assum `sb.bb_instructions = _ ++ _`
    (mp_tac o Q.AP_TERM `DROP (LENGTH (collect_phis sb.bb_instructions))`) >>
  simp_tac (srw_ss()) [listTheory.DROP_APPEND] >> simp[]
QED

Resume lineage_dfs_join_physical_start_actual[core_coverage]:
  `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `fn_reachable fn sb.bb_label` by
    metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `non_param_insts sb = sb.bb_instructions` by
    (drule_all fnPlanLineagePhiScheduleTheory.ready_nonentry_block_suffix >> simp[]) >>
  qpat_x_assum `sb.bb_label = succ` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `native_inst_ops_prefix _ _ _ _ _ _ _ _ _ p0 _ _ q`
    (mp_then Any mp_tac fnPlanLineageEntryProductionTheory.native_inst_ops_prefix_erase) >>
  disch_then (mp_then Any mp_tac
    fnPlanLineageEntryProductionTheory.native_ordinary_interval_available) >>
  disch_then (qspecl_then [`sb`,`LENGTH (collect_phis sb.bb_instructions)`] mp_tac) >>
  simp[] >> gvs[]
QED

Finalise lineage_dfs_join_physical_start_actual

Theorem lineage_dfs_join_preterminal_core_actual:
  !fn entry succ sb dfg ch growth spill_base lbl_ctr fn_ops ps_end psL psD.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psD ==>
  ?prefixL prefixD suffix phi_ops al p0 xs qL qD ops q.
    p0 = psD with <|ps_stack := suffix; ps_alloc := al|> /\
    xs = DROP (LENGTH (collect_phis sb.bb_instructions)) sb.bb_instructions /\
    xs <> [] /\
    qL = p0 with ps_stack := prefixL ++ p0.ps_stack /\
    qD = p0 with ps_stack := prefixD ++ p0.ps_stack /\
    (!p r. (p = psL /\ r = qL) \/ (p = psD /\ r = qD) ==>
      phi_schedule_run
        (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i),
          bb_is_halting sb)) (collect_phis sb.bb_instructions)) p = (phi_ops,r)) /\
    native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
      (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
      (LENGTH sb.bb_instructions) xs p0 (PRE (LENGTH xs)) ops q /\
    native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
      (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
      (LENGTH sb.bb_instructions) xs qL (PRE (LENGTH xs)) ops
      (q with ps_stack := prefixL ++ q.ps_stack) /\
    native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
      (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
      (LENGTH sb.bb_instructions) xs qD (PRE (LENGTH xs)) ops
      (q with ps_stack := prefixD ++ q.ps_stack) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
      (PRE (LENGTH sb.bb_instructions))) ==>
      MEM (Var v) q.ps_stack \/ Var v IN FDOM q.ps_spilled) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions)) ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD) /\
    ((LAST sb.bb_instructions).inst_opcode = JMP ==>
      !targets. join_target_ops (liveness_analyze fn) fn succ
        (LAST sb.bb_instructions) = SOME targets ==>
        ALL_DISTINCT targets /\
        !x. MEM x targets ==> MEM x q.ps_stack \/ x IN FDOM q.ps_spilled) /\
    (!bops after. (LAST sb.bb_instructions).inst_opcode = JMP /\
      generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb psD =
        SOME (bops,after) ==>
      ?tops out.
        generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
          (LAST sb.bb_instructions)
          (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions))
          (bb_is_halting sb) F succ q = SOME (tops,out) /\
        generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
          (LAST sb.bb_instructions)
          (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions))
          (bb_is_halting sb) F succ (q with ps_stack := prefixL ++ q.ps_stack) =
          SOME (tops,out with ps_stack := prefixL ++ out.ps_stack) /\
        generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
          (LAST sb.bb_instructions)
          (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions))
          (bb_is_halting sb) F succ (q with ps_stack := prefixD ++ q.ps_stack) =
          SOME (tops,out with ps_stack := prefixD ++ out.ps_stack))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_dfs_join_physical_start_actual >> strip_tac >>
  `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>

  `fn_entry_label fn <> SOME succ` by simp[] >>
  drule_all fnPlanLineagePhiScheduleTheory.ready_nonentry_block_suffix >> strip_tac >>
  `LENGTH (collect_phis sb.bb_instructions) + PRE (LENGTH xs) =
    PRE (LENGTH sb.bb_instructions)` by suspend "cut_index" >>
  `!j. j < PRE (LENGTH xs) ==>
    (EL j xs).inst_opcode <> JMP /\ (EL j xs).inst_opcode <> PHI` by
    suspend "ordinary_layout" >>
  qpat_x_assum `p0 = _` (mk_asm "core") >>
  qpat_x_assum `!k. _ ==> ?ops q. _` (qspec_then `PRE (LENGTH xs)` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`prefixL`,`prefixD`,`suffix`,`phi_ops`,`al`,`p0`,`xs`,`qL`,`qD`,`ops`,`q`] >>
  conj_tac >- (asm "core" ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_asm1_tac >- suspend "terminal_targets" >> suspend "terminal_replay"
QED

Resume lineage_dfs_join_preterminal_core_actual[cut_index]:
  qpat_x_assum `sb.bb_instructions = _ ++ _`
    (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
  gvs[listTheory.DROP_APPEND] >> Cases_on `rest` >> gvs[]
QED

Resume lineage_dfs_join_preterminal_core_actual[ordinary_layout]:
  `!i. LENGTH (collect_phis sb.bb_instructions) <= i /\
    i < LENGTH sb.bb_instructions ==>
    (EL i sb.bb_instructions).inst_opcode <> PHI /\
    ((EL i sb.bb_instructions).inst_opcode = JMP ==>
      SUC i = LENGTH sb.bb_instructions)` by
    (qspecl_then [`fn`,`sb`,`LENGTH (collect_phis sb.bb_instructions)`] mp_tac
       fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
     (impl_tac >- simp[]) >> simp[]) >>
  gen_tac >> strip_tac >>
  `j < LENGTH xs` by decide_tac >>
  `LENGTH (collect_phis sb.bb_instructions) + j < PRE (LENGTH sb.bb_instructions)` by
    decide_tac >>
  `EL j xs = EL (LENGTH (collect_phis sb.bb_instructions) + j) sb.bb_instructions` by
    (simp[listTheory.EL_DROP, arithmeticTheory.ADD_COMM]) >>
  `LENGTH (collect_phis sb.bb_instructions) + j < LENGTH sb.bb_instructions` by decide_tac >>
  qpat_x_assum `!i. _ <= i /\ _ ==> _`
    (qspec_then `LENGTH (collect_phis sb.bb_instructions) + j` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> decide_tac
QED

Resume lineage_dfs_join_preterminal_core_actual[terminal_targets]:
  `fn_reachable fn sb.bb_label` by
    metis_tac[lineage_state_reachable, fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
  `sb.bb_instructions <> []` by
    (Cases_on `sb.bb_instructions` >> gvs[]) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) succ
    (PRE (LENGTH sb.bb_instructions))) ==>
    MEM (Var v) q.ps_stack \/ Var v IN FDOM q.ps_spilled` by simp[] >>
  strip_tac >> gen_tac >> disch_tac >>
  conj_tac >- metis_tac[fnPlanLineageNativeTerminalTheory.ready_join_target_ops_distinct] >>
  metis_tac[fnPlanLineageNativeTerminalTheory.native_terminal_jmp_target_available]
QED

Resume lineage_dfs_join_preterminal_core_actual[terminal_replay]:
  rpt gen_tac >> strip_tac >>
  `?tail_ops. generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
    succ (bb_is_halting sb) 0 (LENGTH sb.bb_instructions)
    (LENGTH (collect_phis sb.bb_instructions)) xs qD = SOME (tail_ops,after)` by
    suspend "dfs_worker" >>
  `generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
    succ (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
    (LENGTH sb.bb_instructions) 0 xs qD = SOME (tail_ops,after)` by
    (qpat_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = SOME (tail_ops,after)`
       (fn th => rewrite_tac[GSYM th]) >>
     irule fnPlanLineageEntryProductionTheory.generate_block_insts_plan_index_sum >> simp[]) >>
  `?before tops.
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
      (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
      (LENGTH sb.bb_instructions) xs qD (PRE (LENGTH xs)) before /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (LAST xs)
      (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions))
      (bb_is_halting sb) F succ before = SOME (tops,after)` by
    (irule fnPlanLineageEntryProductionTheory.native_worker_terminal_prefix >>
     qexistsl_tac [`0`,`tail_ops`,`qD`,`xs`] >>
     simp[fnPlanLineageEntryProductionTheory.native_inst_prefix_zero]) >>
  `before = q with ps_stack := prefixD ++ q.ps_stack` by
    (qpat_assum `native_inst_ops_prefix _ _ _ _ _ _ _ _ _ qD _ _ _`
       (mp_tac o MATCH_MP fnPlanLineageEntryProductionTheory.native_inst_ops_prefix_erase) >>
     qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ before` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[fnPlanLineageEntryProductionTheory.native_inst_prefix_deterministic]) >>
  `LAST xs = LAST sb.bb_instructions` by
    (qpat_assum `xs = _` (fn th => pure_rewrite_tac[th]) >>
     irule listTheory.last_drop >>
     qpat_x_assum `xs <> []` mp_tac >> simp[listTheory.DROP_EQ_NIL]) >>
  `sb.bb_instructions <> []` by (Cases_on `sb.bb_instructions` >> gvs[]) >>
  `inst_wf (LAST sb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM] >>
     metis_tac[rich_listTheory.LAST_MEM]) >>
  `?dest. (LAST sb.bb_instructions).inst_operands = [Label dest] /\
    (LAST sb.bb_instructions).inst_outputs = []` by gvs[venomWfTheory.inst_wf_def] >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ before = _` mp_tac >>
  qpat_assum `before = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `LAST xs = _` (fn th => pure_rewrite_tac[th]) >>
  strip_tac >>
  qpat_x_assum `(LAST sb.bb_instructions).inst_opcode = JMP ==> _` mp_tac >>
  simp[] >> strip_tac >>
  drule_all fnPlanLineageWideTheory.terminal_jmp_inst_bottom_reflection >>
  strip_tac >> qexists_tac `out` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule fnPlanLineageWideTheory.terminal_jmp_inst_bottom_frame >>
  simp[] >> metis_tac[]
QED

Resume lineage_dfs_join_preterminal_core_actual[dfs_worker]:
  qpat_x_assum `!p q. _` (qspecl_then [`psD`,`qD`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Finalise lineage_dfs_join_preterminal_core_actual

Theorem lineage_dfs_join_block_outgoing_core_actual:
  !fn entry succ sb dfg ch growth spill_base lbl_ctr fn_ops ps_end psL psD bops afterD.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psD /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb psD =
    SOME (bops,afterD) ==>
  ?afterL prefixL prefixD out.
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb psL =
      SOME (bops,afterL) /\
    afterL = out with ps_stack := prefixL ++ out.ps_stack /\
    afterD = out with ps_stack := prefixD ++ out.ps_stack /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions)) ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)
Proof
  rpt gen_tac >> strip_tac >>
  `?prefixL prefixD phi_ops xs qL qD ops out.
    xs = DROP (LENGTH (collect_phis sb.bb_instructions)) sb.bb_instructions /\
    (!p r. (p = psL /\ r = qL) \/ (p = psD /\ r = qD) ==>
      phi_schedule_run
        (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i),
          bb_is_halting sb)) (collect_phis sb.bb_instructions)) p = (phi_ops,r)) /\
    native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
      (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
      (LENGTH sb.bb_instructions) xs qL (LENGTH xs) ops
      (out with ps_stack := prefixL ++ out.ps_stack) /\
    native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
      (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
      (LENGTH sb.bb_instructions) xs qD (LENGTH xs) ops
      (out with ps_stack := prefixD ++ out.ps_stack) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ (LENGTH sb.bb_instructions)) ==>
      ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)` by
    (Cases_on `(LAST sb.bb_instructions).inst_opcode = JMP`
     >- suspend "jmp_complete" >> suspend "ordinary_complete") >>
  `fn_entry_label fn <> SOME succ` by simp[] >>
  `!p r. (p = psL /\ r = qL) \/ (p = psD /\ r = qD) ==>
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb p =
      case generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
        succ (bb_is_halting sb) 0 (LENGTH sb.bb_instructions)
        (LENGTH (collect_phis sb.bb_instructions)) xs r of
      NONE => NONE
    | SOME (tail_ops,q) => if revert_block_spills sb (phi_ops ++ tail_ops)
        then NONE else SOME ([SOLabel succ] ++ phi_ops ++ tail_ops,q)` by
    suspend "block_equations" >>
  `!p q. native_inst_ops_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
      (bb_is_halting sb) (LENGTH (collect_phis sb.bb_instructions))
      (LENGTH sb.bb_instructions) xs p (LENGTH xs) ops q ==>
    generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      succ (bb_is_halting sb) 0 (LENGTH sb.bb_instructions)
      (LENGTH (collect_phis sb.bb_instructions)) xs p = SOME (ops,q)` by
    suspend "workers" >>
  suspend "finish"
QED

Resume lineage_dfs_join_block_outgoing_core_actual[block_equations]:
  rpt gen_tac >> strip_tac >>
  `phi_schedule_run
    (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i),
      bb_is_halting sb)) (collect_phis sb.bb_instructions)) p = (phi_ops,r)` by
    metis_tac[] >>
  drule_all fnPlanLineagePhiScheduleTheory.generate_join_block_plan_phi_schedule >>
  disch_then (qspec_then `dfg` strip_assume_tac) >>
  qpat_x_assum `sb.bb_instructions = _ ++ _`
    (mp_tac o Q.AP_TERM `DROP (LENGTH (collect_phis sb.bb_instructions))`) >>
  simp_tac (srw_ss()) [listTheory.DROP_APPEND] >> simp[]
QED

Resume lineage_dfs_join_block_outgoing_core_actual[workers]:
  rpt gen_tac >> strip_tac >>
  gvs[fnPlanLineageEntryProductionTheory.native_inst_ops_prefix_complete] >>
  qpat_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = SOME (ops,q)`
    (fn th => rewrite_tac[GSYM th]) >>
  irule fnPlanLineageEntryProductionTheory.generate_block_insts_plan_index_sum >> simp[]
QED

Resume lineage_dfs_join_block_outgoing_core_actual[jmp_complete]:
  drule_all lineage_dfs_join_preterminal_core_actual >> strip_tac >>
  qpat_x_assum `!bops after. _` (qspecl_then [`bops`,`afterD`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "jmp_extend"
QED

Resume lineage_dfs_join_block_outgoing_core_actual[ordinary_complete]:
  drule_all lineage_dfs_join_physical_start_actual >> strip_tac >>
  suspend "ordinary_layout"
QED

Resume lineage_dfs_join_block_outgoing_core_actual[finish]:
  qpat_x_assum `!p q. native_inst_ops_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ ==> _`
    (fn th =>
      (qpat_assum `native_inst_ops_prefix _ _ _ _ _ _ _ _ _ qL _ _ _` (mp_tac o MATCH_MP th) >>
       qpat_assum `native_inst_ops_prefix _ _ _ _ _ _ _ _ _ qD _ _ _` (mp_tac o MATCH_MP th))) >>
  ntac 2 strip_tac >>
  qpat_assum `!p r. _ ==> generate_block_plan _ _ _ _ _ _ = _`
    (qspecl_then [`psD`,`qD`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qpat_x_assum `!p r. _ ==> generate_block_plan _ _ _ _ _ _ = _`
    (qspecl_then [`psL`,`qL`] mp_tac) >>
  (impl_tac >- simp[]) >> simp[] >>
  Cases_on `revert_block_spills sb (phi_ops ++ ops)` >> gvs[] >>
  strip_tac >> qexistsl_tac [`prefixL`,`prefixD`,`out`] >> simp[]
QED

Resume lineage_dfs_join_block_outgoing_core_actual[jmp_extend]:
  `LAST xs = LAST sb.bb_instructions` by
    (qpat_assum `xs = _` (fn th => pure_rewrite_tac[th]) >>
     irule listTheory.last_drop >>
     qpat_x_assum `xs <> []` mp_tac >> simp[listTheory.DROP_EQ_NIL]) >>
  `DROP (PRE (LENGTH xs)) xs = [LAST sb.bb_instructions]` by
    (qspecl_then [`xs`,`LENGTH xs`] mp_tac rich_listTheory.DROP_PREn_LAST_CONS >>
     simp[arithmeticTheory.PRE_SUB1] >> gvs[]) >>
  `SUC (PRE (LENGTH xs)) = LENGTH xs` by (Cases_on `xs` >> gvs[]) >>
  qexistsl_tac [`prefixL`,`prefixD`,`phi_ops`,`xs`,`qL`,`qD`,`ops ++ tops`,`out`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `p0 = _` kall_tac >>
  qpat_x_assum `qL = _` kall_tac >> qpat_x_assum `qD = _` kall_tac >>
  pure_rewrite_tac[CONJ_ASSOC] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >>
  qpat_assum `SUC (PRE (LENGTH xs)) = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  rewrite_tac[fnPlanLineageEntryProductionTheory.native_inst_ops_prefix_suc] >>
  qmatch_goalsub_rename_tac `out with ps_stack := pref ++ out.ps_stack` >>
  qexistsl_tac [`ops`,`q with ps_stack := pref ++ q.ps_stack`,
    `LAST sb.bb_instructions`,`[]`,`tops`] >> simp[]
QED

Resume lineage_dfs_join_block_outgoing_core_actual[ordinary_layout]:
  `fn_entry_label fn <> SOME succ` by simp[] >>
  `non_param_insts sb = sb.bb_instructions` by
    (drule_all fnPlanLineagePhiScheduleTheory.ready_nonentry_block_suffix >> simp[]) >>
  `MEM sb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `!i. LENGTH (collect_phis sb.bb_instructions) <= i /\
    i < LENGTH sb.bb_instructions ==>
    (EL i sb.bb_instructions).inst_opcode <> PHI /\
    ((EL i sb.bb_instructions).inst_opcode = JMP ==>
      SUC i = LENGTH sb.bb_instructions)` by
    (qspecl_then [`fn`,`sb`,`LENGTH (collect_phis sb.bb_instructions)`] mp_tac
       fnPlanLineageEntryProductionTheory.ready_block_ordinary_suffix_layout >>
     (impl_tac >- simp[]) >> simp[]) >>
  `!j. j < LENGTH xs ==>
    (EL j xs).inst_opcode <> JMP /\ (EL j xs).inst_opcode <> PHI` by
    suspend "nonjmp_layout" >>
  qpat_x_assum `!k. _ ==> ?ops q. _` (qspec_then `LENGTH xs` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`prefixL`,`prefixD`,`phi_ops`,`xs`,`qL`,`qD`,`ops`,`q`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  pure_rewrite_tac[CONJ_ASSOC] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume lineage_dfs_join_block_outgoing_core_actual[nonjmp_layout]:
  gen_tac >> strip_tac >>
  `LENGTH (collect_phis sb.bb_instructions) + j < LENGTH sb.bb_instructions` by
    (qpat_assum `xs = _` (fn th => fs[th]) >> decide_tac) >>
  `EL j xs = EL (LENGTH (collect_phis sb.bb_instructions) + j) sb.bb_instructions` by
    simp[listTheory.EL_DROP, arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `!i. _ <= i /\ _ ==> _`
    (qspec_then `LENGTH (collect_phis sb.bb_instructions) + j` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  reverse conj_tac >- gvs[] >>
  strip_tac >>
  `SUC (LENGTH (collect_phis sb.bb_instructions) + j) = LENGTH sb.bb_instructions` by
    metis_tac[] >>
  `EL (LENGTH (collect_phis sb.bb_instructions) + j) sb.bb_instructions =
    LAST sb.bb_instructions` by
    (`sb.bb_instructions <> []` by (Cases_on `sb.bb_instructions` >> gvs[]) >>
     simp[listTheory.LAST_EL] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
  metis_tac[]
QED

Finalise lineage_dfs_join_block_outgoing_core_actual



Theorem lineage_dfs_join_block_replay_actual:
  !fn entry succ sb dfg ch growth spill_base lbl_ctr fn_ops ps_end psL psD bops afterD.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ succ <> entry /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psL /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) succ psD /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb psD =
    SOME (bops,afterD) ==>
  ?afterL.
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb psL =
      SOME (bops,afterL) /\
    afterL.ps_alloc = afterD.ps_alloc /\ afterL.ps_spilled = afterD.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_dfs_join_block_outgoing_core_actual >> strip_tac >>
  qexists_tac `afterL` >> simp[]
QED

Theorem lineage_singleton_setup_core_seed:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  cfg_preds_of (cfg_analyze fn) lbl = [pred] /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
  generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
    ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
  clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
    (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) =
      (setup_ops,start) /\
  start = p0 with <|ps_stack := prefix ++ p0.ps_stack; ps_cleanup_height := h0;
    ps_cleanup_growth := g0; ps_cleanup_promised := b0|> /\
  EVERY (\v. ~MEM (Var v) prefix) (live_vars_at (liveness_analyze fn) lbl 0) ==>
  (!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
    MEM (Var v) p0.ps_stack \/ Var v IN FDOM p0.ps_spilled) /\
  (!j. j < LENGTH bb.bb_instructions ==>
    EVERY (\v. ~MEM (Var v) prefix)
      (live_vars_at (liveness_analyze fn) lbl (SUC j) ++
       (EL j bb.bb_instructions).inst_outputs))
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,venomExecPropsTheory.lookup_block_label] >>
  `collect_phis bb.bb_instructions = []` by
    (fs[codegen_ready_fn_def,phis_at_joins_def,listTheory.EVERY_MEM] >>
     gvs[listTheory.NULL_EQ,listTheory.LENGTH,arithmeticTheory.LESS_EQ_REFL]) >>
  `native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) bb.bb_instructions start
    (LENGTH (collect_phis bb.bb_instructions)) start` by
    simp[fnPlanLineageEntryProductionTheory.native_inst_prefix_zero] >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
    MEM (Var v) start.ps_stack \/ Var v IN FDOM start.ps_spilled` by
    (`(if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
        clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb
          (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
       else ([],ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
       (setup_ops,start)` by simp[] >>
     drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)
       lineage_state_native_post_phi_available >> simp[] >> metis_tac[]) >>
  `!j v. j < LENGTH bb.bb_instructions /\ MEM v (EL j bb.bb_instructions).inst_outputs ==>
    ~MEM (Var v) prefix` by
    (rpt strip_tac >>
     `~MEM (Var v) start.ps_stack` by
       (irule (cj 1 lineage_state_ordinary_output_body_absent) >>
        rpt (first_assum $ irule_at Any) >> simp[] >> metis_tac[]) >>
     gvs[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `fn_reachable fn bb.bb_label` by
    metis_tac[lineage_state_reachable,fn_reachable_cfg_analyze,codegen_ready_fn_def] >>
  rpt strip_tac >> simp[listTheory.EVERY_APPEND] >> conj_tac
  >- (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
      `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label 0) \/
       ?k. 0 <= k /\ k < SUC j /\ MEM v (EL k bb.bb_instructions).inst_outputs` by
        (irule fnPlanLineageCallersTheory.interval_live_origin >> simp[] >> decide_tac) >>
      gvs[listTheory.EVERY_MEM] >>
      `k < LENGTH bb.bb_instructions` by decide_tac >> metis_tac[]) >>
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem lineage_singleton_core_terminal_targets:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  cfg_preds_of (cfg_analyze fn) lbl = [pred] /\
  lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn init lbl ps /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
    MEM (Var v) p0.ps_stack \/ Var v IN FDOM p0.ps_spilled) /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    halt 0 (LENGTH bb.bb_instructions) bb.bb_instructions p0 k mid /\
  DROP k bb.bb_instructions = [inst] /\ inst.inst_opcode = JMP /\
  join_target_ops (liveness_analyze fn) fn lbl inst = SOME targets ==>
  ALL_DISTINCT targets /\
  (!x. MEM x targets ==> MEM x mid.ps_stack \/ x IN FDOM mid.ps_spilled)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,venomExecPropsTheory.lookup_block_label] >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    metis_tac[fnPlanLineagePhiScheduleTheory.ready_nonentry_block_suffix,optionTheory.SOME_11] >>
  `collect_phis bb.bb_instructions = []` by
    (fs[codegen_ready_fn_def,phis_at_joins_def,listTheory.EVERY_MEM] >>
     gvs[listTheory.NULL_EQ,listTheory.LENGTH,arithmeticTheory.LESS_EQ_REFL]) >>
  `fn_reachable fn bb.bb_label` by
    metis_tac[lineage_state_reachable,fn_reachable_cfg_analyze,codegen_ready_fn_def] >>
  metis_tac[fnPlanLineageNativeTerminalTheory.ordinary_core_terminal_targets]
QED
