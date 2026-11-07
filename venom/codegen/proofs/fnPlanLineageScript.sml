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
 *   dfs_edge_spilled            — CHEATED: pred's DFS code leaves succ's
 *                                 DFS spill map
 * Helper:
 *   lineage_state_dfs_fields    — a lineage state is a DFS state with its
 *                                 stack and spill map replaced
 *   lineage_entry_lineage_state — a lineage entry is a lineage state
 *)

Theory fnPlanLineage
Ancestors
  stackPlanGen stackPlanTypes fnPlanLineageJoinEntry

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

(* Helper: every field but the stack and the spill map is a DFS state's. *)
Theorem lineage_state_dfs_fields:
  !liveness dfg cfg fn ps0 lbl ps.
    lineage_state liveness dfg cfg fn ps0 lbl ps ==>
    ?ps_dfs.
      dfs_block_state liveness dfg cfg fn ps0 lbl ps_dfs /\
      ps = ps_dfs with <| ps_stack := ps.ps_stack;
                          ps_spilled := ps.ps_spilled |>
Proof
  rpt gen_tac >> qid_spec_tac `ps` >> qid_spec_tac `lbl` >>
  ho_match_mp_tac lineage_state_ind >> rpt strip_tac
  >- (qexists_tac `ps0` >>
      simp[dfs_block_state_def, plan_state_component_equality] >>
      qexistsl_tac [`[]`, `[]`] >> simp[dfs_aux_call_entry])
  >> qexists_tac `ps_succ` >> simp[]
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

(* CHEATED leaf: along a CFG edge, the spill map pred's DFS code leaves is
   succ's DFS spill map, which lineage_state_step requires.

   Why it should hold: at a join (more than one predecessor) both maps are
   FEMPTY, since every predecessor ends in a JMP whose plan restores every
   target (fnLineageInvSupport$analyzed_join_edge_block_spills_empty, for
   pin and for the owner's state that
   fnLineageInvOwnerOrigin$dfs_block_state_owner_alloc_origin gives).  With
   a single predecessor, the owner is pred itself; its DFS state is pin
   (dfs_block_state is functional: fnBlockPlanStaticDfsTrace proves it
   under plan success, and the ~sibling rule only admits calls that
   returned SOME), and generate_block_plan is a function, so the owner's
   output is pout.  The entry block has no predecessors. *)
Theorem dfs_edge_spilled:
  !liveness dfg cfg fn ps0 pred pb pin ops pout succ ps_succ.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    dfs_block_state liveness dfg cfg fn ps0 pred pin /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    generate_block_plan liveness dfg cfg fn pb pin = SOME (ops, pout) /\
    MEM succ (cfg_succs_of cfg pred) /\
    dfs_block_state liveness dfg cfg fn ps0 succ ps_succ ==>
    pout.ps_spilled = ps_succ.ps_spilled
Proof
  cheat
QED

(* ===== Successor transfer ===== *)

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
