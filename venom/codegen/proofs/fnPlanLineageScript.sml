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
 *   lineage_state_block_plan    — ADMITTED successor transfer: a lineage
 *                                 state regenerates the block's DFS code
 * Helper:
 *   lineage_state_dfs_fields    — a lineage state is a DFS state with its
 *                                 stack and spill map replaced
 *)

Theory fnPlanLineage
Ancestors
  stackPlanGen stackPlanTypes

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
   chosen freely. *)
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
  dfs_block_state liveness dfg cfg fn ps0 succ ps_succ ==>
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

(* ===== Successor transfer ===== *)

(* KEY LEMMA (ADMITTED, for alan): a lineage state regenerates the block's
   DFS code, so the code at the block's label is the plan of a state that
   carries the run-time path's stack and spill map.  With the cleanup
   fields taken from the DFS state the code can differ: entered from a
   predecessor whose path elided a cleanup, the stack carries more
   dead_stack_marker entries than on the DFS path, and a later
   clean_stack_plan whose DFS state has no promise may fail its height
   test only on the run-time path; hence the existential h, promised.

   Why it should hold: lineage and DFS states share alloc, label counter
   and the planner inputs; at a join (cfg_is_normalized: each predecessor
   ends in a JMP whose reorder produces the target stack, with no spills
   left) the stacks agree except for a bottom prefix of dead_stack_marker
   entries, which stack_get_depth (Var _), stack_get_phi_depth,
   stack_get_unfixed_depth and select_spill_candidate do not see; along
   other edges the induction carries that agreement. *)
Theorem lineage_state_block_plan:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb
   ps ps_dfs block_ops ps_dfs_after.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
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
      ps_after.ps_alloc = ps_dfs_after.ps_alloc
Proof
  cheat
QED
