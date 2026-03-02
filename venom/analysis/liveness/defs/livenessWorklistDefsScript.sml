(*
 * Liveness Analysis — Worklist Definitions
 *
 * Worklist-based liveness matching Python's deque loop.
 * Replaces the round-robin liveness_iterate with per-block processing
 * via wl_iterate from the dataflow framework.
 *
 * TOP-LEVEL:
 *   liveness_process_block  — process single block for worklist
 *   liveness_wl_analyze     — worklist-based liveness analysis
 *   liveness_deps           — predecessors (backward analysis)
 *)

Theory livenessWorklistDefs
Ancestors
  livenessDefs worklistDefs cfgDefs

(* Process a single block for the worklist iteration.
   Computes out_vars from successors, merges with existing,
   recomputes inst_liveness. Returns updated state.
   Matches Python's _calculate_out_vars + _calculate_liveness. *)
Definition liveness_process_block_def:
  liveness_process_block cfg bbs lbl lr =
    case lookup_block lbl bbs of
    | NONE => lr
    | SOME bb => process_block cfg bbs lr bb
End

(* Deps for backward analysis: predecessors.
   When block A's data changes, predecessors of A need reprocessing
   (they compute out_vars from successors including A). *)
Definition liveness_deps_def:
  liveness_deps cfg lbl = cfg_preds_of cfg lbl
End

(* Worklist-based liveness analysis.
   Initial worklist = DFS post-order (all blocks).
   Uses wl_iterate from the dataflow framework. *)
Definition liveness_wl_analyze_def:
  liveness_wl_analyze fn =
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let lr0 = init_liveness bbs in
    let wl0 = cfg.cfg_dfs_post in
    let deps = liveness_deps cfg in
    SND (wl_iterate (liveness_process_block cfg bbs) deps wl0 lr0)
End
