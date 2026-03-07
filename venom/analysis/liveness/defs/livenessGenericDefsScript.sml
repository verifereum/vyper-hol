(*
 * Liveness Analysis — Generic Framework Instantiation
 *
 * Expresses liveness analysis as an instance of df_analyze (backward,
 * set union, live_update transfer). Eventually replaces liveness_analyze
 * and liveness_wl_analyze.
 *
 * TOP-LEVEL:
 *   liveness_transfer       — per-instruction transfer: (live \ defs) ∪ uses
 *   liveness_edge_transfer  — PHI-aware edge transfer: input_vars_from
 *   liveness_df_analyze     — liveness via generic df_analyze
 *
 * The lattice is (string list, ⊆, ∪) — sets-as-lists, subset ordering,
 * list_union join. Direction is Backward. Context is fn.fn_blocks
 * (needed by edge_transfer to look up PHI instructions).
 *)

Theory livenessGenericDefs
Ancestors
  dfAnalyzeDefs livenessDefs

(* Per-instruction transfer for backward liveness:
   live' = (live \ defs) ∪ uses.
   Context is unit — liveness transfer doesn't need extra info. *)
Definition liveness_transfer_def:
  liveness_transfer (bbs : basic_block list) (inst : instruction)
                    (live : string list) =
    let uses = inst_uses inst in
    let defs = inst_defs inst in
    if NULL uses ∧ NULL defs then live
    else live_update defs uses live
End

(* PHI-aware edge transfer for backward liveness.
   When flowing backward from successor to current block, include
   operand for current block's label, exclude others.
   Args: ctx=bbs, succ_lbl=successor, cur_lbl=current block, live=succ entry *)
Definition liveness_edge_transfer_def:
  liveness_edge_transfer (bbs : basic_block list) succ_lbl cur_lbl
                         (live : string list) =
    case lookup_block succ_lbl bbs of
      NONE => live
    | SOME succ_bb =>
        input_vars_from cur_lbl succ_bb.bb_instructions live
End

(* Liveness analysis via generic dataflow framework.
   Backward direction, empty-list bottom, list_union join. *)
Definition liveness_df_analyze_def:
  liveness_df_analyze fn =
    df_analyze Backward [] list_union liveness_transfer
              liveness_edge_transfer fn.fn_blocks fn
End
