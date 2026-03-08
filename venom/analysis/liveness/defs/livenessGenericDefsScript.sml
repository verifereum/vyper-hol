(*
 * Liveness Analysis — Generic Framework Instantiation
 *
 * Expresses liveness analysis as an instance of df_analyze (backward,
 * set union, live_update transfer). Eventually replaces liveness_analyze.
 *
 * TOP-LEVEL:
 *   liveness_transfer       — per-instruction transfer: (live \ defs) ∪ uses
 *   liveness_edge_transfer  — PHI-aware edge transfer: input_vars_from
 *   liveness_df_analyze     — liveness via generic df_analyze
 *   liveness_at             — live variables before instruction idx
 *   liveness_boundary       — boundary (entry) live variables for a block
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
   bbs parameter is the shared context type (needed by edge_transfer
   for PHI-aware operand lookup; unused by the transfer itself). *)
Definition liveness_transfer_def:
  liveness_transfer (bbs : basic_block list) (inst : instruction)
                    (live : string list) =
    live_update (inst_defs inst) (inst_uses inst) live
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
              liveness_edge_transfer fn.fn_blocks NONE fn
End

(* Live variables before instruction idx in block lbl.
   For idx = LENGTH instrs, returns live variables after the last instruction
   (the exit liveness = value flowing from successors). *)
Definition liveness_at_def:
  liveness_at fn lbl idx =
    df_at [] (liveness_df_analyze fn) lbl idx
End

(* Boundary (entry) live variables for block lbl.
   For backward analysis, this is the fold output = entry liveness. *)
Definition liveness_boundary_def:
  liveness_boundary fn lbl =
    df_boundary [] (liveness_df_analyze fn) lbl
End
