(*
 * Generic Dataflow Analysis — Correctness (Statements Only)
 *
 * Re-exports from proofs/dfAnalyzeProofsScript.sml via ACCEPT_TAC.
 *)

Theory dfAnalyzeProps
Ancestors
  dfAnalyzeProofs

(* Convergence: analysis reaches a fixpoint under lattice preconditions.
   Preconditions are on the derived process function; users instantiate
   for their specific analysis via lattice properties. *)
Theorem df_analyze_fixpoint:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  ACCEPT_TAC df_analyze_fixpoint_proof
QED

(* Within a block, transfer relates adjacent instruction points at fixpoint.
   Covers all pairs including the exit value at index LENGTH:
   Forward:  df_at(lbl, idx+1) = transfer(inst_idx, df_at(lbl, idx))
   Backward: df_at(lbl, idx)   = transfer(inst_idx, df_at(lbl, idx+1)) *)
Theorem df_at_intra_transfer:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn lbl (bb : basic_block) idx.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      is_fixpoint process all_lbls result /\
      lookup_block lbl bbs = SOME bb /\
      SUC idx ≤ LENGTH bb.bb_instructions
    ==>
      (dir = Forward ==>
        df_at bottom result lbl (SUC idx) =
          transfer ctx (EL idx bb.bb_instructions)
                       (df_at bottom result lbl idx)) /\
      (dir = Backward ==>
        df_at bottom result lbl idx =
          transfer ctx (EL idx bb.bb_instructions)
                       (df_at bottom result lbl (SUC idx)))
Proof
  ACCEPT_TAC df_at_intra_transfer_proof
QED

(* Inter-block transfer: at fixpoint, the fold input to a block equals the
   join of edge-transferred neighbor boundaries.
   Forward: df_at(lbl, 0) = join of edge_transfer(pred, lbl, boundary(pred))
   Backward: df_at(lbl, n) = join of edge_transfer(succ, lbl, boundary(succ)) *)
Theorem df_at_inter_transfer:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn lbl (bb : basic_block).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
    let neighbors =
      (case dir of
         Forward => cfg_preds_of cfg lbl
       | Backward => cfg_succs_of cfg lbl) in
    let edge_vals = MAP (λnbr.
          edge_transfer ctx nbr lbl
            (df_boundary bottom result nbr)) neighbors in
    let joined =
      (case edge_vals of
         [] => (case entry_val of
                  NONE => bottom
                | SOME (ev_lbl, v) =>
                    if lbl = ev_lbl then v else bottom)
       | _ => FOLDL join bottom edge_vals) in
      is_fixpoint process all_lbls result /\
      lookup_block lbl bbs = SOME bb
    ==>
      (dir = Forward ==>
        df_at bottom result lbl 0 = joined) /\
      (dir = Backward ==>
        df_at bottom result lbl (LENGTH bb.bb_instructions) = joined)
Proof
  ACCEPT_TAC df_at_inter_transfer_proof
QED

(* Lattice invariant: closed-under-operations properties propagate
   from bottom through all analysis values. *)
Theorem df_analyze_invariant:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool).
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a /\ P b ==> P (join a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a))
    ==>
      (!lbl idx. P (df_at bottom result lbl idx)) /\
      (!lbl. P (df_boundary bottom result lbl))
Proof
  ACCEPT_TAC df_analyze_invariant_proof
QED

(* Lattice-to-process lifting: join-upper-bound implies df_process_block
   is inflationary w.r.t. the pointwise boundary ordering.
   Processing block lbl sets boundary(lbl) := join old final_val, which
   is ≥ old by the upper-bound property. Other boundaries are unchanged.
   Inst values are overwritten — only boundaries drive convergence. *)
Theorem df_process_inflationary:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val cfg bbs (elem_leq : 'a -> 'a -> bool).
    reflexive elem_leq /\
    (!a b. elem_leq a (join a b))
  ==>
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let leq = (λst1 st2.
      (!lbl. elem_leq (df_boundary bottom st1 lbl)
                       (df_boundary bottom st2 lbl))) in
    !lbl st. leq st (process lbl st)
Proof
  ACCEPT_TAC df_process_inflationary_proof
QED

(* CFG preds/succs inverse → worklist deps complete for df_process_block. *)
Theorem df_process_deps_complete:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val cfg bbs.
    (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b))
  ==>
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    wl_deps_complete process deps
Proof
  ACCEPT_TAC df_process_deps_complete_proof
QED
