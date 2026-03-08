(*
 * Generic Dataflow Analysis — Proofs
 *
 * TOP-LEVEL:
 *   df_analyze_fixpoint_proof       — worklist converges to fixpoint
 *   df_at_intra_transfer_proof      — within a block, transfer relates adjacent points
 *   df_at_inter_transfer_proof      — inter-block: fold input = join of neighbors
 *   df_boundary_eq_exit_proof       — at fixpoint, boundary = exit value
 *   df_analyze_invariant_proof      — lattice invariant preserved through analysis
 *   df_process_inflationary_proof   — lattice monotonicity → process inflationary
 *   df_process_deps_complete_proof  — CFG correctness → worklist deps complete
 *)

Theory dfAnalyzeProofs
Ancestors
  dfAnalyzeDefs worklistDefs cfgDefs

(* At convergence, processing any block is a no-op.
   Preconditions are on the derived process function (df_process_block).
   Users derive these from lattice-level properties for their specific analysis. *)
Theorem df_analyze_fixpoint_proof:
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
  cheat
QED

(* Within a block, the transfer function relates adjacent instruction points.
   True at fixpoint: the fold that produced the inst_map entries applied
   transfer sequentially, so adjacent entries differ by exactly one transfer.
   Covers all pairs including the exit value at index LENGTH:
   For Forward:  df_at(lbl, idx+1) = transfer(inst_idx, df_at(lbl, idx))
   For Backward: df_at(lbl, idx)   = transfer(inst_idx, df_at(lbl, idx+1)) *)
Theorem df_at_intra_transfer_proof:
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
  cheat
QED

(* Inter-block transfer: at fixpoint, the fold input to a block equals the
   join of edge-transferred neighbor boundaries.
   Forward: df_at(lbl, 0) = FOLDL join bottom [edge_transfer(pred, lbl, boundary(pred))]
   Backward: df_at(lbl, n) = FOLDL join bottom [edge_transfer(succ, lbl, boundary(succ))]
   When a block has no neighbors, entry_val is used (or bottom if NONE). *)
Theorem df_at_inter_transfer_proof:
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
  cheat
QED

(* At fixpoint, boundary equals the exit value (forward) or entry value
   (backward). Follows from: at fixpoint, fold input is stable, so
   final_val is deterministic, and boundary = join(boundary, final_val) =
   boundary only when boundary = final_val (since the sequence is monotone
   and converged).
   Requires: join is idempotent (join a a = a). *)
Theorem df_boundary_eq_exit_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn lbl (bb : basic_block).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      is_fixpoint process all_lbls result /\
      lookup_block lbl bbs = SOME bb /\
      (!a. join a a = a)
    ==>
      (dir = Forward ==>
        df_boundary bottom result lbl =
          df_at bottom result lbl (LENGTH bb.bb_instructions)) /\
      (dir = Backward ==>
        df_boundary bottom result lbl =
          df_at bottom result lbl 0)
Proof
  cheat
QED

(* Lattice invariant: if P holds for bottom, is closed under join/transfer/
   edge_transfer, then P holds for all values in the analysis result. *)
Theorem df_analyze_invariant_proof:
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
  cheat
QED

(* Lattice-to-process lifting: if join/transfer/edge_transfer are monotone
   w.r.t. an element-level ordering, then df_process_block is inflationary
   w.r.t. the induced df_state ordering.
   elem_leq: ordering on lattice elements (e.g., set inclusion).
   Preconditions: join is an upper bound, transfer and edge_transfer monotone. *)
Theorem df_process_inflationary_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val cfg bbs (elem_leq : 'a -> 'a -> bool).
    reflexive elem_leq /\
    transitive elem_leq /\
    (!a b. elem_leq a (join a b)) /\
    (!a b c. elem_leq b c ==> elem_leq (join a b) (join a c)) /\
    (!inst a b. elem_leq a b ==>
       elem_leq (transfer ctx inst a) (transfer ctx inst b)) /\
    (!src dst a b. elem_leq a b ==>
       elem_leq (edge_transfer ctx src dst a)
                (edge_transfer ctx src dst b))
  ==>
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let leq = (λst1 st2.
      (!lbl. elem_leq (df_boundary bottom st1 lbl)
                       (df_boundary bottom st2 lbl)) /\
      (!lbl idx. elem_leq (df_at bottom st1 lbl idx)
                           (df_at bottom st2 lbl idx))) in
    !lbl st. leq st (process lbl st)
Proof
  cheat
QED

(* CFG correctness → worklist deps complete.
   For forward: deps = succs. When processing A changes its boundary,
   successors of A (which read A's boundary) need reprocessing.
   For backward: deps = preds, symmetric argument.
   Requires CFG succs/preds are inverses. *)
Theorem df_process_deps_complete_proof:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val cfg bbs.
    (* CFG preds/succs are inverses *)
    (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b))
  ==>
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    wl_deps_complete process deps
Proof
  cheat
QED
