(*
 * Generic Dataflow Analysis with Widening — Proofs
 *
 * Convergence and correctness theorems for widening-based iteration.
 * Mirror of dfAnalyzeProofs for the df_analyze_widen variant.
 *
 * TOP-LEVEL:
 *   df_analyze_widen_fixpoint_proof       — worklist converges to fixpoint
 *   df_widen_at_intra_transfer_proof      — within-block transfer
 *   df_widen_at_inter_transfer_proof      — inter-block: fold input = widened join
 *   df_analyze_widen_invariant_proof      — lattice invariant propagation
 *   df_process_widen_inflationary_proof   — monotone ops → inflationary
 *   df_process_widen_deps_complete_proof  — CFG inverse → deps complete
 *)

Theory dfAnalyzeWidenProofs
Ancestors
  dfAnalyzeWidenDefs worklistDefs cfgDefs

(* Convergence: widening ensures the worklist empties.
   The widening operator must guarantee that the sequence of entry values
   for each block stabilizes after finitely many steps.
   widen_bounded: widening produces a value that is an upper bound AND
   the ascending chain from repeated widening has bounded length. *)
Theorem df_analyze_widen_fixpoint_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (P : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_widen_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze_widen dir bottom join widen threshold
           transfer edge_transfer ctx entry_val fn)
Proof
  cheat
QED

(* Within a block, transfer relates adjacent instruction points.
   Same structure as df_at_intra_transfer but for df_widen_state. *)
Theorem df_widen_at_intra_transfer_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn lbl (bb : basic_block) idx.
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      is_fixpoint process all_lbls result /\
      lookup_block lbl bbs = SOME bb /\
      SUC idx ≤ LENGTH bb.bb_instructions
    ==>
      (dir = Forward ==>
        df_widen_at bottom result lbl (SUC idx) =
          transfer ctx (EL idx bb.bb_instructions)
                       (df_widen_at bottom result lbl idx)) /\
      (dir = Backward ==>
        df_widen_at bottom result lbl idx =
          transfer ctx (EL idx bb.bb_instructions)
                       (df_widen_at bottom result lbl (SUC idx)))
Proof
  cheat
QED

(* Inter-block transfer for widening variant.
   The fold input equals the (possibly widened) join of neighbor boundaries.
   Unlike the base case, widening may have been applied if visits >= threshold. *)
Theorem df_widen_at_inter_transfer_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn lbl (bb : basic_block).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let all_lbls = MAP (λbb. bb.bb_label) bbs in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      is_fixpoint process all_lbls result /\
      lookup_block lbl bbs = SOME bb
    ==>
      (dir = Forward ==>
        df_widen_at bottom result lbl 0 =
          df_widen_entry bottom result lbl) /\
      (dir = Backward ==>
        df_widen_at bottom result lbl (LENGTH bb.bb_instructions) =
          df_widen_entry bottom result lbl)
Proof
  cheat
QED

(* Lattice invariant for widening: if P is closed under all operations
   including widen, then P holds everywhere in the result. *)
Theorem df_analyze_widen_invariant_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn (P : 'a -> bool).
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a /\ P b ==> P (join a b)) /\
      (!a b. P a /\ P b ==> P (widen a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a))
    ==>
      (!lbl idx. P (df_widen_at bottom result lbl idx)) /\
      (!lbl. P (df_widen_boundary bottom result lbl)) /\
      (!lbl. P (df_widen_entry bottom result lbl))
Proof
  cheat
QED

(* Monotone lattice ops → df_process_block_widen is inflationary
   w.r.t. the pointwise boundary ordering.
   Requires widen to also be inflationary: widen old new ≥ new.
   Boundary uses inflationary join (join old final_val), so convergence
   follows from the same argument as the base variant. *)
Theorem df_process_widen_inflationary_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val cfg bbs
   (elem_leq : 'a -> 'a -> bool).
    reflexive elem_leq /\
    transitive elem_leq /\
    (!a b. elem_leq a (join a b)) /\
    (!a b c. elem_leq b c ==> elem_leq (join a b) (join a c)) /\
    (!a b. elem_leq b (widen a b)) /\
    (!inst a b. elem_leq a b ==>
       elem_leq (transfer ctx inst a) (transfer ctx inst b)) /\
    (!src dst a b. elem_leq a b ==>
       elem_leq (edge_transfer ctx src dst a)
                (edge_transfer ctx src dst b))
  ==>
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let leq = (λst1 st2.
      (!lbl. elem_leq (df_widen_boundary bottom st1 lbl)
                       (df_widen_boundary bottom st2 lbl))) in
    !lbl st. leq st (process lbl st)
Proof
  cheat
QED

(* CFG preds/succs inverse → deps complete for widening process. *)
Theorem df_process_widen_deps_complete_proof:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val cfg bbs.
    (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b))
  ==>
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    wl_deps_complete process deps
Proof
  cheat
QED
