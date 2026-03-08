(*
 * Generic Dataflow Analysis with Widening — Correctness (Statements Only)
 *
 * Re-exports from proofs/dfAnalyzeWidenProofsScript.sml via ACCEPT_TAC.
 *)

Theory dfAnalyzeWidenProps
Ancestors
  dfAnalyzeWidenProofs

(* Convergence: widening analysis reaches a fixpoint.
   Same structure as df_analyze_fixpoint but for the widening variant.
   The widening operator ensures bounded_measure holds even for
   infinite-height lattices. *)
Theorem df_analyze_widen_fixpoint:
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
  ACCEPT_TAC df_analyze_widen_fixpoint_proof
QED

(* Within a block, transfer relates adjacent instruction points. *)
Theorem df_widen_at_intra_transfer:
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
  ACCEPT_TAC df_widen_at_intra_transfer_proof
QED

(* Inter-block: at fixpoint, the fold input equals the cached entry value
   (which is the possibly-widened join of neighbor boundaries). *)
Theorem df_widen_at_inter_transfer:
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
  ACCEPT_TAC df_widen_at_inter_transfer_proof
QED

(* Lattice invariant: closed-under-ops (including widen) propagates. *)
Theorem df_analyze_widen_invariant:
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
  ACCEPT_TAC df_analyze_widen_invariant_proof
QED

(* Monotone ops + widen inflationary → process is inflationary. *)
Theorem df_process_widen_inflationary:
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
                       (df_widen_boundary bottom st2 lbl)) /\
      (!lbl idx. elem_leq (df_widen_at bottom st1 lbl idx)
                           (df_widen_at bottom st2 lbl idx))) in
    !lbl st. leq st (process lbl st)
Proof
  ACCEPT_TAC df_process_widen_inflationary_proof
QED

(* CFG preds/succs inverse → deps complete for widening process. *)
Theorem df_process_widen_deps_complete:
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
  ACCEPT_TAC df_process_widen_deps_complete_proof
QED
