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
      wl_deps_complete process deps /\
      (!lbl. MEM lbl all_lbls ==> MEM lbl wl0)
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  ACCEPT_TAC df_analyze_fixpoint_proof
QED

(* Within a block, transfer relates adjacent instruction points at fixpoint.
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
      SUC idx < LENGTH bb.bb_instructions
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

(* Lattice invariant: closed-under-operations properties propagate
   from bottom through all analysis values. *)
Theorem df_analyze_invariant:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool).
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (!a b. P a /\ P b ==> P (join a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a))
    ==>
      (!lbl idx. P (df_at bottom result lbl idx)) /\
      (!lbl. P (df_boundary bottom result lbl))
Proof
  ACCEPT_TAC df_analyze_invariant_proof
QED

(* Lattice-to-process lifting: monotone lattice operations imply
   df_process_block is inflationary w.r.t. the pointwise ordering. *)
Theorem df_process_inflationary:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val cfg bbs (elem_leq : 'a -> 'a -> bool).
    partial_order elem_leq /\
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
