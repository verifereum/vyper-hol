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
    let changed lbl old new =
          (df_widen_boundary bottom new lbl <>
           df_widen_boundary bottom old lbl \/
           df_widen_entry bottom new lbl <>
           df_widen_entry bottom old lbl) in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_widen_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = cfg.cfg_dfs_pre in
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete changed process deps
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
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      wf_function fn /\
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
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
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      wf_function fn /\
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
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

(* Lattice invariant: closed-under-ops (including widen) propagates.
   Requires convergence so WHILE result is well-defined. *)
Theorem df_analyze_widen_invariant:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn (P : 'a -> bool)
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (Q : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let st0 = init_df_widen_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      (* element-level closure *)
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a /\ P b ==> P (join a b)) /\
      (!a b. P a /\ P b ==> P (widen a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
      (* convergence *)
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!lbl idx. P (df_widen_at bottom result lbl idx)) /\
      (!lbl. P (df_widen_boundary bottom result lbl)) /\
      (!lbl. P (df_widen_entry bottom result lbl))
Proof
  ACCEPT_TAC df_analyze_widen_invariant_proof
QED

(* Join-upper-bound → process is inflationary w.r.t. pointwise
   boundary ordering. Same argument as base variant: boundary(lbl) :=
   join old final_val ≥ old. Widening affects entry, not boundary. *)
Theorem df_process_widen_inflationary:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val cfg bbs
   (elem_leq : 'a -> 'a -> bool).
    reflexive elem_leq /\
    (!a b. elem_leq a (join a b))
  ==>
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let leq = (λst1 st2.
      (!lbl. elem_leq (df_widen_boundary bottom st1 lbl)
                       (df_widen_boundary bottom st2 lbl))) in
    !lbl st. leq st (process lbl st)
Proof
  ACCEPT_TAC df_process_widen_inflationary_proof
QED

(* Visit-count-based convergence: no leq/bounded_measure needed.
   Instead, the user provides P and K such that after K visits to any label
   under P, processing that label is the identity.
   Plus: deps closure (successors of dfs_pre stay in dfs_pre). *)
Theorem df_analyze_widen_fixpoint_by_visits:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (K : num) (P : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let all_lbls = cfg.cfg_dfs_pre in
      (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b)) /\
      (!a b. join (join a b) b = join a b) /\
      (!a b. widen (widen a b) b = widen a b) /\
      (!a. widen a a = a) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of
         NONE => P (init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs))
       | SOME (lbl, v) =>
           P ((init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs)) with
              dws_boundary :=
                (init_df_widen_state bottom
                  (MAP (\bb. bb.bb_label) bbs)).dws_boundary |+ (lbl, v))) /\
      (!lbl st. P st /\ df_widen_visits st lbl >= K ==>
                process lbl st = st) /\
      (!lbl. MEM lbl all_lbls ==>
             EVERY (\s. MEM s all_lbls) (deps lbl))
    ==>
      is_fixpoint process all_lbls
        (df_analyze_widen dir bottom join widen threshold
           transfer edge_transfer ctx entry_val fn)
Proof
  ACCEPT_TAC dfAnalyzeWidenProofsTheory.df_analyze_widen_fixpoint_by_visits
QED

(* Variant: takes wl_deps_complete directly — no widen idempotence needed *)
Theorem df_analyze_widen_fixpoint_by_visits_no_idem:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (K : num) (P : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let chg lbl old new =
          (df_widen_boundary bottom new lbl <>
           df_widen_boundary bottom old lbl \/
           df_widen_entry bottom new lbl <>
           df_widen_entry bottom old lbl) in
    let all_lbls = cfg.cfg_dfs_pre in
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of
         NONE => P (init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs))
       | SOME (lbl, v) =>
           P ((init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs)) with
              dws_boundary := (init_df_widen_state bottom
                (MAP (\bb. bb.bb_label) bbs)).dws_boundary |+ (lbl, v))) /\
      (!lbl st. P st /\ df_widen_visits st lbl >= K ==>
                process lbl st = st) /\
      (!lbl. MEM lbl all_lbls ==>
             EVERY (\s. MEM s all_lbls) (deps lbl)) /\
      wl_deps_complete chg process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze_widen dir bottom join widen threshold
           transfer edge_transfer ctx entry_val fn)
Proof
  ACCEPT_TAC dfAnalyzeWidenProofsTheory.df_analyze_widen_fixpoint_by_visits_no_idem
QED

(* CFG preds/succs inverse → deps complete for widening process.
   Join absorption needed for self-stability (same as base variant). *)
Theorem df_process_widen_deps_complete:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val cfg bbs.
    (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b)) /\
    (!a b. join (join a b) b = join a b) /\
    (!a b. widen (widen a b) b = widen a b) /\
    (!a. widen a a = a)
  ==>
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let changed lbl old new =
          (df_widen_boundary bottom new lbl <>
           df_widen_boundary bottom old lbl \/
           df_widen_entry bottom new lbl <>
           df_widen_entry bottom old lbl) in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    wl_deps_complete changed process deps
Proof
  ACCEPT_TAC df_process_widen_deps_complete_proof
QED
Theorem df_widen_entry_sound:
  !(dir : direction) (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> 'b -> bool)
   (leq : 'a df_widen_state -> 'a df_widen_state -> bool)
   m b (Q : 'a df_widen_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen dir bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let st0 = init_df_widen_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      (!a b s. sound a s ==> sound (join a b) s) /\
      (!a b s. sound a s ==> sound (widen a b) s) /\
      (!s. sound bottom s) /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => !s. sound v s) /\
      (* convergence *)
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with dws_boundary := st0.dws_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!lbl s. sound (df_widen_entry bottom result lbl) s)
Proof
  ACCEPT_TAC dfAnalyzeWidenProofsTheory.df_widen_entry_sound_proof
QED
