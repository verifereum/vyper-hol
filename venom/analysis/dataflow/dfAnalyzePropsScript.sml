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
    let all_lbls = cfg.cfg_dfs_pre in
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
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
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
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
    let joined = df_joined_val dir bottom join edge_transfer ctx
                               entry_val cfg result lbl in
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb
    ==>
      (dir = Forward ==>
        df_at bottom result lbl 0 = joined) /\
      (dir = Backward ==>
        df_at bottom result lbl (LENGTH bb.bb_instructions) = joined)
Proof
  ACCEPT_TAC df_at_inter_transfer_proof
QED

(* Boundary fixpoint: at fixpoint, boundary = join(boundary, exit_val).
   Forward:  boundary(lbl) = join(boundary(lbl), df_at(lbl, LENGTH instrs))
   Backward: boundary(lbl) = join(boundary(lbl), df_at(lbl, 0))
   The block's output is already absorbed into the boundary. *)
Theorem df_boundary_fixpoint:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn lbl (bb : basic_block).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let all_lbls = cfg.cfg_dfs_pre in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      is_fixpoint process all_lbls result /\
      MEM lbl all_lbls /\
      lookup_block lbl bbs = SOME bb
    ==>
      (dir = Forward ==>
        df_boundary bottom result lbl =
          join (df_boundary bottom result lbl)
               (df_at bottom result lbl (LENGTH bb.bb_instructions))) /\
      (dir = Backward ==>
        df_boundary bottom result lbl =
          join (df_boundary bottom result lbl)
               (df_at bottom result lbl 0))
Proof
  ACCEPT_TAC df_boundary_fixpoint_proof
QED

(* Lattice invariant: closed-under-operations properties propagate
   from bottom through all analysis values.
   Requires convergence (bounded_measure) so WHILE terminates and
   result is well-defined. The state-level ordering leq witnesses
   termination — users typically have this from df_analyze_fixpoint. *)
Theorem df_analyze_invariant:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      (* element-level closure *)
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a /\ P b ==> P (join a b)) /\
      (!inst a. P a ==> P (transfer ctx inst a)) /\
      (!src dst a. P a ==> P (edge_transfer ctx src dst a)) /\
      (* convergence — needed because WHILE result is ARB if non-terminating *)
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
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

(* CFG preds/succs inverse → worklist deps complete for df_process_block.
   Join absorption (join (join a b) b = join a b) is needed for self-stability:
   processing a block twice must give the same result, otherwise the block
   would need to be in its own deps (which only happens with self-loops). *)
Theorem df_process_deps_complete:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val cfg bbs.
    (!a b. MEM b (cfg_succs_of cfg a) <=> MEM a (cfg_preds_of cfg b)) /\
    (!a b. join (join a b) b = join a b)
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

(* Process-level fixpoint: uses per-step termination condition.
   Easier to instantiate than df_analyze_fixpoint because the measure m
   only needs to increase when process actually changes the state. *)
Theorem df_analyze_fixpoint_process:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of Forward => cfg_succs_of cfg
                           | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let all_lbls = cfg.cfg_dfs_pre in
      (!lbl st. P st /\ process lbl st <> st ==> m st < m (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. P x ==> m x <= b) /\
      wl_deps_complete process deps
    ==>
      is_fixpoint process all_lbls
        (df_analyze dir bottom join transfer edge_transfer ctx entry_val fn)
Proof
  ACCEPT_TAC df_analyze_fixpoint_process
QED

(* Forward analysis fixpoint for well-formed functions.
   Handles valid_lbl restriction automatically — only requires measure/P
   for block labels (MEM lbl (fn_labels fn)), not for all labels. *)
Theorem df_analyze_fixpoint_forward:
  !(bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (m : 'a df_state -> num) b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Forward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
      wf_function fn /\
      (!lbl st. MEM lbl (fn_labels fn) /\ P st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. MEM lbl (fn_labels fn) /\ P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. P x ==> m x <= b) /\
      wl_deps_complete process (cfg_succs_of cfg)
    ==>
      is_fixpoint process cfg.cfg_dfs_pre
        (df_analyze Forward bottom join transfer edge_transfer ctx
                    entry_val fn)
Proof
  ACCEPT_TAC (dfAnalyzeProofsTheory.df_analyze_fixpoint_forward)
QED

(* Boundary invariant: P closed under join propagates to all boundaries.
   Uses bounded_measure for convergence. *)
Theorem df_analyze_boundary_invariant:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a ==> P (join a b)) /\
      (* convergence *)
      (!lbl st. Q st ==> leq st (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure Q leq m b
    ==>
      (!lbl. P (df_boundary bottom result lbl))
Proof
  ACCEPT_TAC (dfAnalyzeProofsTheory.df_analyze_boundary_invariant)
QED

(* Process-level boundary invariant: like df_analyze_boundary_invariant but
   uses process-level termination instead of bounded_measure. *)
Theorem df_analyze_boundary_invariant_process:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (m : 'a df_state -> num) b (Q : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a ==> P (join a b)) /\
      (* convergence — process-level *)
      (!lbl st. Q st /\ process lbl st <> st ==> m st < m (process lbl st)) /\
      (!lbl st. Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. Q x ==> m x <= b)
    ==>
      (!lbl. P (df_boundary bottom result lbl))
Proof
  ACCEPT_TAC (dfAnalyzeProofsTheory.df_analyze_boundary_invariant_process)
QED

(* Restricted boundary invariant: like df_analyze_boundary_invariant_process
   but Q only needs to be preserved for valid labels. *)
Theorem df_analyze_boundary_invariant_restricted:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn (P : 'a -> bool)
   (m : 'a df_state -> num) b (Q : 'a df_state -> bool)
   (valid_lbl : string -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let st0 = init_df_state bottom (MAP (λbb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      P bottom /\
      (case entry_val of NONE => T
       | SOME (lbl, v) => P v) /\
      (!a b. P a ==> P (join a b)) /\
      (!lbl st. valid_lbl lbl /\ Q st /\ process lbl st <> st ==>
                m st < m (process lbl st)) /\
      (!lbl st. valid_lbl lbl /\ Q st ==> Q (process lbl st)) /\
      (case entry_val of NONE => Q st0
       | SOME (lbl, v) =>
           Q (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      (!x. Q x ==> m x <= b) /\
      EVERY valid_lbl (case dir of
        Forward => cfg.cfg_dfs_pre | Backward => cfg.cfg_dfs_post) /\
      (!lbl. valid_lbl lbl ==>
        EVERY valid_lbl (case dir of
          Forward => cfg_succs_of cfg lbl
        | Backward => cfg_preds_of cfg lbl))
    ==>
      (!lbl. P (df_boundary bottom result lbl))
Proof
  ACCEPT_TAC (dfAnalyzeProofsTheory.df_analyze_boundary_invariant_restricted)
QED

(* df_fold_block keys: all instruction-map keys produced by df_fold_block
   have the given label as their first component *)
Theorem df_fold_block_keys:
  !dir transfer lbl instrs init_val final_val inst_map.
    df_fold_block dir transfer lbl instrs init_val = (final_val, inst_map) ==>
    !k. FLOOKUP inst_map k <> NONE ==> FST k = lbl
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.df_fold_block_keys
QED

(* df_fold_block forward invariant: if P is preserved by each transfer step,
   then P holds for the final value and all instruction-map values *)
Theorem df_fold_block_forward_invariant:
  !transfer lbl instrs init_val fv im P.
    df_fold_block Forward transfer lbl instrs init_val = (fv, im) /\
    P init_val /\
    (!inst v. MEM inst instrs /\ P v ==> P (transfer inst v)) ==>
    P fv /\ !k v. FLOOKUP im k = SOME v ==> P v
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.df_fold_block_forward_invariant
QED

(* cfg_dfs_pre membership implies cfg_dfs_post membership *)
Theorem cfg_dfs_pre_mem_post:
  !fn lbl.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    MEM lbl (cfg_analyze fn).cfg_dfs_post
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.cfg_dfs_pre_mem_post
QED

(* cfg_dfs_pre labels are a subset of fn_labels for well-formed functions *)
Theorem cfg_dfs_pre_subset_fn_labels:
  !fn lbl. wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    MEM lbl (fn_labels fn)
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.cfg_dfs_pre_subset_fn_labels
QED

(* Forward fold: FLOOKUP structure for each instruction index *)
Theorem df_fold_forward_at:
  !transfer lbl instrs idx acc fv im.
    df_fold_forward transfer lbl instrs idx acc FEMPTY = (fv, im) ==>
    FLOOKUP im (lbl, idx) = SOME acc /\
    (!i. i < LENGTH instrs ==>
      FLOOKUP im (lbl, idx + SUC i) =
        SOME (transfer (EL i instrs)
                       (THE (FLOOKUP im (lbl, idx + i))))) /\
    fv = THE (FLOOKUP im (lbl, idx + LENGTH instrs))
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.df_fold_forward_at
QED

(* FOLDL with FEMPTY yields only the initial value *)
Theorem foldl_fempty_val:
  !ls bot k v.
    FLOOKUP (FOLDL (\m l. m |+ (l, bot)) FEMPTY ls) k = SOME v ==> v = bot
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.foldl_fempty_val
QED

(* df_fold_block FDOM structure for forward direction *)
Theorem df_fold_block_fdom:
  !transfer lbl instrs init_val fv im.
    df_fold_block Forward transfer lbl instrs init_val = (fv, im) ==>
    FDOM im = IMAGE (\i. (lbl, i)) (count (LENGTH instrs + 1))
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.df_fold_block_fdom
QED

(* df_valid_inst_keys is always finite *)
Theorem df_valid_inst_keys_finite:
  !bbs. FINITE (df_valid_inst_keys bbs)
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.df_valid_inst_keys_finite
QED

(* df_valid_inst_keys cardinality bounded by df_total_inst_slots *)
Theorem df_valid_inst_keys_card:
  !bbs. CARD (df_valid_inst_keys bbs) <= df_total_inst_slots bbs
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.df_valid_inst_keys_card
QED
