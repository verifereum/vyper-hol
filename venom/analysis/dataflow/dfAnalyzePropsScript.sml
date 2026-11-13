(*
 * Generic Dataflow Analysis — Correctness (Statements Only)
 *
 * Re-exports from proofs/dfAnalyzeProofsScript.sml via ACCEPT_TAC.
 *)

Theory dfAnalyzeProps
Ancestors
  dfAnalyzeProofs

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
      wf_function fn /\
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
      wf_function fn /\
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
      wf_function fn /\
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
    let changed = (\lbl (old:'a df_state) new.
                     df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    wl_deps_complete changed process deps
Proof
  ACCEPT_TAC df_process_deps_complete_proof
QED

(* cfg_dfs_pre labels are a subset of fn_labels for well-formed functions *)
Theorem cfg_dfs_pre_subset_fn_labels:
  !fn lbl. wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    MEM lbl (fn_labels fn)
Proof
  ACCEPT_TAC dfAnalyzeProofsTheory.cfg_dfs_pre_subset_fn_labels
QED

