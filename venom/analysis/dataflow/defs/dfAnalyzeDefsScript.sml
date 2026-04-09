(*
 * Generic Dataflow Analysis — Definitions
 *
 * Parameterized dataflow framework: provide lattice + transfer + direction,
 * get per-instruction analysis results via worklist iteration.
 *
 * TOP-LEVEL:
 *   df_analyze         — run analysis on a function
 *   df_at              — query lattice value at instruction point
 *   df_boundary        — query boundary value (exit for forward, entry for backward)
 *   df_fold_block      — fold transfer across block instructions
 *   df_process_block   — process one block: meet predecessors, fold transfer
 *
 * Helper:
 *   direction          — Forward | Backward
 *   df_state           — per-instruction + per-block boundary lattice values
 *   init_df_state      — initialize all blocks to bottom
 *)

Theory dfAnalyzeDefs
Ancestors
  worklistDefs cfgDefs venomInst

(* ===== Direction ===== *)

Datatype:
  direction = Forward | Backward
End

(* ===== Analysis state ===== *)

(* Per-instruction lattice values + per-block boundary values.
   boundary: block_label → lattice value at block exit (forward) or entry (backward).
     This is the fold output: the value produced by folding transfer through
     all instructions. Neighbors read this value for inter-block dataflow.
   inst: (block_label, inst_idx) → lattice value BEFORE that instruction.
     For both forward and backward, df_at(lbl, idx) = value just before
     executing instruction idx. df_at(lbl, n) where n = LENGTH instrs
     gives the exit value (after the last instruction). *)
Datatype:
  df_state = <|
    ds_inst : (string # num, 'a) fmap;
    ds_boundary : (string, 'a) fmap
  |>
End

(* ===== Query API ===== *)

(* Lattice value BEFORE instruction idx in block lbl.
   For idx = LENGTH instrs, returns the exit value (after last instruction).
   Returns bottom if not computed (block not yet processed). *)
Definition df_at_def:
  df_at (bottom : 'a) (st : 'a df_state) lbl idx =
    case FLOOKUP st.ds_inst (lbl, idx) of
      NONE => bottom
    | SOME v => v
End

(* Boundary value for a block: exit (forward) or entry (backward).
   Returns bottom if not computed. *)
Definition df_boundary_def:
  df_boundary (bottom : 'a) (st : 'a df_state) lbl =
    case FLOOKUP st.ds_boundary lbl of
      NONE => bottom
    | SOME v => v
End

(* ===== Fold transfer across instructions ===== *)

(* Fold transfer forward (index 0..n-1), storing each intermediate value.
   val_before_i is stored at index i; transfer produces val_before_(i+1).
   At the end, the exit value (after last instruction) is stored at index n.
   Returns (final_val, inst_map). *)
Definition df_fold_forward_def:
  df_fold_forward transfer lbl [] (idx : num) acc inst_map =
    (acc, inst_map |+ ((lbl, idx), acc)) ∧
  df_fold_forward transfer lbl (inst::rest) idx acc inst_map =
    let inst_map' = inst_map |+ ((lbl, idx), acc) in
    let acc' = transfer inst acc in
    df_fold_forward transfer lbl rest (idx + 1) acc' inst_map'
End

(* Fold transfer backward (index n-1..0), storing each intermediate value.
   val_after_i is input; transfer produces val_before_i stored at index i.
   At the end, the exit value (after last instruction) is stored at index n.
   Returns (final_val, inst_map). *)
Definition df_fold_backward_def:
  df_fold_backward transfer lbl [] (idx : num) acc inst_map =
    (acc, inst_map |+ ((lbl, idx), acc)) ∧
  df_fold_backward transfer lbl (inst::rest) idx acc inst_map =
    let (acc', inst_map') =
      df_fold_backward transfer lbl rest (idx + 1) acc inst_map in
    let val_before = transfer inst acc' in
    (val_before, inst_map' |+ ((lbl, idx), val_before))
End

(* Direction-dispatched fold *)
Definition df_fold_block_def:
  df_fold_block dir transfer lbl instrs init_val =
    case dir of
      Forward =>
        df_fold_forward transfer lbl instrs 0 init_val FEMPTY
    | Backward =>
        df_fold_backward transfer lbl instrs 0 init_val FEMPTY
End

(* ===== Per-block processing ===== *)

(* Process one block: gather neighbor boundaries, apply edge_transfer per
   neighbor, join, fold transfer through instructions, update state.
   - Forward: read predecessors' boundaries (their exits), fold 0→n,
     store fold output as this block's boundary (exit value)
   - Backward: read successors' boundaries (their entries), fold n→0,
     store fold output as this block's boundary (entry value)
   entry_val: when block has no predecessors (forward) or no successors
   (backward), use this value instead of bottom. For forward analyses,
   the entry block has no predecessors and needs a different initial value
   (e.g. [] for var_def, {entry} for dominators). *)
(* Compute the joined input value for a block from its neighbors'
   boundaries plus the entry_val at the entry block.
   Factored out so theorem statements can reference it by name. *)
Definition df_joined_val_def:
  df_joined_val dir bottom join edge_transfer ctx entry_val cfg
               (st : 'a df_state) lbl =
    let neighbors =
      (case dir of
         Forward => cfg_preds_of cfg lbl
       | Backward => cfg_succs_of cfg lbl) in
    let edge_vals = MAP (λnbr.
          edge_transfer ctx nbr lbl
            (df_boundary bottom st nbr)) neighbors in
    let base =
      (case edge_vals of [] => bottom | _ => FOLDL join bottom edge_vals) in
    case entry_val of
      NONE => base
    | SOME (ev_lbl, v) =>
        if lbl = ev_lbl then join v base else base
End

Definition df_process_block_def:
  df_process_block dir bottom join transfer edge_transfer
                   ctx entry_val cfg bbs lbl (st : 'a df_state) =
    let joined = df_joined_val dir bottom join edge_transfer ctx
                               entry_val cfg st lbl in
    let instrs =
      (case lookup_block lbl bbs of
         NONE => []
       | SOME bb => bb.bb_instructions) in
    let (final_val, inst_map) =
      df_fold_block dir (transfer ctx) lbl instrs joined in
    let old_boundary = df_boundary bottom st lbl in
    let new_boundary = join old_boundary final_val in
    if new_boundary = old_boundary then st
    else st with ds_boundary := st.ds_boundary |+ (lbl, new_boundary)
End

(* ===== Initialization ===== *)

Definition init_df_state_def:
  init_df_state (bottom : 'a) (lbls : string list) : 'a df_state =
    <| ds_inst := FEMPTY;
       ds_boundary :=
         FOLDL (λm lbl. m |+ (lbl, bottom)) FEMPTY lbls |>
End

(* ===== Inst population ===== *)

(* After boundary fixpoint, populate ds_inst by folding each block once.
   The fold uses the stable boundaries, producing deterministic inst_maps. *)
Definition df_populate_inst_def:
  df_populate_inst dir bottom join transfer edge_transfer
                   ctx entry_val cfg bbs lbls (st : 'a df_state) =
    FOLDL (λst' lbl.
      let joined = df_joined_val dir bottom join edge_transfer ctx
                                 entry_val cfg st lbl in
      let instrs =
        (case lookup_block lbl bbs of
           NONE => []
         | SOME bb => bb.bb_instructions) in
      let (final_val, inst_map) =
        df_fold_block dir (transfer ctx) lbl instrs joined in
      st' with ds_inst := FUNION inst_map st'.ds_inst
    ) st lbls
End

(* ===== Top-level analysis ===== *)

(* Generic dataflow analysis: initialize, worklist iterate to boundary
   fixpoint, then populate inst from stable boundaries.
   entry_val: optional (label, value) to override one block's initial boundary.
     Forward analyses use this for the entry block (e.g. dom[entry]={entry}).
     Backward analyses typically pass NONE (exit block's bottom is correct). *)
Definition df_analyze_def:
  df_analyze dir bottom join transfer edge_transfer ctx entry_val fn =
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let lbls = MAP (λbb. bb.bb_label) bbs in
    let st0 = init_df_state bottom lbls in
    let st0' =
      (case entry_val of
         NONE => st0
       | SOME (lbl, v) =>
           st0 with ds_boundary := st0.ds_boundary |+ (lbl, v)) in
    let process =
      df_process_block dir bottom join transfer edge_transfer
                       ctx entry_val cfg bbs in
    let changed =
      (λlbl old new. df_boundary bottom new lbl <> df_boundary bottom old lbl) in
    let deps =
      (case dir of
         Forward => cfg_succs_of cfg
       | Backward => cfg_preds_of cfg) in
    let wl0 =
      (case dir of
         Forward => cfg.cfg_dfs_pre
       | Backward => cfg.cfg_dfs_post) in
    let boundary_result = SND (wl_iterate changed process deps wl0 st0') in
    df_populate_inst dir bottom join transfer edge_transfer
                     ctx entry_val cfg bbs lbls boundary_result
End
