(*
 * Generic Dataflow Analysis with Widening — Definitions
 *
 * Extension of df_analyze for infinite-height lattices.
 * Uses per-block visit counts and a widening operator that kicks in
 * after a threshold number of visits. Ensures convergence even when
 * the lattice has infinite ascending chains.
 *
 * TOP-LEVEL:
 *   df_analyze_widen        — run widening analysis on a function
 *   df_widen_at             — query lattice value at instruction point
 *   df_widen_boundary       — query boundary (exit for forward) value
 *   df_widen_entry          — query entry value (for soundness proofs)
 *
 * Helper:
 *   df_widen_state          — state with visit counts + entry cache
 *   df_process_block_widen  — process one block with widening logic
 *   init_df_widen_state     — initialize state
 *)

Theory dfAnalyzeWidenDefs
Ancestors
  dfAnalyzeDefs

(* ===== Widening state ===== *)

(* Extends df_state with per-block visit counts and cached entry values.
   dws_entry: stored so widening can compare old entry vs new join result.
   dws_visits: how many times each block has been processed. *)
Datatype:
  df_widen_state = <|
    dws_inst : (string # num, 'a) fmap;
    dws_boundary : (string, 'a) fmap;
    dws_entry : (string, 'a) fmap;
    dws_visits : (string, num) fmap
  |>
End

(* ===== Query API ===== *)

Definition df_widen_at_def:
  df_widen_at (bottom : 'a) (st : 'a df_widen_state) lbl idx =
    case FLOOKUP st.dws_inst (lbl, idx) of
      NONE => bottom
    | SOME v => v
End

Definition df_widen_boundary_def:
  df_widen_boundary (bottom : 'a) (st : 'a df_widen_state) lbl =
    case FLOOKUP st.dws_boundary lbl of
      NONE => bottom
    | SOME v => v
End

Definition df_widen_entry_def:
  df_widen_entry (bottom : 'a) (st : 'a df_widen_state) lbl =
    case FLOOKUP st.dws_entry lbl of
      NONE => bottom
    | SOME v => v
End

Definition df_widen_visits_def:
  df_widen_visits (st : 'a df_widen_state) lbl =
    case FLOOKUP st.dws_visits lbl of
      NONE => 0
    | SOME n => n
End

(* ===== Initialization ===== *)

Definition init_df_widen_state_def:
  init_df_widen_state (bottom : 'a) (lbls : string list)
    : 'a df_widen_state =
    <| dws_inst := FEMPTY;
       dws_boundary :=
         FOLDL (λm lbl. m |+ (lbl, bottom)) FEMPTY lbls;
       dws_entry := FEMPTY;
       dws_visits := FEMPTY |>
End

(* ===== Per-block processing with widening ===== *)

(* Process one block: gather neighbor values, join, optionally widen,
   fold transfer, update state.
   - After threshold visits, widen the joined entry against old entry
   - Boundary uses inflationary join (join old final_val) for convergence
   - Entry value is cached for future widening comparisons *)
Definition df_process_block_widen_def:
  df_process_block_widen dir bottom join widen threshold
                         transfer edge_transfer ctx entry_val
                         cfg bbs lbl (st : 'a df_widen_state) =
    let visits = df_widen_visits st lbl in
    let neighbors =
      (case dir of
         Forward => cfg_preds_of cfg lbl
       | Backward => cfg_succs_of cfg lbl) in
    let edge_vals = MAP (λnbr.
          edge_transfer ctx nbr lbl
            (df_widen_boundary bottom st nbr)) neighbors in
    let joined =
      (case edge_vals of
         [] => (case entry_val of
                  NONE => bottom
                | SOME (ev_lbl, v) =>
                    if lbl = ev_lbl then v else bottom)
       | _ => FOLDL join bottom edge_vals) in
    let entry =
      if visits >= threshold then
        widen (df_widen_entry bottom st lbl) joined
      else joined in
    let instrs =
      (case lookup_block lbl bbs of
         NONE => []
       | SOME bb => bb.bb_instructions) in
    let (final_val, inst_map) =
      df_fold_block dir (transfer ctx) lbl instrs entry in
    let old_boundary = df_widen_boundary bottom st lbl in
    let new_boundary = join old_boundary final_val in
    st with <|
      dws_boundary := st.dws_boundary |+ (lbl, new_boundary);
      dws_entry := st.dws_entry |+ (lbl, entry);
      dws_inst := FUNION inst_map st.dws_inst;
      dws_visits := st.dws_visits |+ (lbl, visits + 1)
    |>
End

(* ===== Top-level analysis ===== *)

(* Generic dataflow analysis with widening.
   Same structure as df_analyze but uses df_widen_state and
   widening after threshold visits per block.
   Parameters:
     dir        — Forward | Backward
     bottom     — lattice bottom element
     join       — lattice join (binary)
     widen      — widening operator (old → new → widened)
     threshold  — visit count after which to widen
     transfer   — per-instruction transfer
     edge_transfer — per-edge transfer (branch refinement, PHI renaming)
     ctx        — analysis-specific context
     entry_val  — optional entry block override
     fn         — function to analyze *)
Definition df_analyze_widen_def:
  df_analyze_widen dir bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn =
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let lbls = MAP (λbb. bb.bb_label) bbs in
    let st0 = init_df_widen_state bottom lbls in
    let st0' =
      (case entry_val of
         NONE => st0
       | SOME (lbl, v) =>
           st0 with dws_boundary := st0.dws_boundary |+ (lbl, v)) in
    let process =
      df_process_block_widen dir bottom join widen threshold
                             transfer edge_transfer ctx entry_val
                             cfg bbs in
    let deps =
      (case dir of
         Forward => cfg_succs_of cfg
       | Backward => cfg_preds_of cfg) in
    let wl0 =
      (case dir of
         Forward => cfg.cfg_dfs_pre
       | Backward => cfg.cfg_dfs_post) in
    SND (wl_iterate process deps wl0 st0')
End
