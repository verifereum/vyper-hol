(*
 * Dominator Tree Analysis — Definitions
 *
 * Ports vyper/venom/analysis/dominators.py to HOL4.
 * Algorithm: iterative fixpoint (Cooper, Harvey, Kennedy 2001).
 *
 * TOP-LEVEL:
 *   dom_analyze            — run full dominator analysis on cfg + function
 *   dom_analysis           — result record
 *   dominates              — does d dominate n?
 *   strict_dominates       — does d strictly dominate n?
 *   idom_of                — immediate dominator lookup
 *   dominated_of           — dom-tree children lookup
 *   frontier_of            — dominance frontier lookup
 *   frontier_set           — dominance frontier of a set of blocks
 *
 * Helper (internal):
 *   dom_transfer_inst       — per-instruction transfer (identity)
 *   dom_edge_transfer       — add dst to predecessor dom set
 *   dom_fixpoint            — run df_analyze Forward for dominator sets
 *   dom_sets_of             — extract dominator fmap from df_state
 *   compute_idom_for        — idom for a single label
 *   compute_idom            — idom for all labels
 *   compute_dominated       — invert idom to get dom-tree children
 *   walk_to_idom            — helper walk for dominance frontier
 *   compute_df              — dominance frontier for all blocks
 *)

Theory dominatorDefs
Ancestors
  list finite_map pred_set
  venomInst cfgDefs dfAnalyzeDefs dfHelperDefs
Libs
  listTheory finite_mapTheory pred_setTheory pairTheory

(* ==========================================================================
   Result type
   ========================================================================== *)

(*
 * da_dominators : label → dominator set (as list)
 * da_idom       : label → immediate dominator (entry not in domain)
 * da_dominated  : label → dom-tree children
 * da_frontier   : label → dominance frontier
 *)
Datatype:
  dom_analysis = <|
    da_dominators : (string, string list) fmap;
    da_idom       : (string, string) fmap;
    da_dominated  : (string, string list) fmap;
    da_frontier   : (string, string list) fmap
  |>
End

(* ==========================================================================
   Query API
   ========================================================================== *)

(* d dominates n: d is in dom(n). *)
Definition dominates_def:
  dominates dom d n ⇔
    MEM d (fmap_lookup_list dom.da_dominators n)
End

(* d strictly dominates n: d dominates n and d ≠ n. *)
Definition strict_dominates_def:
  strict_dominates dom d n ⇔
    dominates dom d n ∧ d ≠ n
End

(* Immediate dominator of n. NONE for entry block. *)
Definition idom_of_def:
  idom_of dom n = FLOOKUP dom.da_idom n
End

(* Children in dom tree (blocks immediately dominated by n). *)
Definition dominated_of_def:
  dominated_of dom n = fmap_lookup_list dom.da_dominated n
End

(* Dominance frontier of n. *)
Definition frontier_of_def:
  frontier_of dom n = fmap_lookup_list dom.da_frontier n
End

(* Dominance frontier of a set of blocks. *)
Definition frontier_set_def:
  frontier_set dom lbls =
    nub (FLAT (MAP (frontier_of dom) lbls))
End

(* ==========================================================================
   Phase 1: Compute dominator sets via df_analyze

   dom[entry] = {entry}
   dom[b]     = {b} ∪ ∩{dom[p] | p ∈ preds(b)}

   Lattice: (P(labels), ⊇) — all labels = bottom (identity for ∩).
   Transfer: identity (dominators are block-level, not per-instruction).
   Edge transfer: set_insert dst — adds current block to each predecessor's
     dominator set before intersection.
   ========================================================================== *)

(* Per-instruction transfer: identity.
   Dominators don't change within a block; the {b} is handled by
   edge_transfer adding dst to each predecessor's dominator set. *)
Definition dom_transfer_inst_def:
  dom_transfer_inst (() : unit) (inst : instruction)
                    (doms : string list) = doms
End

(* Edge transfer: add the destination block to the predecessor's dom set.
   For block b with predecessors p1, p2:
     edge_vals = [set_insert b dom[p1], set_insert b dom[p2]]
     joined = ∩{set_insert b dom[pi]} = {b} ∪ ∩{dom[pi]}
   This gives dom[b] = {b} ∪ ∩{dom[p] | p ∈ preds(b)} as desired. *)
Definition dom_edge_transfer_def:
  dom_edge_transfer (() : unit) (src : string) (dst : string)
                    (doms : string list) =
    set_insert dst doms
End

(* ==========================================================================
   Phase 2: Immediate dominators

   Sort dom(b) by post-order index; idom = second element.
   Entry block has no idom (not in da_idom domain).
   ========================================================================== *)

Definition post_order_index_def:
  post_order_index post_order lbl =
    case INDEX_OF lbl post_order of
      NONE => 0n
    | SOME i => i
End

(* idom for one label. Returns NONE for entry or if dom set is trivial. *)
Definition compute_idom_for_def:
  compute_idom_for post_order entry dom_sets lbl =
    if lbl = entry then NONE
    else
      let doms = fmap_lookup_list dom_sets lbl in
      let sorted = QSORT (λa b. post_order_index post_order a <
                                  post_order_index post_order b) doms in
      case sorted of
        [] => NONE
      | [_] => NONE
      | _ :: idom :: _ => SOME idom
End

(* Compute idom for all labels. Only non-entry blocks with ≥2 dominators
   get an entry in the map. *)
Definition compute_idom_def:
  compute_idom post_order entry dom_sets labels =
    FOLDL (λm lbl.
      case compute_idom_for post_order entry dom_sets lbl of
        NONE => m
      | SOME idom_lbl => m |+ (lbl, idom_lbl))
    FEMPTY labels
End

(* ==========================================================================
   Phase 2b: Dom-tree children (invert idom)
   ========================================================================== *)

Definition compute_dominated_def:
  compute_dominated idom labels =
    FOLDL (λm lbl.
      case FLOOKUP idom lbl of
        NONE => m
      | SOME parent =>
          let old = fmap_lookup_list m parent in
          m |+ (parent, set_insert lbl old))
    FEMPTY labels
End

(* ==========================================================================
   Phase 3: Dominance frontier

   DF(n) = {y | ∃ pred p of y: n dominates p ∧ n ≠ idom(y)}

   For each join point y (>1 pred), walk from each predecessor up the
   idom tree until reaching idom(y), adding y to df[runner] at each step.

   walk_to_idom uses fuel = LENGTH labels. The idom tree is a tree rooted
   at entry, so the walk visits at most |labels| nodes. For well-formed
   inputs, the walk terminates before fuel runs out. Fuel avoids needing
   an acyclicity precondition in the definition.
   ========================================================================== *)

Definition walk_to_idom_def:
  walk_to_idom idom target runner df 0 = df ∧
  walk_to_idom idom target runner df (SUC fuel) =
    (case FLOOKUP idom target of
       NONE => df
     | SOME target_idom =>
         if runner = target_idom then df
         else
           let old = fmap_lookup_list df runner in
           let df' = df |+ (runner, set_insert target old) in
           case FLOOKUP idom runner of
             NONE => df'
           | SOME next =>
               walk_to_idom idom target next df' fuel)
End

Definition compute_df_def:
  compute_df cfg idom order fuel =
    FOLDL (λdf lbl.
      let preds = cfg_preds_of cfg lbl in
      if LENGTH preds ≤ 1 then df
      else
        FOLDL (λdf' pred.
          walk_to_idom idom lbl pred df' fuel)
        df preds)
    FEMPTY order
End

(* ==========================================================================
   Top-level: run full dominator analysis
   ========================================================================== *)

(* Run dominator fixpoint via df_analyze Forward. *)
Definition dom_fixpoint_def:
  dom_fixpoint fn =
    let entry =
      case entry_block fn of
        NONE => ""
      | SOME bb => bb.bb_label in
    let all_labels = fn_labels fn in
    df_analyze Forward all_labels list_intersect dom_transfer_inst
              dom_edge_transfer () (SOME (entry, [entry])) fn
End

(* Extract dominator sets from df_state.
   Boundary value at each block = dom set for that block. *)
Definition dom_sets_of_def:
  dom_sets_of fn (st : string list df_state) =
    let all_labels = fn_labels fn in
    FOLDL (λm lbl. m |+ (lbl, df_boundary all_labels st lbl))
          FEMPTY (fn_labels fn)
End

Definition dom_analyze_def:
  dom_analyze cfg fn =
    let entry =
      case entry_block fn of
        NONE => ""
      | SOME bb => bb.bb_label in
    let labels = fn_labels fn in
    let st = dom_fixpoint fn in
    let dom_sets = dom_sets_of fn st in
    let order = cfg.cfg_dfs_post in
    let idom = compute_idom order entry dom_sets labels in
    let dominated = compute_dominated idom labels in
    let fuel = LENGTH labels in
    let df = compute_df cfg idom order fuel in
    <| da_dominators := dom_sets;
       da_idom := idom;
       da_dominated := dominated;
       da_frontier := df |>
End
