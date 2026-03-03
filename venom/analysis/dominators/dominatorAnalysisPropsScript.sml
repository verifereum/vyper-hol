(*
 * Dominator Analysis — Property Statements
 *
 * Exported API for consumers of the dominator analysis.
 *
 * 1) Fixpoint — dom_analyze returns a stable dom set.
 * 2) Boundedness — dominator sets ⊆ fn_labels.
 * 3) Entry dominance — entry dominates all reachable blocks.
 * 4) Self dominance — every block dominates itself.
 * 5) Transitivity — dominates is transitive.
 * 6) Antisymmetry — dominates is antisymmetric (for reachable blocks).
 * 7) Immediate dominator — idom is closest strict dominator.
 * 8) Dominance frontier — DF characterization.
 *
 * Proofs will live in proofs/dominatorProofsScript.sml.
 *)

Theory dominatorAnalysisProps
Ancestors
  dominatorProofs

(* ==========================================================================
   1) Fixpoint — one more pass does not change dom sets
   ========================================================================== *)

(* After dom_analyze, applying dom_one_pass again yields the same map.
   Ensures the iterative fixpoint has converged. *)
Theorem dom_analyze_fixpoint:
  ∀fn cfg.
    wf_function fn ∧
    cfg = cfg_analyze fn ⇒
    let dom = dom_analyze cfg fn in
    let entry = case entry_block fn of NONE => "" | SOME bb => bb.bb_label in
    dom_one_pass cfg entry cfg.cfg_dfs_post dom.da_dominators =
      dom.da_dominators
Proof
  cheat
QED

(* ==========================================================================
   2) Boundedness — dominator sets only contain function labels
   ========================================================================== *)

(* Every element of dom(lbl) is a label of some block in the function. *)
Theorem dom_labels_bounded:
  ∀fn cfg lbl d.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    MEM lbl (fn_labels fn) ⇒
    let dom = dom_analyze cfg fn in
    MEM d (fmap_lookup_list dom.da_dominators lbl) ⇒
    MEM d (fn_labels fn)
Proof
  cheat
QED

(* ==========================================================================
   3) Entry dominance — entry dominates all reachable blocks
   ========================================================================== *)

(* For a well-formed function with entry block, the entry label appears
   in dom(lbl) for every reachable label. *)
Theorem dom_entry_dominates_all:
  ∀fn cfg bb lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ∧
    cfg_reachable_of cfg lbl ⇒
    dominates (dom_analyze cfg fn) bb.bb_label lbl
Proof
  cheat
QED

(* ==========================================================================
   4) Self dominance — every block in the function dominates itself
   ========================================================================== *)

(* Every label that appears in the function's blocks dominates itself. *)
Theorem dom_self:
  ∀fn cfg lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    MEM lbl (fn_labels fn) ⇒
    dominates (dom_analyze cfg fn) lbl lbl
Proof
  cheat
QED

(* ==========================================================================
   5) Transitivity — if a dominates b and b dominates c, then a dominates c
   ========================================================================== *)

(* Dominates is transitive on reachable blocks. *)
Theorem dominates_trans:
  ∀fn cfg a b c.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg c ⇒
    let dom = dom_analyze cfg fn in
    dominates dom a b ∧ dominates dom b c ⇒
    dominates dom a c
Proof
  cheat
QED

(* ==========================================================================
   6) Antisymmetry — if a dominates b and b dominates a, then a = b
   ========================================================================== *)

(* Dominates is antisymmetric on reachable blocks. Together with reflexivity
   (dom_self) and transitivity, this makes dominance a partial order. *)
Theorem dominates_antisym:
  ∀fn cfg a b.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg a ∧
    cfg_reachable_of cfg b ⇒
    let dom = dom_analyze cfg fn in
    dominates dom a b ∧ dominates dom b a ⇒
    a = b
Proof
  cheat
QED

(* ==========================================================================
   7) Immediate dominator — idom is closest strict dominator
   ========================================================================== *)

(* If idom(lbl) = SOME d, then d strictly dominates lbl and every other
   strict dominator of lbl also dominates d. *)
Theorem idom_is_immediate:
  ∀fn cfg lbl d.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg lbl ⇒
    let dom = dom_analyze cfg fn in
    idom_of dom lbl = SOME d ⇒
    strict_dominates dom d lbl ∧
    ∀d'. strict_dominates dom d' lbl ∧ d' ≠ d ⇒
         dominates dom d' d
Proof
  cheat
QED

(* Entry block has no immediate dominator. *)
Theorem idom_entry_none:
  ∀fn cfg bb.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ⇒
    idom_of (dom_analyze cfg fn) bb.bb_label = NONE
Proof
  cheat
QED

(* ==========================================================================
   8) Dominance frontier correctness
   ========================================================================== *)

(* y is in the dominance frontier of n iff there exists a predecessor p
   of y such that n dominates p but n does not strictly dominate y. *)
Theorem df_correct:
  ∀fn cfg n y.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg n ∧
    cfg_reachable_of cfg y ⇒
    let dom = dom_analyze cfg fn in
    (MEM y (frontier_of dom n) ⇔
     ∃p. MEM p (cfg_preds_of cfg y) ∧
         dominates dom n p ∧
         ¬strict_dominates dom n y)
Proof
  cheat
QED
