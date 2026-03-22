(*
 * Dominator Analysis — Property Statements
 *
 * Exported API for consumers of the dominator analysis.
 *
 *  1) Domain — da_dominators covers all fn_labels
 *  2) Fixpoint equation — dom sets satisfy the dominator recurrence
 *  3) Boundedness — dominator sets ⊆ fn_labels
 *  4) Entry dominance — entry dominates all reachable blocks
 *  5) Self dominance — every block dominates itself
 *  6) Transitivity — dominates is transitive
 *  7) Antisymmetry — dominates is antisymmetric (for reachable blocks)
 *  8) Immediate dominator — idom is closest strict dominator
 *  9) Immediate dominator existence — every reachable non-entry block has an idom
 * 10) Immediate dominator — entry has no idom
 * 11) Dom-tree children ↔ idom inverse
 * 12) Dominance frontier correctness
 *
 * Proofs live in proofs/dominatorProofsScript.sml.
 *)

Theory dominatorAnalysisProps
Ancestors
  dominatorProofs

(* ==========================================================================
   1) Domain — da_dominators covers all fn_labels
   ========================================================================== *)

Theorem dom_analyze_domain:
  ∀fn cfg lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    MEM lbl (fn_labels fn) ⇒
    lbl ∈ FDOM (dom_analyze cfg fn).da_dominators
Proof
  ACCEPT_TAC dom_analyze_domain_proof
QED

(* ==========================================================================
   2) Fixpoint equation — dom sets satisfy the dominator recurrence
   ========================================================================== *)

Theorem dom_fixpoint_equation:
  ∀fn cfg bb lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ∧
    cfg_reachable_of cfg lbl ∧
    lbl ≠ bb.bb_label ∧
    cfg_preds_of cfg lbl ≠ [] ⇒
    let dom = dom_analyze cfg fn in
    set (fmap_lookup_list dom.da_dominators lbl) =
      {lbl} ∪
      BIGINTER (IMAGE (λp. set (fmap_lookup_list dom.da_dominators p))
                      (set (cfg_preds_of cfg lbl)))
Proof
  ACCEPT_TAC dom_fixpoint_equation_proof
QED

(* The only dominator of the entry block is itself. *)
Theorem dom_entry_self:
  ∀fn cfg bb.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ⇒
    set (fmap_lookup_list (dom_analyze cfg fn).da_dominators bb.bb_label) =
      {bb.bb_label}
Proof
  ACCEPT_TAC dom_entry_self_proof
QED

(* ==========================================================================
   3) Boundedness — dominator sets only contain function labels
   ========================================================================== *)

Theorem dom_labels_bounded:
  ∀fn cfg lbl d.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    MEM lbl (fn_labels fn) ⇒
    let dom = dom_analyze cfg fn in
    MEM d (fmap_lookup_list dom.da_dominators lbl) ⇒
    MEM d (fn_labels fn)
Proof
  ACCEPT_TAC dom_labels_bounded_proof
QED

(* ==========================================================================
   4) Entry dominance — entry dominates all reachable blocks
   ========================================================================== *)

Theorem dom_entry_dominates_all:
  ∀fn cfg bb lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ∧
    cfg_reachable_of cfg lbl ⇒
    dominates (dom_analyze cfg fn) bb.bb_label lbl
Proof
  ACCEPT_TAC dom_entry_dominates_all_proof
QED

(* ==========================================================================
   5) Self dominance — every block in the function dominates itself
   ========================================================================== *)

Theorem dom_self:
  ∀fn cfg lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    MEM lbl (fn_labels fn) ⇒
    dominates (dom_analyze cfg fn) lbl lbl
Proof
  ACCEPT_TAC dom_self_proof
QED

(* ==========================================================================
   5b) Dominates implies reachable — a dominator of a reachable block is reachable
   ========================================================================== *)

Theorem dominates_reachable:
  ∀fn d p.
    wf_function fn ∧
    cfg_reachable_of (cfg_analyze fn) p ∧
    dominates (dom_analyze (cfg_analyze fn) fn) d p ⇒
    cfg_reachable_of (cfg_analyze fn) d
Proof
  ACCEPT_TAC dominates_reachable
QED

(* ==========================================================================
   6) Transitivity — if a dominates b and b dominates c, then a dominates c
   ========================================================================== *)

Theorem dominates_trans:
  ∀fn cfg a b c.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg c ⇒
    let dom = dom_analyze cfg fn in
    dominates dom a b ∧ dominates dom b c ⇒
    dominates dom a c
Proof
  ACCEPT_TAC dominates_trans_proof
QED

(* ==========================================================================
   7) Antisymmetry — if a dominates b and b dominates a, then a = b
   ========================================================================== *)

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
  ACCEPT_TAC dominates_antisym_proof
QED

(* ==========================================================================
   8) Immediate dominator — idom is closest strict dominator
   ========================================================================== *)

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
  ACCEPT_TAC idom_is_immediate_proof
QED

(* ==========================================================================
   9) Immediate dominator existence — every reachable non-entry block has idom
   ========================================================================== *)

Theorem idom_exists:
  ∀fn cfg bb lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ∧
    cfg_reachable_of cfg lbl ∧
    lbl ≠ bb.bb_label ⇒
    ∃d. idom_of (dom_analyze cfg fn) lbl = SOME d
Proof
  ACCEPT_TAC idom_exists_proof
QED

(* ==========================================================================
  10) Immediate dominator — entry has no idom
   ========================================================================== *)

Theorem idom_entry_none:
  ∀fn cfg bb.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ⇒
    idom_of (dom_analyze cfg fn) bb.bb_label = NONE
Proof
  ACCEPT_TAC idom_entry_none_proof
QED

(* ==========================================================================
  11) Dom-tree children — dominated_of is the inverse of idom_of
   ========================================================================== *)

Theorem dominated_iff_idom:
  ∀fn cfg n c.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    MEM n (fn_labels fn) ∧
    MEM c (fn_labels fn) ⇒
    let dom = dom_analyze cfg fn in
    (MEM c (dominated_of dom n) ⇔ idom_of dom c = SOME n)
Proof
  ACCEPT_TAC dominated_iff_idom_proof
QED

(* ==========================================================================
  12b) Dominator chain — dominators of a node are totally ordered
   ========================================================================== *)

Theorem dominates_chain:
  ∀fn cfg a b c.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg c ⇒
    let dom = dom_analyze cfg fn in
    dominates dom a c ∧ dominates dom b c ⇒
    dominates dom a b ∨ dominates dom b a
Proof
  ACCEPT_TAC dominates_chain_proof
QED

(* ==========================================================================
  12) Dominance frontier correctness
   ========================================================================== *)

Theorem dom_frontier_correct:
  ∀fn cfg n y.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg n ∧
    cfg_reachable_of cfg y ∧
    LENGTH (cfg_preds_of cfg y) > 1 ∧
    fn_entry_label fn ≠ SOME y ∧
    (∀p. MEM p (cfg_preds_of cfg y) ⇒ cfg_reachable_of cfg p) ⇒
    let dom = dom_analyze cfg fn in
    (MEM y (frontier_of dom n) ⇔
     ∃p. MEM p (cfg_preds_of cfg y) ∧
         dominates dom n p ∧
         ¬strict_dominates dom n y)
Proof
  ACCEPT_TAC dom_frontier_correct_proof
QED
