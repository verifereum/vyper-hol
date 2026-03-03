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
 * Proofs will live in proofs/dominatorProofsScript.sml.
 *)

Theory dominatorAnalysisProps
Ancestors
  dominatorProofs

(* ==========================================================================
   1) Domain — da_dominators covers all fn_labels
   ========================================================================== *)

(* Every label in the function has a dominator set entry. *)
Theorem dom_analyze_domain:
  ∀fn cfg lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    MEM lbl (fn_labels fn) ⇒
    lbl ∈ FDOM (dom_analyze cfg fn).da_dominators
Proof
  cheat
QED

(* ==========================================================================
   2) Fixpoint equation — dom sets satisfy the dominator recurrence

   For non-entry reachable blocks, dom(lbl) as a set equals
   {lbl} ∪ ∩{dom(p) | p ∈ preds(lbl)}.
   This is the fundamental characterization of the dominator fixpoint.
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
  cheat
QED

(* Entry block dominates only itself. *)
Theorem dom_entry_self:
  ∀fn cfg bb.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ⇒
    set (fmap_lookup_list (dom_analyze cfg fn).da_dominators bb.bb_label) =
      {bb.bb_label}
Proof
  cheat
QED

(* ==========================================================================
   3) Boundedness — dominator sets only contain function labels
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
   4) Entry dominance — entry dominates all reachable blocks
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
   5) Self dominance — every block in the function dominates itself
   ========================================================================== *)

(* Every label in the function dominates itself.
   For unreachable blocks this holds vacuously (dom set = all labels from init,
   since dom_transfer only visits reachable blocks in cfg_dfs_post order). *)
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
   6) Transitivity — if a dominates b and b dominates c, then a dominates c
   ========================================================================== *)

(* Dominates is transitive on reachable blocks.
   Reachability of c suffices: b ∈ dom(c) with c reachable implies b reachable,
   and a ∈ dom(b) with b reachable implies a reachable. *)
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
   7) Antisymmetry — if a dominates b and b dominates a, then a = b
   ========================================================================== *)

(* Dominates is antisymmetric on reachable blocks. Together with reflexivity
   (dom_self) and transitivity, this makes dominance a partial order.
   Both reachability conditions are needed: for unreachable blocks,
   dom = all labels, so mutual dominance holds for any two unreachable blocks. *)
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
   8) Immediate dominator — idom is closest strict dominator
   ========================================================================== *)

(* If idom(lbl) = SOME d, then d strictly dominates lbl and every other
   strict dominator of lbl also dominates d (i.e., d is the closest
   strict dominator in the dominator tree). *)
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

(* ==========================================================================
   9) Immediate dominator existence — every reachable non-entry block has idom
   ========================================================================== *)

(* Every reachable non-entry block has an immediate dominator.
   Consumers (make_ssa, mem_ssa) rely on idom_of returning SOME. *)
Theorem idom_exists:
  ∀fn cfg bb lbl.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    entry_block fn = SOME bb ∧
    cfg_reachable_of cfg lbl ∧
    lbl ≠ bb.bb_label ⇒
    ∃d. idom_of (dom_analyze cfg fn) lbl = SOME d
Proof
  cheat
QED

(* ==========================================================================
  10) Immediate dominator — entry has no idom
   ========================================================================== *)

(* Entry block has no immediate dominator (it is the root of the dom tree). *)
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
  11) Dom-tree children — dominated_of is the inverse of idom_of
   ========================================================================== *)

(* c appears in dominated_of(n) iff idom(c) = n. This is the bidirectional
   link consumers need to traverse the dominator tree. *)
Theorem dominated_iff_idom:
  ∀fn cfg n c.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    MEM n (fn_labels fn) ∧
    MEM c (fn_labels fn) ⇒
    let dom = dom_analyze cfg fn in
    (MEM c (dominated_of dom n) ⇔ idom_of dom c = SOME n)
Proof
  cheat
QED

(* ==========================================================================
  12) Dominance frontier correctness
   ========================================================================== *)

(* y is in the dominance frontier of n iff there exists a CFG predecessor p
   of y such that n dominates p but n does not strictly dominate y.
   For single-predecessor y, the condition is never satisfiable: the unique
   pred's dominator must also strictly dominate y. *)
Theorem dom_frontier_correct:
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
