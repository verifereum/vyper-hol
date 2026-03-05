(*
 * Variable Range Analysis — Properties (public API)
 *
 * Re-exports proven properties from proofs/ via ACCEPT_TAC.
 *
 * TOP-LEVEL PROPERTIES:
 *   vr_leq_refl/antisym/trans — partial order
 *   vr_union_upper_l/r        — join is upper bound
 *   vr_intersect_lower_l/r    — meet is lower bound
 *   vr_widen_upper_new        — widening is upper bound of new
 *   vr_widen_result           — widening returns TOP or old or new
 *   in_range_top/bottom       — TOP/BOTTOM membership
 *   in_range_constant         — constant range characterization
 *   in_range_monotone         — range containment respects leq
 *   in_range_union_l/r        — union soundness
 *   in_range_intersect        — intersect soundness
 *)

Theory variableRangeAnalysisProps
Ancestors
  valueRangeDefs rangeEvalDefs rangeAnalysisDefs
  valueRangeProofs rangeEvalProofs rangeAnalysisProofs

(* ===== Partial Order ===== *)

Theorem vr_leq_refl:
  ∀r. vr_leq r r
Proof ACCEPT_TAC valueRangeProofsTheory.vr_leq_refl
QED

Theorem vr_leq_antisym:
  ∀a b. vr_leq a b ∧ vr_leq b a ⇒ a = b
Proof ACCEPT_TAC valueRangeProofsTheory.vr_leq_antisym
QED

Theorem vr_leq_trans:
  ∀a b c. vr_leq a b ∧ vr_leq b c ⇒ vr_leq a c
Proof ACCEPT_TAC valueRangeProofsTheory.vr_leq_trans
QED

(* ===== Join ===== *)

Theorem vr_union_upper_l:
  ∀a b. vr_leq a (vr_union a b)
Proof ACCEPT_TAC valueRangeProofsTheory.vr_union_upper_l
QED

Theorem vr_union_upper_r:
  ∀a b. vr_leq b (vr_union a b)
Proof ACCEPT_TAC valueRangeProofsTheory.vr_union_upper_r
QED

(* ===== Meet ===== *)

Theorem vr_intersect_lower_l:
  ∀a b. vr_leq (vr_intersect a b) a
Proof ACCEPT_TAC valueRangeProofsTheory.vr_intersect_lower_l
QED

Theorem vr_intersect_lower_r:
  ∀a b. vr_leq (vr_intersect a b) b
Proof ACCEPT_TAC valueRangeProofsTheory.vr_intersect_lower_r
QED

(* ===== Widening ===== *)

Theorem vr_widen_upper_new:
  ∀old new. vr_leq new (vr_widen old new)
Proof ACCEPT_TAC valueRangeProofsTheory.vr_widen_upper_new
QED

Theorem vr_widen_result:
  ∀old new.
    vr_widen old new = VR_Top ∨
    vr_widen old new = old ∨
    vr_widen old new = new
Proof ACCEPT_TAC valueRangeProofsTheory.vr_widen_result
QED

(* ===== in_range ===== *)

Theorem in_range_top:
  ∀w. in_range VR_Top w
Proof ACCEPT_TAC valueRangeProofsTheory.in_range_top
QED

Theorem in_range_bottom:
  ∀w. ¬in_range VR_Bottom w
Proof ACCEPT_TAC valueRangeProofsTheory.in_range_bottom
QED

Theorem in_range_constant:
  ∀v w. in_range (vr_constant v) w ⇔ w2i w = v
Proof ACCEPT_TAC valueRangeProofsTheory.in_range_constant
QED

Theorem in_range_monotone:
  ∀r r' w. in_range r w ∧ vr_leq r r' ⇒ in_range r' w
Proof ACCEPT_TAC valueRangeProofsTheory.in_range_monotone
QED

Theorem in_range_union_l:
  ∀a b w. in_range a w ⇒ in_range (vr_union a b) w
Proof ACCEPT_TAC valueRangeProofsTheory.in_range_union_l
QED

Theorem in_range_union_r:
  ∀a b w. in_range b w ⇒ in_range (vr_union a b) w
Proof ACCEPT_TAC valueRangeProofsTheory.in_range_union_r
QED

Theorem in_range_intersect:
  ∀a b w.
    in_range (vr_intersect a b) w ⇒
    in_range a w ∧ in_range b w
Proof ACCEPT_TAC valueRangeProofsTheory.in_range_intersect
QED
