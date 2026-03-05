(*
 * Value Range Lattice — Proofs
 *
 * Proves lattice properties for value_range:
 *   - partial order (reflexive, antisymmetric, transitive)
 *   - join/meet correctness
 *   - widening is an upper bound
 *   - in_range soundness helpers
 *)

Theory valueRangeProofs
Ancestors
  valueRangeDefs
Libs
  integerTheory integer_wordTheory

(* ===== Partial Order ===== *)

(* vr_leq is reflexive *)
Theorem vr_leq_refl:
  ∀r. vr_leq r r
Proof
  Cases >> rw[vr_leq_def]
QED

(* vr_leq is antisymmetric *)
Theorem vr_leq_antisym:
  ∀a b. vr_leq a b ∧ vr_leq b a ⇒ a = b
Proof
  Cases >> Cases >> rw[vr_leq_def] >> rw[] >>
  intLib.ARITH_TAC
QED

(* vr_leq is transitive *)
Theorem vr_leq_trans:
  ∀a b c. vr_leq a b ∧ vr_leq b c ⇒ vr_leq a c
Proof
  Cases >> Cases >> Cases >> rw[vr_leq_def] >>
  intLib.ARITH_TAC
QED

(* ===== Join (Union) ===== *)

(* vr_union is an upper bound of both arguments *)
Theorem vr_union_upper_l:
  ∀a b. vr_leq a (vr_union a b)
Proof
  Cases >> Cases >> rw[vr_union_def, vr_leq_def, integerTheory.INT_MIN, integerTheory.INT_MAX] >>
  intLib.ARITH_TAC
QED

Theorem vr_union_upper_r:
  ∀a b. vr_leq b (vr_union a b)
Proof
  Cases >> Cases >> rw[vr_union_def, vr_leq_def, integerTheory.INT_MIN, integerTheory.INT_MAX] >>
  intLib.ARITH_TAC
QED

(* BOTTOM is the identity for union *)
Theorem vr_union_bottom_l:
  ∀r. vr_union VR_Bottom r = r
Proof
  rw[vr_union_def]
QED

Theorem vr_union_bottom_r:
  ∀r. vr_union r VR_Bottom = r
Proof
  Cases >> rw[vr_union_def]
QED

(* TOP absorbs union *)
Theorem vr_union_top_l:
  ∀r. vr_union VR_Top r = VR_Top
Proof
  Cases >> rw[vr_union_def]
QED

(* ===== Meet (Intersect) ===== *)

(* vr_intersect is a lower bound of both arguments *)
Theorem vr_intersect_lower_l:
  ∀a b. vr_leq (vr_intersect a b) a
Proof
  Cases >> Cases >> rw[vr_intersect_def, vr_leq_def, integerTheory.INT_MIN, integerTheory.INT_MAX] >>
  rw[] >> intLib.ARITH_TAC
QED

Theorem vr_intersect_lower_r:
  ∀a b. vr_leq (vr_intersect a b) b
Proof
  Cases >> Cases >> rw[vr_intersect_def, vr_leq_def, integerTheory.INT_MIN, integerTheory.INT_MAX] >>
  rw[] >> intLib.ARITH_TAC
QED

(* ===== Widening ===== *)

(* Widening produces an upper bound of the new value *)
Theorem vr_widen_upper_new:
  ∀old new. vr_leq new (vr_widen old new)
Proof
  Cases >> Cases >> rw[vr_widen_def, vr_leq_def] >> rw[]
QED

(* Widening result: either TOP, or old, or new *)
Theorem vr_widen_result:
  ∀old new.
    vr_widen old new = VR_Top ∨
    vr_widen old new = old ∨
    vr_widen old new = new
Proof
  Cases >> Cases >> rw[vr_widen_def] >> rw[]
QED

(* ===== in_range basics ===== *)

(* TOP contains everything *)
Theorem in_range_top:
  ∀w. in_range VR_Top w
Proof
  rw[in_range_def]
QED

(* BOTTOM contains nothing *)
Theorem in_range_bottom:
  ∀w. ¬in_range VR_Bottom w
Proof
  rw[in_range_def]
QED

(* Constant range contains exactly that constant *)
Theorem in_range_constant:
  ∀v w. in_range (vr_constant v) w ⇔ w2i w = v
Proof
  rw[in_range_def, vr_constant_def] >> intLib.ARITH_TAC
QED

(* If in_range r w and vr_leq r r', then in_range r' w *)
Theorem in_range_monotone:
  ∀r r' w. in_range r w ∧ vr_leq r r' ⇒ in_range r' w
Proof
  Cases >> Cases >> rw[in_range_def, vr_leq_def] >> intLib.ARITH_TAC
QED

(* Union soundness: if w is in either range, it's in the union *)
Theorem in_range_union_l:
  ∀a b w. in_range a w ⇒ in_range (vr_union a b) w
Proof
  rpt strip_tac >>
  irule in_range_monotone >>
  qexists_tac `a` >> rw[vr_union_upper_l]
QED

Theorem in_range_union_r:
  ∀a b w. in_range b w ⇒ in_range (vr_union a b) w
Proof
  rpt strip_tac >>
  irule in_range_monotone >>
  qexists_tac `b` >> rw[vr_union_upper_r]
QED

(* Intersect soundness: if w is in the intersect, it's in both *)
Theorem in_range_intersect:
  ∀a b w.
    in_range (vr_intersect a b) w ⇒
    in_range a w ∧ in_range b w
Proof
  Cases >> Cases >>
  rw[in_range_def, vr_intersect_def, integerTheory.INT_MIN, integerTheory.INT_MAX] >>
  rw[] >> intLib.ARITH_TAC
QED
