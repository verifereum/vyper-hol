(*
 * Lowering Memory Safety — Properties
 *
 * Top-level theorems only. Internal proof helpers remain in
 * loweringMemSafetyProofsTheory.
 *)

Theory loweringMemSafetyProps
Ancestors
  loweringMemSafetyProofs loweringMemSafetyDefs allocaRemapDefs

(* ===== Type-safety interface ===== *)

Theorem value_type_fits_alloca:
  ∀cenv tenv ty tv v.
    evaluate_type tenv ty = SOME tv ∧
    value_has_type tv v ∧ well_formed_type_value tv
  ⇒ value_within_alloca_size cenv ty v
Proof
  ACCEPT_TAC loweringMemSafetyProofsTheory.value_type_fits_alloca
QED

(* ===== Alloca uniqueness ===== *)

Theorem alloca_regions_same:
  ∀s a1 a2 b1 sz1 b2 sz2 x.
    allocas_non_overlapping s ∧
    FLOOKUP s.vs_allocas a1 = SOME (b1,sz1) ∧
    FLOOKUP s.vs_allocas a2 = SOME (b2,sz2) ∧
    b1 ≤ x ∧ x < b1 + sz1 ∧ b2 ≤ x ∧ x < b2 + sz2
    ⇒ a1 = a2 ∧ b1 = b2 ∧ sz1 = sz2
Proof
  ACCEPT_TAC loweringMemSafetyProofsTheory.alloca_regions_same
QED

(* ===== Execution safety preservation ===== *)

Theorem reachable_preserves_safety:
  ∀fn roots s s'.
    step_preserves_safety fn roots ∧
    alloca_safe_access fn roots s ∧
    ptrs_in_alloca_bounds fn roots s ∧
    reachable_by_execution fn s s'
    ⇒ alloca_safe_access fn roots s' ∧ ptrs_in_alloca_bounds fn roots s'
Proof
  ACCEPT_TAC loweringMemSafetyProofsTheory.reachable_preserves_safety
QED
