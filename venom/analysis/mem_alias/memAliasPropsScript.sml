(*
 * Memory Alias Analysis — Properties (public API)
 *
 * Re-exports proven properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors memAliasProps` to get defs + properties.
 *
 * TOP-LEVEL PROPERTIES:
 *   ma_analyze_wf                 — analysis output satisfies wf_alias_sets
 *   ma_may_alias_iff              — alias query ⟺ may_overlap (the key theorem)
 *   ma_different_alloca_no_alias  — different base allocations ⟹ no alias
 *   ma_empty_no_alias             — ml_empty never aliases with anything
 *   ma_mark_volatile_is_volatile  — returned location has volatile flag set
 *   ma_mark_volatile_preserves_wf — marking volatile preserves well-formedness
 *)

Theory memAliasProps
Ancestors
  memAliasDefs memAliasProofs

(* ===== Core ===== *)

(* The top-level analysis produces well-formed alias sets *)
Theorem ma_analyze_wf:
  ∀bp_result fn addr_sp.
    wf_alias_sets (ma_analyze bp_result fn addr_sp)
Proof ACCEPT_TAC memAliasProofsTheory.ma_analyze_wf
QED

(* For well-formed alias sets, the alias query is equivalent to may_overlap.
 * The analysis is a precomputation of pairwise may_overlap, not an
 * approximation — so consumers can reason purely about may_overlap. *)
Theorem ma_may_alias_iff:
  ∀sets loc1 loc2.
    wf_alias_sets sets ⇒
    (ma_may_alias sets loc1 loc2 ⇔ may_overlap loc1 loc2)
Proof ACCEPT_TAC memAliasProofsTheory.ma_may_alias_iff
QED

(* ===== Convenience corollaries ===== *)

(* Locations backed by different base allocations never alias *)
Theorem ma_different_alloca_no_alias:
  ∀sets loc1 loc2 a1 a2.
    wf_alias_sets sets ∧
    loc1.ml_alloca = SOME a1 ∧ loc2.ml_alloca = SOME a2 ∧ a1 ≠ a2 ⇒
    ¬ma_may_alias sets loc1 loc2
Proof ACCEPT_TAC memAliasProofsTheory.ma_different_alloca_no_alias
QED

(* The empty memory location (zero size at offset 0) never aliases *)
Theorem ma_empty_no_alias:
  ∀sets loc.
    wf_alias_sets sets ⇒
    ¬ma_may_alias sets ml_empty loc
Proof ACCEPT_TAC memAliasProofsTheory.ma_empty_no_alias
QED

(* ===== ma_mark_volatile ===== *)

(* The returned location has the volatile flag set *)
Theorem ma_mark_volatile_is_volatile:
  ∀sets loc vloc sets'.
    ma_mark_volatile sets loc = (vloc, sets') ⇒
    vloc.ml_volatile
Proof ACCEPT_TAC memAliasProofsTheory.ma_mark_volatile_is_volatile
QED

(* Marking a location volatile preserves well-formedness *)
Theorem ma_mark_volatile_preserves_wf:
  ∀sets loc vloc sets'.
    wf_alias_sets sets ∧
    ma_mark_volatile sets loc = (vloc, sets') ⇒
    wf_alias_sets sets'
Proof ACCEPT_TAC memAliasProofsTheory.ma_mark_volatile_preserves_wf
QED

