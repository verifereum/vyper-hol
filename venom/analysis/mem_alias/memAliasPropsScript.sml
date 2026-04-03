(*
 * Memory Alias Analysis — Properties (public API)
 *
 * Re-exports proven properties from proofs/ via ACCEPT_TAC.
 * Consumers: just `Ancestors memAliasProps` to get defs + properties.
 *
 * Structural:
 *   ma_analyze_wf                 — analysis output satisfies wf_alias_sets
 *   ma_may_alias_iff              — alias query ⟺ may_overlap (the key theorem)
 *   ma_different_alloca_no_alias  — different base allocations ⟹ no alias
 *   ma_empty_no_alias             — ml_empty never aliases with anything
 *   ma_mark_volatile_is_volatile  — returned location has volatile flag set
 *   ma_mark_volatile_preserves_wf — marking volatile preserves well-formedness
 *
 * Soundness:
 *   ma_may_alias_sound            — ¬ma_may_alias ⟹ runtime disjointness
 *   ma_may_alias_sound_no_alloca  — simplified: both ml_alloca = NONE
 *
 * Bridge (analysis → runtime):
 *   bp_segment_from_ops_runtime_region — connects analysis mem_loc to runtime region
 *
 * General memory properties (allocas_non_overlapping, regions_disjoint,
 * mload_mstore_disjoint) are in venomMemProps — not analysis-specific.
 * memloc_runtime_region is in memLocDefs.
 *)

Theory memAliasProps
Ancestors
  memAliasDefs memAliasProofs basePtrProps venomMemProps memLocDefs

(* ===== Structural Properties ===== *)

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

(* ===== Soundness Theorems ===== *)

(* ¬ma_may_alias ⟹ runtime regions are disjoint.
   Uses allocas_non_overlapping and regions_disjoint from venomMemDefs. *)
Theorem ma_may_alias_sound:
  ∀sets loc1 loc2 s r1 r2.
    wf_alias_sets sets ∧
    ¬ma_may_alias sets loc1 loc2 ∧
    allocas_non_overlapping s ∧
    memloc_runtime_region loc1 s = SOME r1 ∧
    memloc_runtime_region loc2 s = SOME r2 ⇒
    regions_disjoint r1 r2
Proof ACCEPT_TAC memAliasProofsTheory.ma_may_alias_sound_proof
QED

(* Simplified: both locations have ml_alloca = NONE (absolute addresses).
   No alloca precondition needed — disjointness follows from may_overlap. *)
Theorem ma_may_alias_sound_no_alloca:
  ∀sets loc1 loc2.
    wf_alias_sets sets ∧
    ¬ma_may_alias sets loc1 loc2 ∧
    loc1.ml_alloca = NONE ∧ loc2.ml_alloca = NONE ∧
    IS_SOME loc1.ml_offset ∧ IS_SOME loc1.ml_size ∧
    IS_SOME loc2.ml_offset ∧ IS_SOME loc2.ml_size ⇒
    regions_disjoint
      (THE loc1.ml_offset, THE loc1.ml_size)
      (THE loc2.ml_offset, THE loc2.ml_size)
Proof ACCEPT_TAC memAliasProofsTheory.ma_may_alias_sound_no_alloca_proof
QED

(* ===== Bridge: Analysis → Runtime ===== *)

(* When bp_segment_from_ops produces a fixed mem_loc (known offset + size),
 * memloc_runtime_region returns the matching runtime region. *)
Theorem bp_segment_from_ops_runtime_region:
  ∀bp ops ml s.
    bp_ptr_sound bp s ∧
    bp_segment_from_ops bp ops = ml ∧
    ml_is_fixed ml ∧
    IS_SOME (eval_operand ops.iao_ofst s) ⇒
    ∃addr.
      eval_operand ops.iao_ofst s = SOME (n2w addr) ∧
      memloc_runtime_region ml s = SOME (addr, THE ml.ml_size)
Proof ACCEPT_TAC memAliasProofsTheory.bp_segment_from_ops_runtime_region_proof
QED
