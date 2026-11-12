(*
 * Memory Alias Analysis — Properties
 *
 * Consumers need both `memAliasProps` and `memAliasProofs`: the structural
 * results (ma_analyze_wf, ma_may_alias_iff, ma_different_alloca_no_alias,
 * ma_empty_no_alias, ma_mark_volatile_is_volatile,
 * ma_mark_volatile_preserves_wf) live only in memAliasProofs.
 *
 * Here:
 *   ma_may_alias_sound                 — ¬ma_may_alias ⟹ runtime disjointness
 *   ma_may_alias_sound_no_alloca       — re-exported from memAliasProofs
 *   bp_segment_from_ops_runtime_region — connects analysis mem_loc to runtime region
 *
 * General memory properties (allocas_non_overlapping, regions_disjoint,
 * mload_mstore_disjoint) are in venomMemProps — not analysis-specific.
 * memloc_runtime_region is in memLocDefs.
 *)

Theory memAliasProps
Ancestors
  memAliasDefs memAliasProofs basePtrProps venomMemProps memLocDefs

(* ===== Soundness Theorems ===== *)

(* ¬ma_may_alias ⟹ runtime regions are disjoint.
   Uses allocas_non_overlapping and regions_disjoint from venomMemDefs. *)
Theorem ma_may_alias_sound:
  ∀sets loc1 loc2 s r1 r2.
    wf_alias_sets sets ∧
    ¬ma_may_alias sets loc1 loc2 ∧
    allocas_non_overlapping s ∧
    memloc_within_alloca loc1 s ∧
    memloc_within_alloca loc2 s ∧
    memloc_runtime_region loc1 s = SOME r1 ∧
    memloc_runtime_region loc2 s = SOME r2 ⇒
    regions_disjoint r1 r2
Proof ACCEPT_TAC memAliasProofsTheory.ma_may_alias_sound_proof
QED

(* Re-exported for existing references to memAliasPropsTheory. *)
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
Proof ACCEPT_TAC memAliasProofsTheory.ma_may_alias_sound_no_alloca
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
