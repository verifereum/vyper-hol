(*
 * Venom Memory Definitions
 *
 * General predicates for memory layout and region disjointness.
 * These are venom_state properties, not analysis-specific.
 *
 * TOP-LEVEL:
 *   allocas_non_overlapping — distinct allocas have disjoint regions
 *   regions_disjoint        — two byte ranges don't overlap
 *)

Theory venomMemDefs
Ancestors
  venomState finite_map

(* Distinct allocas have disjoint memory regions.
 * Guaranteed by bump allocation: exec_alloca places each new alloca
 * at next_alloca_offset which is ≥ all existing (offset + size). *)
Definition allocas_non_overlapping_def:
  allocas_non_overlapping (s : venom_state) ⇔
    ∀a1 a2 b1 sz1 b2 sz2.
      a1 ≠ a2 ∧
      FLOOKUP s.vs_allocas a1 = SOME (b1, sz1) ∧
      FLOOKUP s.vs_allocas a2 = SOME (b2, sz2) ⇒
      b1 + sz1 ≤ b2 ∨ b2 + sz2 ≤ b1
End

Definition regions_disjoint_def:
  regions_disjoint (start1 : num, sz1 : num) (start2, sz2) ⇔
    sz1 = 0 ∨ sz2 = 0 ∨ start1 + sz1 ≤ start2 ∨ start2 + sz2 ≤ start1
End
