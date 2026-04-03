(*
 * Venom Memory Properties
 *
 * General properties of memory operations and alloca layout.
 * These are venom_state properties, not analysis-specific —
 * usable by any pass or analysis that reasons about memory.
 *
 * TOP-LEVEL:
 *   allocas_non_overlapping       — distinct allocas have disjoint regions
 *   regions_disjoint              — two byte ranges don't overlap
 *   allocas_non_overlapping_empty — base case (no allocas)
 *   allocas_non_overlapping_step_inst — preserved by step_inst
 *   allocas_non_overlapping_run_block — preserved by run_block
 *   mload_mstore_disjoint        — disjoint 32-byte write/read independence
 *   mload_mstore8_disjoint       — disjoint 1-byte write / 32-byte read
 *)

Theory venomMemProps
Ancestors
  venomExecSemantics finite_map

(* ===== Alloca Non-Overlapping ===== *)

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

(* Base case: no allocas → trivially non-overlapping *)
Theorem allocas_non_overlapping_empty:
  ∀s. s.vs_allocas = FEMPTY ⇒ allocas_non_overlapping s
Proof
  rw[allocas_non_overlapping_def, FLOOKUP_DEF]
QED

(* step_inst preserves allocas_non_overlapping.
 * Only ALLOCA modifies vs_allocas; exec_alloca places new allocation
 * at next_alloca_offset ≥ all existing (offset + size). *)
Theorem allocas_non_overlapping_step_inst:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    allocas_non_overlapping s ⇒
    allocas_non_overlapping s'
Proof
  cheat
QED

(* run_block preserves allocas_non_overlapping. *)
Theorem allocas_non_overlapping_run_block:
  ∀fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ∧
    allocas_non_overlapping s ⇒
    allocas_non_overlapping s'
Proof
  cheat
QED

(* ===== Region Disjointness ===== *)

Definition regions_disjoint_def:
  regions_disjoint (start1 : num, sz1 : num) (start2, sz2) ⇔
    sz1 = 0 ∨ sz2 = 0 ∨ start1 + sz1 ≤ start2 ∨ start2 + sz2 ≤ start1
End

(* ===== Memory Operation Independence ===== *)

(* Writing 32 bytes at off1 doesn't affect reading 32 bytes at off2
 * when the regions don't overlap.
 * Key lemma for load_elim, MCE, mem2var proofs. *)
Theorem mload_mstore_disjoint:
  ∀off1 off2 val s.
    regions_disjoint (off1, 32) (off2, 32) ⇒
    mload off2 (mstore off1 val s) = mload off2 s
Proof
  cheat
QED

(* Writing 1 byte at off1 doesn't affect reading 32 bytes at off2
 * when the regions don't overlap. *)
Theorem mload_mstore8_disjoint:
  ∀off1 off2 val s.
    regions_disjoint (off1, 1) (off2, 32) ⇒
    mload off2 (mstore8 off1 val s) = mload off2 s
Proof
  cheat
QED
