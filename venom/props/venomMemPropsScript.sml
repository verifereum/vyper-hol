(*
 * Venom Memory Properties
 *
 * General properties of memory operations and alloca layout.
 * Re-exports proven properties from venomMemProofs via ACCEPT_TAC.
 * Definitions are in venomMemDefs.
 *
 * TOP-LEVEL:
 *   allocas_non_overlapping_empty     — base case (no allocas)
 *   allocas_non_overlapping_step_inst — preserved by step_inst
 *   allocas_non_overlapping_run_block — preserved by run_block
 *   mload_mstore_disjoint            — disjoint 32-byte write/read independence
 *   mload_mstore8_disjoint           — disjoint 1-byte write / 32-byte read
 *)

Theory venomMemProps
Ancestors
  venomMemDefs venomMemProofs venomExecSemantics

Theorem allocas_non_overlapping_empty:
  ∀s. s.vs_allocas = FEMPTY ⇒ allocas_non_overlapping s
Proof ACCEPT_TAC venomMemProofsTheory.allocas_non_overlapping_empty_proof
QED

Theorem allocas_non_overlapping_step_inst:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    allocas_non_overlapping s ⇒
    allocas_non_overlapping s'
Proof ACCEPT_TAC venomMemProofsTheory.allocas_non_overlapping_step_inst_proof
QED

Theorem allocas_non_overlapping_run_block:
  ∀fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ∧
    allocas_non_overlapping s ⇒
    allocas_non_overlapping s'
Proof ACCEPT_TAC venomMemProofsTheory.allocas_non_overlapping_run_block_proof
QED

Theorem mload_mstore_disjoint:
  ∀off1 off2 val s.
    regions_disjoint (off1, 32) (off2, 32) ⇒
    mload off2 (mstore off1 val s) = mload off2 s
Proof ACCEPT_TAC venomMemProofsTheory.mload_mstore_disjoint_proof
QED

Theorem mload_mstore8_disjoint:
  ∀off1 off2 val s.
    regions_disjoint (off1, 1) (off2, 32) ⇒
    mload off2 (mstore8 off1 val s) = mload off2 s
Proof ACCEPT_TAC venomMemProofsTheory.mload_mstore8_disjoint_proof
QED
