(*
 * Venom Memory Proofs
 *
 * TOP-LEVEL:
 *   allocas_non_overlapping_empty_proof     — base case
 *   allocas_non_overlapping_step_inst_proof — preserved by step_inst
 *   allocas_non_overlapping_exec_block_proof — preserved by exec_block
 *   mload_mstore_disjoint_proof             — 32-byte write/read independence
 *   mload_mstore8_disjoint_proof            — 1-byte write / 32-byte read
 *)

Theory venomMemProofs
Ancestors
  venomMemDefs venomExecSemantics finite_map

Theorem allocas_non_overlapping_empty_proof:
  ∀s. s.vs_allocas = FEMPTY ⇒ allocas_non_overlapping s
Proof
  rw[allocas_non_overlapping_def, FLOOKUP_DEF]
QED

Theorem allocas_non_overlapping_step_inst_proof:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    allocas_non_overlapping s ⇒
    allocas_non_overlapping s'
Proof
  cheat
QED

Theorem allocas_non_overlapping_exec_block_proof:
  ∀fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ∧
    allocas_non_overlapping s ⇒
    allocas_non_overlapping s'
Proof
  cheat
QED

Theorem mload_mstore_disjoint_proof:
  ∀off1 off2 val s.
    regions_disjoint (off1, 32) (off2, 32) ⇒
    mload off2 (mstore off1 val s) = mload off2 s
Proof
  cheat
QED

Theorem mload_mstore8_disjoint_proof:
  ∀off1 off2 val s.
    regions_disjoint (off1, 1) (off2, 32) ⇒
    mload off2 (mstore8 off1 val s) = mload off2 s
Proof
  cheat
QED
