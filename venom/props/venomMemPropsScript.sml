(*
 * Venom Memory Properties (public interface)
 *
 * Stable, generally useful properties of memory operations and alloca layout.
 * Longer memory proof engineering lives in venomMemProofs; this theory owns the
 * public theorem names below and derives them from the workhorse proofs.
 *
 * TOP-LEVEL:
 *   allocas_non_overlapping_empty     — base case (no allocas)
 *   alloca_inv_empty                  — alloca_inv for empty allocas
 *   alloca_inv_step_inst              — alloca_inv preserved by step_inst
 *   alloca_inv_exec_block             — alloca_inv preserved by exec_block
 *   alloca_inv_run_block              — alloca_inv preserved by run_block
 *   alloca_inv_run_blocks             — alloca_inv preserved by run_blocks
 *   alloca_inv_run_function           — alloca_inv preserved by run_function
 *   allocas_non_overlapping_step_inst — preserved by step_inst (needs alloca_inv)
 *   allocas_non_overlapping_run_block — preserved by run_block (needs alloca_inv)
 *   allocas_non_overlapping_exec_block — preserved by exec_block
 *   mload_mstore_disjoint             — disjoint 32-byte write/read independence
 *   mload_mstore8_disjoint            — disjoint 1-byte write / 32-byte read
 *   mload_mstore_same                 — same-offset 32-byte write/read
 *   word_bytes_roundtrip              — byte-list to word and back
 *   word_to_bytes_be_w2w              — zero extension pads big-endian bytes
 *   word_of_bytes_be_inj              — big-endian byte-to-word injectivity
 *   w2w_word_of_bytes_be_pad_left     — corollary for word_of_bytes_be + w2w
 *)

Theory venomMemProps
Ancestors
  venomMemDefs venomMemProofs venomExecSemantics divides
Libs
  wordsLib

Theorem dimindex_256[simp]:
  dimindex (:256) = 256
Proof
  EVAL_TAC
QED

Theorem allocas_non_overlapping_empty:
  ∀s. s.vs_allocas = FEMPTY ⇒ allocas_non_overlapping s
Proof
  metis_tac[venomMemProofsTheory.allocas_non_overlapping_empty_proof]
QED

Theorem alloca_inv_empty:
  ∀s. s.vs_allocas = FEMPTY ⇒ alloca_inv s
Proof
  metis_tac[venomMemProofsTheory.alloca_inv_empty_proof]
QED

Theorem alloca_inv_step_inst:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof
  metis_tac[venomMemProofsTheory.alloca_inv_step_inst_proof]
QED

Theorem alloca_inv_run_block:
  ∀fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof
  metis_tac[venomMemProofsTheory.alloca_inv_run_block_proof]
QED

Theorem alloca_inv_exec_block:
  ∀fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof
  metis_tac[venomMemProofsTheory.alloca_inv_exec_block_proof]
QED

Theorem alloca_inv_run_blocks:
  ∀fuel ctx fn s s'.
    run_blocks fuel ctx fn s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof
  metis_tac[venomMemProofsTheory.alloca_inv_run_blocks_proof]
QED

Theorem alloca_inv_run_function:
  ∀fuel ctx fn s s'.
    run_function fuel ctx fn s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof
  metis_tac[venomMemProofsTheory.alloca_inv_run_function_proof]
QED

Theorem step_inst_base_preserves_allocas:
  ∀inst s s'.
    (step_inst_base inst s = OK s' ∨
     step_inst_base inst s = Halt s' ∨
     (∃a. step_inst_base inst s = Abort a s') ∨
     (∃v. step_inst_base inst s = IntRet v s')) ∧
    inst.inst_opcode ≠ INVOKE ∧
    inst.inst_opcode ≠ ALLOCA ⇒
    s'.vs_allocas = s.vs_allocas
Proof
  metis_tac[venomMemProofsTheory.step_inst_base_preserves_allocas]
QED

Theorem allocas_non_overlapping_step_inst:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    alloca_inv s ⇒
    allocas_non_overlapping s'
Proof
  metis_tac[venomMemProofsTheory.allocas_non_overlapping_step_inst_proof]
QED

Theorem allocas_non_overlapping_run_block:
  ∀fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    allocas_non_overlapping s'
Proof
  metis_tac[venomMemProofsTheory.allocas_non_overlapping_run_block_proof]
QED

Theorem allocas_non_overlapping_exec_block:
  ∀fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    allocas_non_overlapping s'
Proof
  metis_tac[venomMemProofsTheory.allocas_non_overlapping_exec_block_proof]
QED

Theorem mload_mstore_disjoint:
  ∀off1 off2 val s.
    regions_disjoint (off1, 32) (off2, 32) ⇒
    mload off2 (mstore off1 val s) = mload off2 s
Proof
  metis_tac[venomMemProofsTheory.mload_mstore_disjoint_proof]
QED

Theorem mload_mstore8_disjoint:
  ∀off1 off2 val s.
    regions_disjoint (off1, 1) (off2, 32) ⇒
    mload off2 (mstore8 off1 val s) = mload off2 s
Proof
  metis_tac[venomMemProofsTheory.mload_mstore8_disjoint_proof]
QED

Theorem mload_mstore_same:
  ∀off val s.
    mload off (mstore off val s) = val
Proof
  metis_tac[venomMemProofsTheory.mload_mstore_same_proof]
QED

Theorem word_bytes_roundtrip:
  ∀ (bytes : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bytes = dimindex(:α) DIV 8 ⇒
    word_to_bytes (word_of_bytes T (0w : α word) bytes) T = bytes
Proof
  metis_tac[venomMemProofsTheory.word_bytes_roundtrip_proof]
QED

Theorem word_bytes_roundtrip_256:
  ∀bytes.
    LENGTH bytes = 32 ⇒
    word_to_bytes (word_of_bytes T (0w : bytes32) bytes) T = bytes
Proof
  rpt strip_tac >>
  irule word_bytes_roundtrip >>
  simp[divides_def]
QED

Theorem word_to_bytes_be_w2w:
  ∀ (w : α word).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β)
    ⇒
    word_to_bytes (w2w w : β word) T =
    PAD_LEFT 0w (dimindex(:β) DIV 8) (word_to_bytes w T)
Proof
  metis_tac[venomMemProofsTheory.word_to_bytes_be_w2w_proof]
QED

Theorem word_of_bytes_be_inj:
  ∀ (bs1 : byte list) (bs2 : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bs1 = dimindex(:α) DIV 8 ∧
    LENGTH bs2 = dimindex(:α) DIV 8 ∧
    word_of_bytes T (0w : α word) bs1 = word_of_bytes T (0w : α word) bs2 ⇒
    bs1 = bs2
Proof
  metis_tac[venomMemProofsTheory.word_of_bytes_be_inj_proof]
QED

Theorem w2w_word_of_bytes_be_pad_left:
  ∀ (l : byte list).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β) ∧
    LENGTH l = dimindex(:α) DIV 8
    ⇒
    w2w (word_of_bytes_be l : α word) =
    (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word)
Proof
  metis_tac[venomMemProofsTheory.w2w_word_of_bytes_be_pad_left_proof]
QED
