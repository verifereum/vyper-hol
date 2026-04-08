(*
 * Venom Memory Properties
 *
 * General properties of memory operations and alloca layout.
 * Re-exports proven properties from venomMemProofs via ACCEPT_TAC.
 * Definitions are in venomMemDefs.
 *
 * TOP-LEVEL:
 *   allocas_non_overlapping_empty     — base case (no allocas)
 *   alloca_inv_empty                   — alloca_inv for empty allocas
 *   alloca_inv_step_inst               — alloca_inv preserved by step_inst
 *   alloca_inv_exec_block              — alloca_inv preserved by exec_block
 *   alloca_inv_run_block               — alloca_inv preserved by run_block
 *   alloca_inv_run_blocks              — alloca_inv preserved by run_blocks
 *   alloca_inv_run_function            — alloca_inv preserved by run_function
 *   allocas_non_overlapping_step_inst  — preserved by step_inst (needs alloca_inv)
 *   allocas_non_overlapping_run_block  — preserved by run_block (needs alloca_inv)
 *   allocas_non_overlapping_exec_block — preserved by exec_block
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

Theorem alloca_inv_empty:
  ∀s. s.vs_allocas = FEMPTY ⇒ alloca_inv s
Proof ACCEPT_TAC venomMemProofsTheory.alloca_inv_empty_proof
QED

Theorem alloca_inv_step_inst:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof ACCEPT_TAC venomMemProofsTheory.alloca_inv_step_inst_proof
QED

Theorem alloca_inv_run_block:
  ∀fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof ACCEPT_TAC venomMemProofsTheory.alloca_inv_run_block_proof
QED

Theorem alloca_inv_exec_block:
  ∀fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof ACCEPT_TAC venomMemProofsTheory.alloca_inv_exec_block_proof
QED

Theorem alloca_inv_run_blocks:
  ∀fuel ctx fn s s'.
    run_blocks fuel ctx fn s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof ACCEPT_TAC venomMemProofsTheory.alloca_inv_run_blocks_proof
QED

Theorem alloca_inv_run_function:
  ∀fuel ctx fn s s'.
    run_function fuel ctx fn s = OK s' ∧
    alloca_inv s ⇒
    alloca_inv s'
Proof ACCEPT_TAC venomMemProofsTheory.alloca_inv_run_function_proof
QED

Theorem allocas_non_overlapping_step_inst:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    alloca_inv s ⇒
    allocas_non_overlapping s'
Proof ACCEPT_TAC venomMemProofsTheory.allocas_non_overlapping_step_inst_proof
QED

Theorem allocas_non_overlapping_run_block:
  ∀fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    allocas_non_overlapping s'
Proof ACCEPT_TAC venomMemProofsTheory.allocas_non_overlapping_run_block_proof
QED

Theorem allocas_non_overlapping_exec_block:
  ∀fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ∧
    alloca_inv s ⇒
    allocas_non_overlapping s'
Proof ACCEPT_TAC venomMemProofsTheory.allocas_non_overlapping_exec_block_proof
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

Theorem mload_mstore_same:
  ∀off val s.
    mload off (mstore off val s) = val
Proof
  ACCEPT_TAC venomMemProofsTheory.mload_mstore_same_proof
QED

(* Key property: converting bytes to a word and back is identity.
   Generalised from mmCopyEquivScript for wider reuse. *)
Theorem word_bytes_roundtrip:
  ∀ (bytes : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bytes = dimindex(:α) DIV 8 ⇒
    word_to_bytes (word_of_bytes T (0w : α word) bytes) T = bytes
Proof ACCEPT_TAC venomMemProofsTheory.word_bytes_roundtrip_proof
QED

(* word_of_bytes T 0w is injective on 32-byte lists *)
(* TODO: upstream a more general lemma to byteTheory *)
(* Big-endian word_to_bytes of w2w is PAD_LEFT of word_to_bytes.
   Zero-extending a word pads with zero bytes on the left in big-endian. *)
Theorem word_to_bytes_be_w2w:
  ∀ (w : α word).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β)
    ⇒
    word_to_bytes (w2w w : β word) T =
    PAD_LEFT 0w (dimindex(:β) DIV 8) (word_to_bytes w T)
Proof ACCEPT_TAC word_to_bytes_be_w2w_proof
QED

Theorem word_of_bytes_be_inj:
  ∀ (bs1 : byte list) (bs2 : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bs1 = dimindex(:α) DIV 8 ∧
    LENGTH bs2 = dimindex(:α) DIV 8 ∧
    word_of_bytes T (0w : α word) bs1 = word_of_bytes T (0w : α word) bs2 ⇒
    bs1 = bs2
Proof ACCEPT_TAC venomMemProofsTheory.word_of_bytes_be_inj_proof
QED

(* Corollary: w2w of word_of_bytes_be = word_of_bytes_be of PAD_LEFT *)
Theorem w2w_word_of_bytes_be_pad_left:
  ∀ (l : byte list).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β) ∧
    LENGTH l = dimindex(:α) DIV 8
    ⇒
    w2w (word_of_bytes_be l : α word) =
    (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word)
Proof ACCEPT_TAC w2w_word_of_bytes_be_pad_left_proof
QED
