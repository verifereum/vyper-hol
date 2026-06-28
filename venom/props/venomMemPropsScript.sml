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
 *   step_inst_base_preserves_allocas — step_inst_base preserves alloca map
 *   step_inst_base_preserves_alloca_next — step_inst_base preserves next alloca offset
 *   step_inst_base_preserves_alloca_state — step_inst_base preserves alloca map+next
 *   step_inst_preserves_alloca_state — step_inst preserves alloca map+next
 *   step_inst_non_alloca_preserves_allocas — non-ALLOCA step_inst preserves alloca map
 *   allocas_non_overlapping_step_inst — preserved by step_inst (needs alloca_inv)
 *   allocas_non_overlapping_run_block — preserved by run_block (needs alloca_inv)
 *   allocas_non_overlapping_exec_block — preserved by exec_block
 *   LENGTH_write_memory_with_expansion — exact length after memory write
 *   LENGTH_mstore_eq                  — exact length after MSTORE
 *   LENGTH_mstore8_eq                 — exact length after MSTORE8
 *   write_memory_with_expansion_nondecreasing — memory write does not shrink
 *   mstore_memory_nondecreasing       — MSTORE does not shrink memory
 *   mstore8_memory_nondecreasing      — MSTORE8 does not shrink memory
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
  venomMemDefs venomMemProofs venomExecSemantics venomState venomInst venomEffects divides
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

Theorem step_inst_base_preserves_alloca_next:
  ∀inst s s'.
    (step_inst_base inst s = OK s' ∨
     step_inst_base inst s = Halt s' ∨
     (∃a. step_inst_base inst s = Abort a s') ∨
     (∃v. step_inst_base inst s = IntRet v s')) ∧
    inst.inst_opcode ≠ INVOKE ∧
    inst.inst_opcode ≠ ALLOCA ⇒
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  metis_tac[venomMemProofsTheory.step_inst_base_preserves_alloca_next]
QED

Theorem step_inst_base_preserves_alloca_state:
  ∀inst s s'.
    step_inst_base inst s = OK s' ∧
    ¬is_terminator inst.inst_opcode ∧
    ¬is_alloca_op inst.inst_opcode ⇒
    s'.vs_allocas = s.vs_allocas ∧
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode ≠ INVOKE` by (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
    ASM_REWRITE_TAC[step_inst_base_def] >> simp[]) >>
  `inst.inst_opcode ≠ ALLOCA` by (CCONTR_TAC >> gvs[is_alloca_op_def]) >>
  metis_tac[step_inst_base_preserves_allocas,
            step_inst_base_preserves_alloca_next]
QED

Theorem step_inst_preserves_alloca_state:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    ¬is_terminator inst.inst_opcode ∧
    ¬is_alloca_op inst.inst_opcode ∧
    ¬is_ext_call_op inst.inst_opcode ∧
    inst.inst_opcode ≠ INVOKE ⇒
    s'.vs_allocas = s.vs_allocas ∧
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_preserves_alloca_state]
QED

Theorem step_inst_non_alloca_preserves_allocas:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    ¬is_alloca_op inst.inst_opcode ∧
    inst.inst_opcode ≠ INVOKE ⇒
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  `inst.inst_opcode ≠ ALLOCA` by (Cases_on `inst.inst_opcode` >> fs[is_alloca_op_def]) >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  metis_tac[step_inst_base_preserves_allocas]
QED

Theorem step_inst_non_alloca_non_term_preserves_allocas:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    ¬is_alloca_op inst.inst_opcode ∧
    ¬is_terminator inst.inst_opcode ∧
    inst.inst_opcode ≠ INVOKE ⇒
    s'.vs_allocas = s.vs_allocas
Proof
  metis_tac[step_inst_non_alloca_preserves_allocas]
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

Theorem LENGTH_write_memory_with_expansion:
  ∀offset bytes s.
    LENGTH (write_memory_with_expansion offset bytes s).vs_memory =
    MAX (LENGTH s.vs_memory) (offset + LENGTH bytes)
Proof
  rw[write_memory_with_expansion_def, LET_THM, arithmeticTheory.MAX_DEF]
QED

Theorem LENGTH_mstore_eq:
  ∀off (v:bytes32) s.
    LENGTH (mstore off v s).vs_memory = MAX (LENGTH s.vs_memory) (off + 32)
Proof
  rw[mstore_def, LET_THM, byteTheory.LENGTH_word_to_bytes,
     arithmeticTheory.MAX_DEF]
QED

Theorem LENGTH_mstore8_eq:
  ∀off (v:bytes32) s.
    LENGTH (mstore8 off v s).vs_memory = MAX (LENGTH s.vs_memory) (off + 1)
Proof
  rw[mstore8_def, LET_THM, arithmeticTheory.MAX_DEF]
QED

Theorem write_memory_with_expansion_nondecreasing:
  ∀offset bytes s.
    LENGTH s.vs_memory ≤ LENGTH (write_memory_with_expansion offset bytes s).vs_memory
Proof
  rw[LENGTH_write_memory_with_expansion, arithmeticTheory.MAX_DEF]
QED

Theorem mstore_memory_nondecreasing:
  ∀offset (value:bytes32) s.
    LENGTH s.vs_memory ≤ LENGTH (mstore offset value s).vs_memory
Proof
  rw[LENGTH_mstore_eq, arithmeticTheory.MAX_DEF]
QED

Theorem mstore8_memory_nondecreasing:
  ∀offset (value:bytes32) s.
    LENGTH s.vs_memory ≤ LENGTH (mstore8 offset value s).vs_memory
Proof
  rw[LENGTH_mstore8_eq, arithmeticTheory.MAX_DEF]
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
