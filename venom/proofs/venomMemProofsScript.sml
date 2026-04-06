(*
 * Venom Memory Proofs
 *
 * TOP-LEVEL:
 *   allocas_non_overlapping_empty_proof     — base case
 *   allocas_non_overlapping_step_inst_proof — preserved by step_inst
 *   allocas_non_overlapping_run_block_proof — preserved by run_block
 *   mload_mstore_disjoint_proof             — 32-byte write/read independence
 *   mload_mstore8_disjoint_proof            — 1-byte write / 32-byte read
 *)

Theory venomMemProofs
Ancestors
  list rich_list words byte finite_map
  venomState venomMemDefs venomExecSemantics
Libs
  wordsLib

Theorem did8[local] = EVAL``dimindex(:256) DIV 8``

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

Theorem allocas_non_overlapping_run_block_proof:
  ∀fuel ctx bb s s'.
    run_block fuel ctx bb s = OK s' ∧
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

Theorem mload_mstore_same_proof:
  ∀off val s.
    mload off (mstore off val s) = val
Proof
  simp[mload_def, mstore_def] >>
  rpt gen_tac >>
  rewrite_tac[TAKE_APPEND] >>
  rewrite_tac[DROP_APPEND, DROP_TAKE_EQ_NIL] >>
  simp_tac (std_ss ++ listSimps.LIST_ss)
    [LENGTH_word_to_bytes, LENGTH_TAKE_EQ] >>
  IF_CASES_TAC >- (
    simp_tac (std_ss ++ listSimps.LIST_ss)
      [did8,
       iterateTheory.ADD_SUBR2, TAKE_APPEND,
       LENGTH_word_to_bytes] >>
    simp[LENGTH_word_to_bytes, TAKE_LENGTH_TOO_LONG]) >>
  IF_CASES_TAC >- (
    simp_tac (std_ss ++ listSimps.LIST_ss)
      [LENGTH_REPLICATE, did8, DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
    simp[iterateTheory.ADD_SUBR2, TAKE_APPEND,
         TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG] ) >>
  fs[]
QED
