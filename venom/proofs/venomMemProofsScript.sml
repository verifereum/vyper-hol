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
  list rich_list words byte arithmetic finite_map
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
  simp[mload_def, mstore_def, regions_disjoint_def] >>
  rpt gen_tac >>
  simp[DROP_APPEND, LENGTH_TAKE_EQ] >>
  strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[NOT_GREATER]
  >- (
    gvs[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, LENGTH_REPLICATE,
        DROP_LENGTH_TOO_LONG] )
  >- (
    Cases_on`off2 ≤ LENGTH s.vs_memory` >>
    gvs[TAKE_APPEND, DROP_LENGTH_TOO_LONG, DROP_DROP_T,
        LENGTH_REPLICATE, TAKE_LENGTH_TOO_LONG] >>
    `2 * off1 + 32 - 2 * off2 = 0` by (rewrite_tac[SUB_EQ_0] \\ decide_tac) >>
    pop_assum SUBST_ALL_TAC >> gvs[] )
  >- (
    Cases_on`off1 + 32 ≤ LENGTH s.vs_memory` >>
    gvs[TAKE_APPEND, DROP_LENGTH_TOO_LONG, DROP_DROP_T,
        LENGTH_REPLICATE, TAKE_LENGTH_TOO_LONG] >>
    `off2 - off1 = 0 /\ off2 + 32 - off1 = 0 /\ 2 * off2 - 2 * off1 = 0` by
      (rewrite_tac[SUB_EQ_0] \\ decide_tac) >>
    ntac 3 (pop_assum SUBST_ALL_TAC) >> gvs[NOT_LESS_EQUAL] >>
    AP_TERM_TAC >> simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ] >>
    simp[EL_TAKE, EL_APPEND, LENGTH_TAKE_EQ, EL_DROP, EL_REPLICATE] >>
    rw[] >> gvs[] )
  >- (
    AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE, EL_TAKE, DROP_DROP_T] >>
    qx_gen_tac `x` \\ strip_tac >>
    `off2 - off1 = 0` by decide_tac >>
    pop_assum SUBST_ALL_TAC >> simp[] >>
    once_rewrite_tac[EL_APPEND] >>
    rewrite_tac[LENGTH_APPEND, LENGTH_DROP, LENGTH_TAKE_EQ] >>
    `off1 ≤ LENGTH s.vs_memory` by decide_tac >>
    pop_assum (SUBST_ALL_TAC o EQT_INTRO) >>
    rewrite_tac[LENGTH_word_to_bytes, did8] >>
    reverse IF_CASES_TAC
    >- (`F` suffices_by rw[] >> decide_tac) >>
    simp[EL_APPEND, EL_DROP, EL_TAKE])
QED

Theorem mload_mstore8_disjoint_proof:
  ∀off1 off2 val s.
    regions_disjoint (off1, 1) (off2, 32) ⇒
    mload off2 (mstore8 off1 val s) = mload off2 s
Proof
  simp[mload_def, mstore8_def, regions_disjoint_def] >>
  rpt gen_tac >>
  simp[DROP_APPEND, LENGTH_TAKE_EQ] >>
  strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[NOT_GREATER]
  >- (
    gvs[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, LENGTH_REPLICATE,
        DROP_LENGTH_TOO_LONG] )
  >- (
    Cases_on`off2 ≤ LENGTH s.vs_memory` >>
    gvs[TAKE_APPEND, DROP_LENGTH_TOO_LONG, DROP_DROP_T,
        LENGTH_REPLICATE, TAKE_LENGTH_TOO_LONG] >>
    `off1 - off2 = 0` by (rewrite_tac[SUB_EQ_0] \\ decide_tac) >>
    pop_assum SUBST_ALL_TAC >> gvs[] )
  >- (
    Cases_on`off1 + 32 ≤ LENGTH s.vs_memory` >>
    gvs[TAKE_APPEND, DROP_LENGTH_TOO_LONG, DROP_DROP_T,
        LENGTH_REPLICATE, TAKE_LENGTH_TOO_LONG] >>
    `off2 - off1 = 0 /\ off2 + 32 - off1 = 0 /\
     2 * off2 + 31 - 2 * off1 = 0` by
      (rewrite_tac[SUB_EQ_0] \\ decide_tac) >>
    ntac 3 (pop_assum SUBST_ALL_TAC) >> gvs[NOT_LESS_EQUAL] >>
    AP_TERM_TAC >> simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ] >>
    simp[EL_TAKE, EL_APPEND, LENGTH_TAKE_EQ, EL_DROP, EL_REPLICATE] >>
    rw[] >> gvs[] )
  >- (
    AP_TERM_TAC >>
    simp[LIST_EQ_REWRITE, EL_TAKE, DROP_DROP_T] >>
    qx_gen_tac `x` \\ strip_tac >>
    `off2 - off1 = 0` by decide_tac >>
    pop_assum SUBST_ALL_TAC >> simp[] >>
    once_rewrite_tac[EL_APPEND] >>
    rewrite_tac[LENGTH_APPEND, LENGTH_DROP, LENGTH_TAKE_EQ] >>
    `off1 ≤ LENGTH s.vs_memory` by decide_tac >>
    pop_assum (SUBST_ALL_TAC o EQT_INTRO) >>
    rewrite_tac[LENGTH_word_to_bytes, did8] >>
    reverse IF_CASES_TAC
    >- (`F` suffices_by rw[] >> decide_tac) >>
    simp[EL_APPEND, EL_DROP, EL_TAKE])
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
