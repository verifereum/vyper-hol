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
  list rich_list words byte arithmetic finite_map divides
  venomState venomMemDefs venomExecSemantics
Libs
  wordsLib dep_rewrite

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

Theorem word_bytes_roundtrip_proof:
  ∀ (bytes : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bytes = dimindex(:α) DIV 8 ⇒
    word_to_bytes (word_of_bytes T (0w : α word) bytes) T = bytes
Proof
  rw[LIST_EQ_REWRITE, LENGTH_word_to_bytes]
  >> fs[]
  >> rw[word_to_bytes_def]
  >> simp[EL_word_to_bytes_aux]
  >> simp[get_byte_word_of_bytes_be]
  >> DEP_REWRITE_TAC[first_byte_at_0w]
  >> rw[DIV_LE_X, dimindex_lt_dimword]
QED

Theorem word_of_bytes_be_inj_proof:
  ∀ (bs1 : byte list) (bs2 : byte list).
    8 ≤ dimindex(:α) ∧ divides 8 (dimindex(:α)) ∧
    LENGTH bs1 = dimindex(:α) DIV 8 ∧
    LENGTH bs2 = dimindex(:α) DIV 8 ∧
    word_of_bytes T (0w : α word) bs1 = word_of_bytes T (0w : α word) bs2 ⇒
    bs1 = bs2
Proof
  rw[] >>
  `word_to_bytes (word_of_bytes T 0w bs1 : α word) T =
   word_to_bytes (word_of_bytes T 0w bs2 : α word) T` by simp[] >>
  metis_tac[word_bytes_roundtrip_proof]
QED

Theorem word_to_bytes_be_w2w_proof:
  ∀ (w : α word).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β)
    ⇒
    word_to_bytes (w2w w : β word) T =
    PAD_LEFT 0w (dimindex(:β) DIV 8) (word_to_bytes w T)
Proof
  rw[PAD_LEFT, GSYM REPLICATE_GENLIST] >>
  simp[word_to_bytes_be_def, word_to_bytes_def] >>
  simp[LIST_EQ_REWRITE, LENGTH_word_to_bytes_aux] >>
  rw[]
  >- (
    irule $ GSYM SUB_ADD >>
    gvs[DIV_LE_X, LEFT_ADD_DISTRIB, DIVIDES_DIV] ) >>
  simp[EL_word_to_bytes_aux, EL_APPEND,
       LENGTH_word_to_bytes_aux, EL_REPLICATE] >>
  IF_CASES_TAC >- (
    simp[word_eq_0, w2w, word_lsr_def, get_byte_def, byte_index_def] >>
    simp[fcpTheory.FCP_BETA] >>
    gen_tac >> strip_tac >>
    qmatch_goalsub_abbrev_tac`x MOD db MOD b8` >>
    disj2_tac >>
    qmatch_goalsub_abbrev_tac`w2w w ' ii` >>
    `b8 < dimindex(:'b)` by gvs[Abbr`b8`] >>
    `dimindex(:'b) < db` by gvs[dimindex_lt_dimword,Abbr`db`] >>
    `x < db` by gvs[] >> gvs[] >>
    gvs[LEFT_SUB_DISTRIB] >>
    `8 * b8 = dimindex(:'b)` by gvs[Abbr`b8`, DIVIDES_DIV] >>
    gvs[] >>
    `8 * (dimindex(:'a) DIV 8) ≤ dimindex(:'b)` by simp[DIVIDES_DIV] >>
    drule_at(Pos(el 2))DIV_SUB >>
    impl_tac >- rw[] >> simp[DIVIDES_DIV] >>
    strip_tac >> gvs[X_LT_DIV] >>
    `ii < dimindex(:'b)` by gvs[Abbr`ii`] >>
    simp[w2w] >> gvs[Abbr`ii`] ) >>
  `8 * (dimindex(:'a) DIV 8) ≤ dimindex(:'b)` by simp[DIVIDES_DIV] >>
  drule_at(Pos(el 2))DIV_SUB >>
  impl_tac >- rw[] >> simp[DIVIDES_DIV] >>
  disch_then (strip_assume_tac o SYM) >> gvs[X_LT_DIV] >>
  simp[get_byte_def] >>
  qmatch_goalsub_abbrev_tac`ba DIV 8` >>
  qmatch_asmsub_abbrev_tac`db - da = _`>>
  simp[byte_index_def] >>
  assume_tac(INST_TYPE[alpha|->beta]dimindex_lt_dimword) >>
  gvs[] >>
  `x < db` by gvs[Abbr`db`,X_LT_DIV] >> gvs[] >>
  qmatch_goalsub_abbrev_tac`xxx MOD dw MOD da` >>
  `da < dimindex(:'a)` by simp[Abbr`da`] >>
  `dimindex(:'a) < dimword(:'a)` by simp[dimindex_lt_dimword] >> gvs[] >>
  `xxx < dw` by gvs[Abbr`xxx`] >> gvs[] >>
  `xxx < da` by gvs[Abbr`xxx`,Abbr`da`,X_LT_DIV] >> gvs[] >>
  `db - (x + 1) = da - (xxx + 1)` by (
    gvs[Abbr`xxx`] >>
    rewrite_tac[SUB_PLUS] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    qspecl_then[`x`,`ba DIV 8`]mp_tac SUB_SUB >>
    impl_tac >- simp[DIV_LE_X] >> simp[] >> disch_then kall_tac >>
    AP_THM_TAC >> AP_TERM_TAC >>
    `da <= db` suffices_by gvs[] >>
    unabbrev_all_tac >>
    irule DIV_LE_MONOTONE >> rw[] ) >>
  gvs[] >>
  simp[GSYM WORD_EQ, word_bit_def, w2w, word_lsr_def, fcpTheory.FCP_BETA]
QED

Theorem w2w_word_of_bytes_be_pad_left_proof:
  ∀ (l : byte list).
    8 ≤ dimindex(:α) ∧ 8 ≤ dimindex(:β) ∧
    divides 8 (dimindex(:α)) ∧ divides 8 (dimindex(:β)) ∧
    dimindex(:α) ≤ dimindex(:β) ∧
    LENGTH l = dimindex(:α) DIV 8
    ⇒
    w2w (word_of_bytes_be l : α word) =
    (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word)
Proof
  rw[] >>
  `word_to_bytes (w2w (word_of_bytes_be l : α word) : β word) T =
   word_to_bytes (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word) T`
    suffices_by metis_tac[word_of_bytes_word_to_bytes] >>
  simp[GSYM word_to_bytes_be_def, GSYM word_of_bytes_be_def] >>
  DEP_REWRITE_TAC[word_to_bytes_be_w2w_proof] >> simp[] >>
  simp[word_to_bytes_be_def, word_of_bytes_be_def] >>
  DEP_REWRITE_TAC[word_bytes_roundtrip_proof] >>
  simp[bitstringTheory.length_pad_left, DIV_LE_MONOTONE] >>
  rw[] >> gvs[NOT_LESS]
  >- (qspec_then`8`imp_res_tac DIV_LE_MONOTONE >> gvs[]) >>
  DEP_REWRITE_TAC[word_to_bytes_be_w2w_proof] >> simp[] >>
  DEP_REWRITE_TAC[word_bytes_roundtrip_proof] >> simp[]
QED
