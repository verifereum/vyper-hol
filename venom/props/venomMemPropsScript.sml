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
  arithmetic divides rich_list list byte words
  venomMemDefs venomMemProofs venomExecSemantics
Libs
  wordsLib dep_rewrite

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
Proof
  rw[LIST_EQ_REWRITE, LENGTH_word_to_bytes]
  >> fs[]
  >> rw[word_to_bytes_def]
  >> simp[EL_word_to_bytes_aux]
  >> simp[get_byte_word_of_bytes_be]
  >> DEP_REWRITE_TAC[first_byte_at_0w]
  >> rw[DIV_LE_X, dimindex_lt_dimword]
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

Theorem word_of_bytes_be_inj:
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
  metis_tac[word_bytes_roundtrip]
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
Proof
  rw[] >>
  `word_to_bytes (w2w (word_of_bytes_be l : α word) : β word) T =
   word_to_bytes (word_of_bytes_be (PAD_LEFT 0w (dimindex(:β) DIV 8) l) : β word) T`
    suffices_by metis_tac[word_of_bytes_word_to_bytes] >>
  simp[GSYM word_to_bytes_be_def, GSYM word_of_bytes_be_def] >>
  DEP_REWRITE_TAC[word_to_bytes_be_w2w] >> simp[] >>
  simp[word_to_bytes_be_def, word_of_bytes_be_def] >>
  DEP_REWRITE_TAC[word_bytes_roundtrip] >>
  simp[bitstringTheory.length_pad_left, DIV_LE_MONOTONE] >>
  rw[] >> gvs[NOT_LESS]
  >- (qspec_then`8`imp_res_tac DIV_LE_MONOTONE >> gvs[]) >>
  DEP_REWRITE_TAC[word_to_bytes_be_w2w] >> simp[] >>
  DEP_REWRITE_TAC[word_bytes_roundtrip] >> simp[]
QED
