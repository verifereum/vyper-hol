(* TOP-LEVEL: val_in_memory_prim_enc, val_in_memory_flag_enc.
   Scalar layout facts shared by creation encoding and the legacy ABI proofs.
   This theory has no dependency on admitted recursive encoder correctness. *)
Theory abiValueEncoding
Ancestors
  list rich_list words byte divides bitstring integer_word
  valueEncoding valueEncodingProps compileEnv vyperABI vyperTyping vyperValue contractABI
  venomMemProps
Libs
  dep_rewrite wordsLib

(* ===== Scalar source/ABI layouts ===== *)

Theorem val_in_memory_prim_enc:
  ∀ bt v off mem av.
    val_in_memory (BaseTV bt) v off mem ∧
    off + 32 ≤ LENGTH mem ∧
    is_word_type (BaseT bt) ∧
    value_has_type (BaseTV bt) v ∧
    vyper_to_abi_base bt v = SOME av
    ⇒
    mem_bytes_at off 32 mem = enc (vyper_base_to_abi_type bt) av
Proof
  (* Case split on bt and v. For each case:
     1. val_in_memory supplies the type-directed word representation of v
     2. Unfold mem_word_at: word_of_bytes T 0w (mem_bytes_at off 32 mem) = w
     3. Apply word_bytes_roundtrip: word_to_bytes w T = mem_bytes_at off 32 mem
     4. Unfold enc/enc_number: enc at av = word_to_bytes w' T
     5. Connect that typed word representation to the ABI value *)
  Cases_on `bt` >> Cases_on `v` >>
  simp[val_in_memory_def, is_word_type_def, vyper_to_abi_base_def,
       vyper_base_to_abi_type_def, enc_def, enc_number_def,
       mem_word_at_def, mem_bytes_at_def, val_to_w256_def] >>
  rw[] >> rw[enc_def] >> gvs[value_has_type_def, TAKE_APPEND] >>
  gvs[typed_val_to_w256_def] >>
  full_simp_tac bool_ss [GSYM arithmeticTheory.SUB_EQ_0] >> gvs[] >>
  TRY (
    `n2w (Num i): bytes32 = i2w i` by (
      rw[integer_wordTheory.i2w_def] >>
      Cases_on`i=0` \\ gvs[] >>
      `F` suffices_by rw[] >>
      intLib.COOPER_TAC) >> gvs[]) >>
  TRY (
    qpat_x_assum`word_of_bytes _ _ _ = _`(SUBST_ALL_TAC o SYM) >>
    irule $ GSYM word_bytes_roundtrip >>
    simp[dividesTheory.divides_def] >> NO_TAC)
  >- (
    Cases_on`b` \\ gvs[value_has_type_def, is_word_type_def] >>
    gvs[PAD_RIGHT, REPLICATE_GENLIST, TAKE_LENGTH_TOO_LONG,
        byteTheory.word_of_bytes_be_def] >>
    drule_at Any word_of_bytes_be_inj >>
    simp[dividesTheory.divides_def] ) >>
  gvs[GSYM wordsTheory.w2w_def] >>
  qmatch_goalsub_abbrev_tac`word_to_bytes www` >>
  qmatch_asmsub_abbrev_tac`word_of_bytes _ _ _ = ww1` >>
  `www = ww1` by (
    rw[Abbr`www`] >> gvs[byteTheory.word_of_bytes_be_def] >>
    drule_at Any word_of_bytes_be_inj >>
    rw[bitstringTheory.length_pad_left] >>
    simp[GSYM byteTheory.word_of_bytes_be_def] >>
    DEP_REWRITE_TAC[w2w_word_of_bytes_be_pad_left] >>
    simp[dividesTheory.divides_def] ) >>
  gvs[Abbr`www`] >>
  irule $ GSYM word_bytes_roundtrip >>
  rw[dividesTheory.divides_def]
QED

Theorem val_in_memory_flag_enc:
  ∀ m k off mem.
    val_in_memory (FlagTV m) (FlagV k) off mem ∧
    off + 32 ≤ LENGTH mem
    ⇒
    mem_bytes_at off 32 mem = enc (Uint 256) (NumV k)
Proof
  rw[val_in_memory_def, enc_def, enc_number_def,
     mem_word_at_def, mem_bytes_at_def, val_to_w256_def] >>
  qpat_x_assum`_ = n2w _`(SUBST_ALL_TAC o SYM) >>
  irule EQ_SYM >>
  irule word_bytes_roundtrip >>
  simp[dividesTheory.divides_def]
QED

Theorem evaluate_type_base_result:
  evaluate_type tenv (BaseT bt) = SOME tv ⇒ tv = BaseTV bt
Proof
  Cases_on `bt` >> TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  simp[Once evaluate_type_def, CaseEq "bool", LET_THM] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_base_memory:
  evaluate_type tenv (BaseT bt) = SOME tv ∧
  is_word_type (BaseT bt) ∧ value_has_type tv v ∧
  val_in_memory tv v off mem ∧ off + 32 ≤ LENGTH mem ∧
  vyper_to_abi tenv (BaseT bt) v = SOME av ⇒
  mem_bytes_at off 32 mem = enc (vyper_to_abi_type tenv (BaseT bt)) av
Proof
  rpt strip_tac >> drule evaluate_type_base_result >> strip_tac >>
  gvs[] >> drule_all val_in_memory_prim_enc >> simp[]
QED

Theorem abi_word_type_size:
  is_word_type ty ∧ evaluate_type tenv ty = SOME tv ⇒
  type_memory_size tv = 32
Proof
  rpt strip_tac >> Cases_on `ty` >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >>
       TRY (rename1 `BytesT bd` >> Cases_on `bd`)) >>
  gvs[is_word_type_def, evaluate_type_def, type_memory_size_def, AllCaseEqs()]
QED

Theorem abi_flag_memory:
  evaluate_type tenv (FlagT nsid) = SOME tv ∧
  val_in_memory tv v off mem ∧ off + 32 ≤ LENGTH mem ∧
  vyper_to_abi tenv (FlagT nsid) v = SOME av ⇒
  mem_bytes_at off 32 mem = enc (vyper_to_abi_type tenv (FlagT nsid)) av
Proof
  rpt strip_tac >> Cases_on `v` >>
  gvs[vyper_to_abi_def, evaluate_type_def, AllCaseEqs()] >>
  drule_all val_in_memory_flag_enc >> simp[enc_def, enc_number_def]
QED

(* The typed source word is exactly its ABI word, including bytes20 versus
   address alignment and flags; no untyped value-to-word heuristic is used. *)
Theorem abi_word_memory:
  is_word_type ty ∧ evaluate_type tenv ty = SOME tv ∧
  value_has_type tv v ∧ val_in_memory tv v off mem ∧
  off + 32 ≤ LENGTH mem ∧ vyper_to_abi tenv ty v = SOME av ⇒
  mem_bytes_at off 32 mem = enc (vyper_to_abi_type tenv ty) av ∧
  LENGTH (enc (vyper_to_abi_type tenv ty) av) = 32
Proof
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at off 32 mem = enc (vyper_to_abi_type tenv ty) av` by
    (Cases_on `ty` >> TRY (gvs[is_word_type_def] >> NO_TAC) >>
     FIRST [drule_all abi_base_memory >> simp[],
            drule_all abi_flag_memory >> simp[]]) >>
  conj_tac >- simp[] >>
  qpat_x_assum `mem_bytes_at off 32 mem = _`
    (mp_tac o AP_TERM ``LENGTH : byte list -> num``) >> simp[]
QED
