(* Meaningful-byte interface for immutable assignment stores. *)
Theory immutableDeployAssignBytes
Ancestors
  immutableValue immutableEncoding immutableEncodingProofs valueEncodingProofs
  abiEncoderMemory abiCanonicalHeadSize valueTypingMemoryProps
  valueEncoding list rich_list

Theorem immutable_mask_prefix_agreement:
  !n k actual expected.
    LENGTH actual = n /\ LENGTH expected = n /\
    TAKE k actual = TAKE k expected ==>
    EVERY (\(used,(a,e)). used ==> a = e)
      (ZIP (TAKE n (REPLICATE k T ++ REPLICATE n F),
            ZIP (actual,expected)))
Proof
  rpt strip_tac >> simp[EVERY_EL, EL_ZIP, EL_TAKE] >>
  rpt strip_tac >>
  Cases_on `n' < k` >> gvs[EL_APPEND_EQN, EL_REPLICATE] >>
  qpat_x_assum `TAKE k actual = TAKE k expected`
    (mp_tac o AP_TERM ``EL n'``) >>
  simp[EL_TAKE]
QED

Theorem immutable_payload_prefix[local]:
  LENGTH bs = k /\ k + 32 <= cap /\
  mem_word_at off mem = n2w k /\
  mem_bytes_at (off+32) k mem = bs ==>
  TAKE (k + 32) (mem_bytes_at off cap mem) =
  TAKE (k + 32)
    (immutable_fit cap (word_to_bytes (n2w k:bytes32) T ++ bs))
Proof
  rpt strip_tac >> gvs[] >>
  drule_all abi_encoder_bytes_source_prefix >> strip_tac >>
  `TAKE (LENGTH bs + 32) (mem_bytes_at off cap mem) =
    mem_bytes_at off (LENGTH bs + 32) mem` by
    metis_tac[mem_bytes_at_window, DROP_0, arithmeticTheory.ADD_CLAUSES] >>
  simp[immutable_fit_def, TAKE_TAKE, arithmeticTheory.ADD_COMM,
       TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem immutable_base_memory_bytes:
  immutable_value_admissible (BaseTV bt) v /\
  val_in_memory (BaseTV bt) v off mem ==>
  immutable_value_bytes_rel (BaseTV bt) v
    (mem_bytes_at off (type_memory_size (BaseTV bt)) mem)
Proof
  let val base_case =
  Cases_on `v` >>
  simp[immutable_value_admissible_def, val_in_memory_def] >>
  rpt strip_tac >>
  simp[immutable_value_bytes_rel_def, immutable_value_mask_def,
       encode_immutable_value_def, type_memory_size_def,
       immutable_word_fit, immutable_mask_fit_def,
       typed_val_to_w256_def, mem_bytes_at_word,
       TAKE_APPEND1, TAKE_LENGTH_ID_rwt] >>
  simp[immutable_word_bytes_def, immutable_mask_same_bytes] >>
  match_mp_tac immutable_mask_prefix_agreement >>
  simp[] >>
  irule immutable_payload_prefix >> simp[] >>
  mp_tac (Q.SPEC `n` word_size_capacity) >> decide_tac
  in
    Cases_on `bt` >~ [`BytesT b`]
    >- (Cases_on `b` >> base_case)
    >> base_case
  end
QED
