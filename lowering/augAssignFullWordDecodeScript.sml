(* Scalar decode inversion is independent of saved-slot relational agreement. *)
Theory augAssignFullWordDecode
Ancestors
  supportedTypes valueEncoding valueEncodingProofs vyperStorage vyperTyping vyperValue

Theorem supported_full_word_decode:
  supported_full_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
  typed_val_to_w256 tv (decode_base_from_slot w tv) = w
Proof
  simp[supported_full_word_type_def] >> strip_tac >>
  gvs[evaluate_type_def, decode_base_from_slot_def,
      typed_val_to_w256_def, val_to_w256_def]
  >- (`w2n w < 2 ** 256` by
        (mp_tac (Q.ISPEC `w:bytes32` wordsTheory.w2n_lt) >>
         simp[wordsTheory.dimword_def, SF wordsLib.SIZES_ss]) >>
      simp[truncate_unsigned_def, integer_wordTheory.i2w_pos])
  >- (`256 = SUC 255` by decide_tac >>
      pure_once_asm_rewrite_tac[] >> pop_assum kall_tac >>
      pure_rewrite_tac[truncate_signed_def, LET_THM] >> BETA_TAC >>
      `w2n w < 2 ** 256` by
        (mp_tac (Q.ISPEC `w:bytes32` wordsTheory.w2n_lt) >>
         simp[wordsTheory.dimword_def, SF wordsLib.SIZES_ss]) >>
      IF_CASES_TAC >> gvs[] >>
      simp[GSYM arithmeticPropsTheory.word_i2w_sub,
           integer_wordTheory.i2w_pos, wordsTheory.n2w_mod]) >>
  simp[word_of_bytes_be_pad_right, byteTheory.word_of_bytes_be_def,
       byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_word_to_bytes,
       listTheory.TAKE_LENGTH_TOO_LONG, byteTheory.LENGTH_word_to_bytes,
       SF wordsLib.SIZES_ss]
QED
