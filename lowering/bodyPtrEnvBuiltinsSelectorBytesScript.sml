(* The four-byte payload survives padding and a full-word store. *)
Theory bodyPtrEnvBuiltinsSelectorBytes
Ancestors venomMemProps list rich_list words

Theorem selector_padded_word_bytes:
  LENGTH (bs:word8 list) = 4 ==>
  TAKE 4 (word_to_bytes (word_of_bytes T (0w:256 word)
    (TAKE 32 (bs ++ REPLICATE 31 (0w:word8)))) T) = bs
Proof
  strip_tac >>
  `LENGTH (TAKE 32 (bs ++ REPLICATE 31 (0w:word8))) = 32` by
    simp[LENGTH_TAKE_EQ] >>
  drule word_bytes_roundtrip_256 >> disch_then SUBST1_TAC >>
  simp[TAKE_TAKE, TAKE_APPEND]
QED
