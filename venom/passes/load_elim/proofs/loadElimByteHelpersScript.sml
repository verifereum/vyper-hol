Theory loadElimByteHelpers
Ancestors
  vfmTypes rich_list

Theorem word_to_bytes_aux_zero:
  !n be. word_to_bytes_aux n (0w:'a word) be = REPLICATE n (0w:8 word)
Proof
  Induct_on `n` >>
  simp[byteTheory.word_to_bytes_aux_def, byteTheory.get_byte_def,
       wordsTheory.ZERO_SHIFT, wordsTheory.w2w_0,
       GSYM listTheory.SNOC_APPEND, rich_listTheory.SNOC_REPLICATE]
QED

Theorem word_of_bytes_zero_256:
  word_of_bytes T (0w:256 word) (REPLICATE 32 (0w:8 word)) = 0w
Proof
  `REPLICATE 32 (0w:8 word) = word_to_bytes (0w:256 word) T`
    by simp[byteTheory.word_to_bytes_def, fcpLib.INDEX_CONV ``dimindex (:256)``,
            word_to_bytes_aux_zero] >>
  simp[vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED
