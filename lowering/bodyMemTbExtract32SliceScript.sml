(* Raw word loads from a represented dynamic Bytes payload. *)
Theory bodyMemTbExtract32Slice
Ancestors
  abiCanonicalHeadSize valueEncodingProps valueEncoding byte words valueEncodingDefs
  vyperValue vyperAST

Theorem extract32_payload_word:
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p mem /\
  n + 32 <= LENGTH bs ==>
  mem_word_at (p + 32 + n) mem =
    word_of_bytes_be (TAKE 32 (DROP n bs))
Proof
  strip_tac >>
  `mem_bytes_at (p + 32) (LENGTH bs) mem = bs` by
    gvs[val_in_memory_def] >>
  drule mem_bytes_at_window >>
  disch_then (qspecl_then [`p + 32`, `mem`] mp_tac) >>
  simp[mem_word_at_def, GSYM mem_bytes_at_def, word_of_bytes_be_def]
QED

Theorem extract32_payload_mload:
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) p s.vs_memory /\
  n + 32 <= LENGTH bs /\ p + 32 + n < dimword (:256) ==>
  mload (w2n ((n2w (p + 32):bytes32) + n2w n)) s =
    word_of_bytes_be (TAKE 32 (DROP n bs))
Proof
  strip_tac >>
  drule_all extract32_payload_word >>
  simp[mem_word_at_eq_mload, word_add_n2w, w2n_n2w]
QED
