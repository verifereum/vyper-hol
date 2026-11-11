(* TOP-LEVEL: raw_return_copy preserves the length-prefixed Bytes value and
   the bytes selected by raw RETURN after copying to a fresh buffer.
   MCOPY snapshots the source, so the boundary also covers overlapping ranges. *)
Theory rawReturnCopy
Ancestors
  valueEncodingDefs list arithmetic words
  copyFwdEquiv allocaRemapDefs venomExecSemantics venomState
  valueEncoding valueEncodingProofs exprSimBufferStore vyperValue vyperAST vyperTyping

Theorem raw_return_copy:
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV data) src s.vs_memory /\
  LENGTH data < dimword (:256) /\ dst + 32 < dimword (:256) /\
  32 + LENGTH data <= copied ==>
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV data) dst
    (mcopy dst src copied s).vs_memory /\
  mem_bytes_at (w2n ((n2w dst : bytes32) + 32w))
    (w2n (mem_word_at dst (mcopy dst src copied s).vs_memory))
    (mcopy dst src copied s).vs_memory = data
Proof
  simp[val_in_memory_def] >> strip_tac >>
  `mem_bytes_at dst 32 (mcopy dst src copied s).vs_memory =
   mem_bytes_at src 32 s.vs_memory` by
    (mp_tac (Q.SPECL [`dst`,`src`,`copied`,`s`,`0`,`32`] buffer_mcopy_window) >> simp[]) >>
  `mem_word_at dst (mcopy dst src copied s).vs_memory =
   mem_word_at src s.vs_memory` by
    fs[mem_word_at_def, mem_bytes_at_def] >>
  `mem_bytes_at (dst + 32) (LENGTH data)
      (mcopy dst src copied s).vs_memory = data` by
    (mp_tac (Q.SPECL [`dst`,`src`,`copied`,`s`,`32`,`LENGTH (data : word8 list)`]
      buffer_mcopy_window) >> simp[]) >>
  simp[word_add_n2w]
QED
