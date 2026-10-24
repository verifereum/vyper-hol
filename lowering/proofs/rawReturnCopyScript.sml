(* TOP-LEVEL: raw_return_copy preserves the length-prefixed Bytes value and
   the bytes selected by raw RETURN after copying to a fresh buffer.
   Helper: mcopy_bytes_at transports any subwindow of the copied region.
   MCOPY snapshots the source, so the boundary also covers overlapping ranges. *)
Theory rawReturnCopy
Ancestors
  list arithmetic words
  copyFwdEquiv allocaRemapDefs venomExecSemantics venomState
  valueEncoding valueEncodingProofs vyperValue vyperAST vyperTyping

Theorem mcopy_bytes_at:
  offset + len <= copied ==>
  mem_bytes_at (dst + offset) len (mcopy dst src copied s).vs_memory =
  mem_bytes_at (src + offset) len s.vs_memory
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_mem_bytes_at_proof] >>
  qx_gen_tac `i` >> strip_tac >>
  `offset + i < copied` by decide_tac >>
  mp_tac (Q.SPEC `offset + i`
    (SRULE [LET_THM] (Q.SPECL [`s`,`dst`,`src`,`copied`]
      mcopy_establishes_equiv))) >>
  asm_simp_tac std_ss
    [EL_mem_bytes_at, mem_byte_at_def, AC ADD_ASSOC ADD_COMM]
QED

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
    (irule (SRULE [] (Q.INST [`offset` |-> `0`] mcopy_bytes_at)) >> decide_tac) >>
  `mem_word_at dst (mcopy dst src copied s).vs_memory =
   mem_word_at src s.vs_memory` by
    fs[mem_word_at_def, mem_bytes_at_def] >>
  `mem_bytes_at (dst + 32) (LENGTH data)
      (mcopy dst src copied s).vs_memory = data` by
    (mp_tac (Q.INST [`offset` |-> `32`, `len` |-> `LENGTH (data : word8 list)`]
      mcopy_bytes_at) >> simp[]) >>
  simp[word_add_n2w]
QED

val () = List.app (fn (name, th) =>
  if null (Thm.hyp th) andalso
     List.all (fn tag => tag = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th))) andalso
     null (#2 (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail ("Unexpected proof assumption: " ^ name))
  (DB.thms "rawReturnCopy");
