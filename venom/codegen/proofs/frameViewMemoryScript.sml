(*
 * Byte-level memory agreement facts for the frame view.
 *
 * The byte-level read/write lemmas are memoryReadRel's, regularMemorySim's
 * and regularCallEmitSim's; this theory adds the agreement forms the
 * frameView* step lemmas use.
 *
 * TOP-LEVEL:
 *   padded_memory_read_cong     — padded reads agree where the bytes agree
 *   write_memory_byte_agreement — a write keeps byte agreement
 *   write_memory_byte_outside   — a write leaves bytes outside it unchanged
 *)

Theory frameViewMemory
Ancestors
  memoryReadRel venomState codegenRel regularMemorySim regularCallEmitSim list

Theorem padded_memory_read_cong:
  (!i. off <= i /\ i < off + n ==> read_byte i m = read_byte i mem) ==>
  TAKE n (DROP off m ++ REPLICATE n 0w) =
  TAKE n (DROP off mem ++ REPLICATE n 0w)
Proof
  strip_tac >> simp[venom_returndata_read_byte, LIST_EQ_REWRITE] >>
  rpt strip_tac >> simp[EL_GENLIST]
QED

Theorem write_memory_byte_agreement:
  read_byte i s.vs_memory = read_byte i t.vs_memory ==>
  read_byte i (write_memory_with_expansion off bytes s).vs_memory =
  read_byte i (write_memory_with_expansion off bytes t).vs_memory
Proof
  simp[read_byte_write_memory_with_expansion]
QED

Theorem write_memory_byte_outside:
  ~(off <= i /\ i < off + LENGTH bytes) ==>
  read_byte i (write_memory_with_expansion off bytes s).vs_memory =
  read_byte i s.vs_memory
Proof
  simp[read_byte_write_memory_with_expansion]
QED
