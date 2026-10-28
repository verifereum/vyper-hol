(* The slot codec also represents word-addressed local memory: recursive
   offsets are word indices (32 bytes in memory, one slot in storage), fixed
   bytes are left aligned, and apply_writes preserves unwritten capacity. *)
Theory vyperMemory
Ancestors
  vyperAST vyperValue vyperStorage vfmState words list
Libs
  wordsLib

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``];

Theorem memory_fixed_bytes_roundtrip:
  encode_value (BaseTV (BytesT (Fixed 2))) (BytesV [18w;52w]) =
    SOME [(0, (0x1234w:256 word) << 240)] ∧
  decode_value
    (apply_writes 0w [(0, (0x1234w:256 word) << 240)] empty_storage)
    0 (BaseTV (BytesT (Fixed 2))) = SOME (BytesV [18w;52w])
Proof
  EVAL_TAC
QED
