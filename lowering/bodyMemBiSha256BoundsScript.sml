(* SHA256 reads a dynamic bytestring header even when its data is empty. *)
Theory bodyMemBiSha256Bounds
Ancestors
  exprSimMemDefs exprSimProps instMemFrontier words arithmetic

Theorem sha256_bytes_read_ranges:
  b + val_store_size (BaseTV (BytesT (Dynamic cap))) (BytesV bs) <= frontier ==>
  b + 32 <= frontier /\
  (LENGTH bs = 0 \/
   w2n (n2w (b + 32):bytes32) + LENGTH bs <= frontier)
Proof
  simp[val_store_size_def] >> strip_tac >>
  assume_tac (Q.SPEC `LENGTH (bs:word8 list)` le_word_size_mul) >>
  `w2n (n2w (b + 32):bytes32) <= b + 32` by
    simp[w2n_n2w, arithmeticTheory.MOD_LESS_EQ] >>
  fs[w2n_n2w] >> decide_tac
QED

Theorem sha256_string_read_ranges:
  b + val_store_size (BaseTV (StringT cap)) (StringV str) <= frontier ==>
  b + 32 <= frontier /\
  (LENGTH str = 0 \/
   w2n (n2w (b + 32):bytes32) + LENGTH str <= frontier)
Proof
  simp[val_store_size_def] >> strip_tac >>
  assume_tac (Q.SPEC `LENGTH (str:string)` le_word_size_mul) >>
  `w2n (n2w (b + 32):bytes32) <= b + 32` by
    simp[w2n_n2w, arithmeticTheory.MOD_LESS_EQ] >>
  fs[w2n_n2w] >> decide_tac
QED
