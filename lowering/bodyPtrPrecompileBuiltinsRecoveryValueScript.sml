Theory bodyPtrPrecompileBuiltinsRecoveryValue
Ancestors exprSimPrecompiles exprSimHash valueEncodingProofs valueEncoding valueCopy
          venomCallOracleDefs extCallOracle venomMemDefs venomState
          list rich_list words vfmExecution byte vfmTypes vfmBuffer

Theorem recovery_output_encoding:
  ((data = [] /\ (addr:address) = 0w) \/
   data = PAD_LEFT 0w 32 (word_to_bytes addr T)) ==>
  (word_of_bytes_be (TAKE 32 (data ++ REPLICATE 32 0w)) : bytes32) =
  typed_val_to_w256 (BaseTV AddressT) (AddressV addr)
Proof
  strip_tac
  >- (gvs[] >> simp[typed_val_to_w256_def, val_to_w256_address,
        GSYM word_to_bytes_w2w_address, word_of_bytes_be_def,
        word_to_bytes_word_of_bytes_256, TAKE_LENGTH_TOO_LONG,
        word_of_bytes_replicate_zero, wordsTheory.w2w_0]) >>
  gvs[typed_val_to_w256_def] >> AP_TERM_TAC >>
  `LENGTH (PAD_LEFT 0w 32 (word_to_bytes addr T)) = 32` by
    simp[PAD_LEFT, LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem recovery_output_write:
  mem_word_at off s.vs_memory = 0w /\
  ((data = [] /\ (addr:address) = 0w) \/
    data = PAD_LEFT 0w 32 (word_to_bytes addr T)) ==>
  mem_word_at off
    (write_memory_with_expansion off (TAKE 32 data) s).vs_memory =
    typed_val_to_w256 (BaseTV AddressT) (AddressV addr)
Proof
  strip_tac
  >- (`mem_bytes_at off 32
        (write_memory_with_expansion off [] s).vs_memory =
        mem_bytes_at off 32 s.vs_memory` by
        (irule mem_bytes_at_write_disjoint >> simp[]) >>
      gvs[mem_word_at_def, mem_bytes_at_def] >>
      simp[typed_val_to_w256_def, val_to_w256_address,
           GSYM word_to_bytes_w2w_address, word_of_bytes_be_def,
           word_to_bytes_word_of_bytes_256, TAKE_LENGTH_TOO_LONG,
           word_of_bytes_replicate_zero, wordsTheory.w2w_0]) >>
  `LENGTH data = 32` by
    gvs[PAD_LEFT, LENGTH_word_to_bytes,
        fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  `TAKE 32 data = data` by simp[GSYM LENGTH_NIL, TAKE_LENGTH_TOO_LONG] >>
  `mem_bytes_at off 32
      (write_memory_with_expansion off data s).vs_memory = data` by
    metis_tac[hash_write_memory_read_self] >>
  mp_tac recovery_output_encoding >>
  (impl_tac >- simp[]) >>
  gvs[mem_word_at_def, GSYM mem_bytes_at_def, word_of_bytes_be_def,
      TAKE_LENGTH_TOO_LONG] >>
  metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem recovery_result_four_words:
  !(h:bytes32) (v:bytes32) (r:bytes32) (sig:bytes32).
  precompile_result 1w
    (word_to_bytes h T ++ word_to_bytes v T ++
     word_to_bytes r T ++ word_to_bytes sig T) =
  SOME (SOME (case vfmExecution$ecrecover h (w2n v) (w2n r) (w2n sig) of
    NONE => [] | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T)))
Proof
  rpt gen_tac >>
  rewrite_tac[precompile_result_def, take_pad_word_prefix] >>
  simp[take_pad_0_def,
       LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``,
       listTheory.TAKE_APPEND1, listTheory.DROP_APPEND,
       TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, PAD_RIGHT,
       num_of_be_bytes_word32, word_to_bytes_word_of_bytes_32,
       word_of_bytes_be_def]
QED

Theorem recovery_request_result:
  mem_bytes_at (w2n ai) 128 s.vs_memory =
    word_to_bytes (h:bytes32) T ++ word_to_bytes (v:bytes32) T ++
    word_to_bytes (r:bytes32) T ++ word_to_bytes (sig:bytes32) T ==>
  precompile_result (venom_call_request s 1w 0w ai 128w T).cr_target
    (venom_call_request s 1w 0w ai 128w T).cr_data =
    SOME (SOME (case vfmExecution$ecrecover h (w2n v) (w2n r) (w2n sig) of
      NONE => [] | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T)))
Proof
  strip_tac >>
  simp[venom_call_request_def, venomStateTheory.read_memory_def, GSYM mem_bytes_at_def,
       wordsTheory.dimword_def, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``, recovery_result_four_words]
QED
