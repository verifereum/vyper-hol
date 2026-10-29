(* Ordinary byte producers supply count/data observations and own 32+maxlen
   bytes. Their unused semantic rounding padding may overlap the tuple buffer. *)
Theory abiTupleEncodeOwnedBytes
Ancestors
  abiTupleEncodeSourceInput abiTupleEncodeInput abiEncoderInput abiEncoderBytes
  abiDecoderReentry compileEnv exprLowering valueEncoding valueEncodingProps vyperABI
  contractABI venomState venomExecSemantics words list arithmetic

Theorem abi_tuple_encode_owned_bytes_capacity:
  32+n <= type_memory_bytes ce (BaseT (BytesT (Dynamic n)))
Proof
  mp_tac (PURE_REWRITE_RULE [ceil32_def] le_ceil32) >>
  simp[type_memory_bytes_def, MULT_COMM]
QED

Theorem abi_tuple_encode_owned_bytes_source_input:
  type_memory_bytes ce (BaseT (BytesT (Dynamic n))) < dimword (:256) /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME source_word /\
  mload (w2n source_word) s = n2w (LENGTH bs) /\
  mem_bytes_at (w2n source_word+32) (LENGTH bs) s.vs_memory = bs /\
  LENGTH bs <= n /\ n < dimword (:256) /\
  (w2n source_word+(32+n) <= lo \/ hi <= w2n source_word) ==>
  abi_tuple_encode_input sf ce (BaseT (BytesT (Dynamic n)))
    (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bs)
    op next lo hi s
Proof
  strip_tac >>
  `abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (BytesT (Dynamic n))))
     (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bs)
     (w2n source_word) (32+n) s.vs_memory` by
    (simp[abi_encoder_input_bytes_iff, type_to_abi_enc_info_def,
       vyper_to_abi_type_def, has_type_def, valid_bytes_bound_def, valid_length_def,
       mem_word_at_eq_mload] >> decide_tac) >>
  mp_tac (Q.INST [`ty` |-> `BaseT (BytesT (Dynamic n))`, `source_cap` |-> `32+n`,
    `at` |-> `vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))`,
    `av` |-> `contractABI$BytesV (bs:word8 list)`] abi_tuple_encode_nonword_source_input) >>
  simp[is_word_type_def, abi_tuple_encode_owned_bytes_capacity]
QED

(* With 64 encoded bytes and a four-byte method ID, actual allocation is 100.
   Full 128-byte separation is false; separation of the owned 100 bytes holds. *)
Theorem abi_tuple_encode_method_bytes_extent:
  type_memory_bytes ce (BaseT (BytesT (Dynamic 68))) = 128 /\
  ~(p+type_memory_bytes ce (BaseT (BytesT (Dynamic 68))) <= p+100 \/ p+228 <= p) /\
  p+(32+68) <= p+100
Proof
  simp[type_memory_bytes_def]
QED
