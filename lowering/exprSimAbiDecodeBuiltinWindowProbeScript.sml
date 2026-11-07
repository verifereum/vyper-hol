Theory exprSimAbiDecodeBuiltinWindowProbe
Ancestors
  exprSimAbiDecodeBuiltinSource abiDecoderCoherence abiDecoderBytestringSource
  abiEncoder compileEnv vyperTyping

Definition window_probe_type_def:
  window_probe_type = TupleT
    [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 2);
     ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 2)]
End

Theorem window_probe_sizes:
  abi_static_size FEMPTY window_probe_type = 64 /\
  static_length (vyper_to_abi_type FEMPTY window_probe_type) = 128 /\
  64 <= abi_size_bound FEMPTY window_probe_type
Proof
  EVAL_TAC >>
  pure_rewrite_tac [wordsTheory.word_0_n2w, wordsTheory.w2n_n2w] >> EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

Theorem window_probe_source:
  (?v. abi_decode_source_accepts FEMPTY window_probe_type
    (REPLICATE 64 (0w:word8)) v) /\
  evaluate_abi_decode FEMPTY window_probe_type (REPLICATE 64 (0w:word8)) =
    INR "abi_decode invalid" /\
  abi_decode_source_view (vyper_to_abi_type FEMPTY window_probe_type)
    (REPLICATE 64 (0w:word8)) 0 = REPLICATE 64 (0w:word8)
Proof
  EVAL_TAC >>
  pure_rewrite_tac [wordsTheory.word_0_n2w, wordsTheory.w2n_n2w] >> EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

Definition window_probe_tv_def:
  window_probe_tv = TupleTV
    [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 2);
     ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 2)]
End

Theorem window_probe_typing:
  assignable_type FEMPTY window_probe_type /\
  abi_decode_bytes_widths FEMPTY window_probe_type
Proof
  EVAL_TAC
QED

Theorem window_probe_coherent:
  ce.ce_struct_fields = FEMPTY ==>
  abi_decoder_coherent ce FEMPTY FEMPTY window_probe_type window_probe_tv
Proof
  strip_tac >>
  simp[window_probe_type_def, window_probe_tv_def,
    abi_decoder_coherent_tuple_iff, abi_decoder_coherent_array_iff,
    abi_decoder_coherent_base_iff, abi_decoder_scalar_valid_def,
    abi_decoder_header_def, type_memory_bytes_def] >>
  EVAL_TAC
QED
