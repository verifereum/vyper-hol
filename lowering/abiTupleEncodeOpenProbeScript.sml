(* Boundary probes for open-input tuple staging; existing strict contracts stay unchanged. *)
Theory abiTupleEncodeOpenProbe
Ancestors
  abiTupleEncodeSlot abiEncoderOpenInputFrame abiEncoderOpenInput
  abiDecoderContract valueEncoding contractABI words list rich_list arithmetic

Theorem abi_tuple_encode_open_window_frame:
  abi_encoder_open_input ei at av sb source_cap s.vs_memory /\
  abi_decode_frame lo (hi-lo) s t /\ lo <= hi /\
  (sb+source_cap <= lo \/ hi <= sb) ==>
  abi_encoder_open_input ei at av sb source_cap t.vs_memory
Proof
  strip_tac >> drule abi_encoder_open_input_mem_agree >>
  disch_then irule >> irule EQ_SYM >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp[abi_decode_frame_def] >> strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem abi_tuple_encode_open_zero_dynamic_frame_probe:
  mem_word_at sb s.vs_memory = 0w /\ abi_decode_frame lo (hi-lo) s t /\
  lo <= hi /\ (sb+32 <= lo \/ hi <= sb) ==>
  abi_encoder_open_input
    (AbiComplex [(AbiCopy 0,0,0,F); (AbiBytestring 0,32,32,T)])
    (Tuple [Tuple []; Bytes NONE]) (ListV [ListV []; BytesV []]) sb 32 t.vs_memory
Proof
  strip_tac >> irule abi_tuple_encode_open_window_frame >>
  qexistsl_tac [`hi`, `lo`, `s`] >> simp[] >>
  mp_tac (Q.SPECL [`SUC 0`, `sb`, `s.vs_memory`] abi_encoder_open_zero_prefix) >>
  pure_rewrite_tac[REPLICATE] >> simp[]
QED
