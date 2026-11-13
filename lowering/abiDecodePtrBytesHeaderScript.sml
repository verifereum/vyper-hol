Theory abiDecodePtrBytesHeader
Ancestors
  abiDecoderBytes abiDecoderContract abiCanonicalHeadSize abiStaticAggregateProps
  valueEncodingProps valueEncoding venomState words arithmetic
  abiDecodePtrBytesMember abiDecoderExecution
  compileEnv exprLoweringProps

Theorem abi_decode_copied_header:
  mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at a (32+c) s.vs_memory ==>
  mload d t = mload a s
Proof
  strip_tac >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at a 32 s.vs_memory` by
    (qpat_x_assum `_ = _` (mp_tac o AP_TERM ``TAKE 32 : byte list -> byte list``) >>
     simp[abiCanonicalHeadSizeTheory.mem_bytes_at_window |> Q.SPECL [`d`, `0`, `32`, `32+c`] |> SRULE [],
          abiCanonicalHeadSizeTheory.mem_bytes_at_window |> Q.SPECL [`a`, `0`, `32`, `32+c`] |> SRULE []]) >>
  metis_tac[mem_word_at_bytes, mem_word_at_eq_mload]
QED

Theorem abi_decode_bytes_success_header:
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecBytestring n) sa = ((),sb) /\ hi <> Lit 0w /\
  fresh_vars_wrt sa s /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand hi s = SOME (n2w h) /\
  eval_operand (Var src) s = SOME (n2w b) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  p < dimword(:256) /\ h < dimword(:256) /\ b+h < dimword(:256) /\
  n+31 < dimword(:256) /\ d+abi_decode_bytes_copy_size n < dimword(:256) /\
  (b+h <= d \/ d+abi_decode_bytes_copy_size n <= b) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  mload d u = mload (b+p) s
Proof
  strip_tac >>
  `n < dimword(:256)` by decide_tac >>
  drule_all abi_decode_bytes_member_success_bounds >> strip_tac >>
  `b+p < dimword(:256)` by decide_tac >>
  `w2n (mload (b+p) s) <= n /\ p+32+w2n (mload (b+p) s) <= h` by
    (fs[word_add_n2w, w2n_n2w]) >>
  `b+p < dimword(:256) /\ d < dimword(:256) /\ n < dimword(:256)` by decide_tac >>
  `abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w (w2n (mload (b+p) s))` by
    simp[abi_decode_load_def, w2n_n2w] >>
  drule abi_decode_bytes_memory_sequence >>
  disch_then (qspec_then `s` mp_tac) >>
  disch_then (qspecl_then [`p`, `d`, `w2n (mload (b+p) s)`, `b`] mp_tac) >>
  (impl_tac >- (simp[abi_decode_source_opcode_def] >>
    qexists_tac `h` >> simp[])) >>
  strip_tac >> gvs[] >> irule abi_decode_copied_header >>
  qexists_tac `w2n (mload (b+p) s)` >> simp[ADD_COMM]
QED
