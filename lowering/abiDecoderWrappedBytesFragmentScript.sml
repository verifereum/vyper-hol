(* Actual recursive singleton Bytes decoding, including the outer memory guard. *)
Theory abiDecoderWrappedBytesFragment
Ancestors
  abiDecoderWrapped abiDecoderSingletonSetup abiDecoderTypedCompose abiDecoderBytesTyped
  abiDecoderTypedContract abiDecoderGuards abiDecoderContract abiDecoderBytes abiEncoder
  emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding fragExec
  venomExecSemantics venomState venomInst words rich_list list

Theorem abi_decoder_typed_wrapped_bytes_sequence:
  compile_abi_decode_to_buf dst src MLOAD hi
    (DecComplex T [(DecBytestring n,32,mem_sz)]) st = ((),st') /\
  abi_decoder_pre ce env (TupleT [BaseT (BytesT (Dynamic n))])
    (TupleTV [BaseTV (BytesT (Dynamic n))]) (DecComplex T [(DecBytestring n,32,mem_sz)])
    (ListV [contractABI$BytesV bs]) (ArrayV (TupleV [vyperValue$BytesV bs]))
    st last src dst MLOAD hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (TupleTV [BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [vyperValue$BytesV bs]))
      st' d (abi_decode_bytes_copy_size n) b cap s t
Proof
  strip_tac >> qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_wrapped_bytes_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_singleton_setup dst src MLOAD hi st = (child_ops,c1)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_singleton_setup dst src MLOAD hi st = ((child_src,child_dst),c1)` >>
  `compile_abi_decode_to_buf child_dst child_src MLOAD hi (DecBytestring n) c1 =
    ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decoder_wrapped_bytes_setup >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK mid` >>
  drule_all abi_decoder_typed_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') mid = OK t` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends c1 st'` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `abi_decoder_post (TupleTV [BaseTV (BytesT (Dynamic n))])
     (ArrayV (TupleV [vyperValue$BytesV bs]))
     st' d (abi_decode_bytes_copy_size n) b cap s t` by
    (simp_tac bool_ss [abi_decoder_singleton_post] >>
     drule_all abi_decoder_post_pure_prefix >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_decoder_wrapped_bytes_shape:
  compile_abi_decode_to_buf dst src MLOAD hi
    (DecComplex T [(DecBytestring n,32,mem_sz)]) st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  simp_tac bool_ss [abi_decode_wrapped_bytes_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_singleton_setup dst src MLOAD hi st = (child_ops,c1)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_singleton_setup dst src MLOAD hi st = ((child_src,child_dst),c1)` >>
  `compile_abi_decode_to_buf child_dst child_src MLOAD hi (DecBytestring n) c1 =
    ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends st c1 /\ inst_extends c1 st'` by
    (conj_tac >> irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  gvs[EVERY_CONJ] >> irule IS_PREFIX_TRANS >> qexists_tac `c1.cs_current_insts` >> simp[]
QED

Theorem abi_decoder_typed_wrapped_bytes_fragment:
  compile_abi_decode_to_buf dst src MLOAD hi
    (DecComplex T [(DecBytestring n,32,mem_sz)]) st = ((),st') ==>
  frag_exec ctx st st'
    (abi_decoder_pre ce env (TupleT [BaseT (BytesT (Dynamic n))])
       (TupleTV [BaseTV (BytesT (Dynamic n))]) (DecComplex T [(DecBytestring n,32,mem_sz)])
       (ListV [contractABI$BytesV bs]) (ArrayV (TupleV [vyperValue$BytesV bs]))
       st last src dst MLOAD hi sb d b cap)
    (\t. ?s. abi_decoder_pre ce env (TupleT [BaseT (BytesT (Dynamic n))])
       (TupleTV [BaseTV (BytesT (Dynamic n))]) (DecComplex T [(DecBytestring n,32,mem_sz)])
       (ListV [contractABI$BytesV bs]) (ArrayV (TupleV [vyperValue$BytesV bs]))
       st last src dst MLOAD hi sb d b cap s /\
       abi_decoder_post (TupleTV [BaseTV (BytesT (Dynamic n))])
         (ArrayV (TupleV [vyperValue$BytesV bs]))
         st' d (abi_decode_bytes_copy_size n) b cap s t)
    (K F)
Proof
  strip_tac >> drule abi_decoder_wrapped_bytes_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >>
  drule_all abi_decoder_typed_wrapped_bytes_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx] >> qexists_tac `s` >> simp[]
QED

Theorem abi_decoder_typed_unwrapped_bytes_sequence =
  SIMP_RULE bool_ss [abi_decoder_singleton_post]
    abi_decoder_typed_wrapped_bytes_sequence;

Theorem abi_decoder_typed_unwrapped_bytes_fragment =
  SIMP_RULE bool_ss [abi_decoder_singleton_post]
    abi_decoder_typed_wrapped_bytes_fragment;
