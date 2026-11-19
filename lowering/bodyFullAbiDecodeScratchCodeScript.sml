Theory bodyFullAbiDecodeScratchCode
Ancestors
  abiDecoderIndexInit loweringHalt externalEntryShape fragExec emitHelperProps

Theorem abi_decode_scratch_code:
  abi_decode_index_init sa = (ip,loop_st) ==>
  ?buf sb counter.
    compile_alloc_buffer 32 sa = (buf,sb) /\ buf.buf_operand = ip /\
    emit_void MSTORE [ip;Lit 0w] sb = ((),loop_st) /\
    ip = Var counter /\ ~not_fresh_at sa counter /\
    not_fresh_at loop_st counter /\
    abi_decoder_operand_live loop_st.cs_next_var ip /\
    sa.cs_next_id < loop_st.cs_next_id /\
    sb.cs_current_bb = sa.cs_current_bb /\
    loop_st.cs_current_bb = sb.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [counter]] /\
    loop_st.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id MSTORE [ip;Lit 0w] []] /\
    (!obs. fn_has_code sa loop_st obs ==>
       fn_has_code sa sb obs /\ fn_has_code sb loop_st obs)
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  qexistsl_tac [`buf`, `allocation_st`, `STRING #"%" (toString sa.cs_next_var)`] >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       loweringStateRelDefsTheory.not_fresh_at_def] >>
  rpt strip_tac >>
  `cs_extends sa allocation_st` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends allocation_st loop_st` by
    ((qspecl_then [`MSTORE`, `[ip;Lit 0w]`, `allocation_st`, `\x. T`]
       mp_tac emit_void_labels >> simp[] >> (gvs[]))) >>
  metis_tac[fn_has_code_split]
QED
