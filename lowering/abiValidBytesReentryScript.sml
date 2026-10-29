(* Noncanonical Bytes/String children may re-enter with stale local SSA bindings. *)
Theory abiValidBytesReentry
Ancestors
  abiDecoderValidBytes abiDecoderBytesFrame abiDecoderBytes abiDecoderString
  abiDecoderReentryPrefix abiDecoderReentrySequence abiDecoderReentry abiDecoderVarExtend
  abiDecoderReservation abiDecoderContract valueEncoding compileEnv
  venomExecSemantics venomState words list

Theorem abi_decoder_valid_bytes_reentry:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_valid_bytes_pre n at bs payload st src dst opc hi sb d
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d actual.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    fresh_vars_wrt limit_st actual /\ actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >> drule_all abi_decoder_valid_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st')
    (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_valid_bytes_pre_def, Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
