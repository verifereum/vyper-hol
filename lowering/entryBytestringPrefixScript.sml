(* Source-valid Bytes/String decoding reaches its cut in the original function. *)
Theory entryBytestringPrefix
Ancestors
  entryWordPrefix abiValidBytesReentry abiDecoderValidBytesInput
  abiDecoderBytesTyped entrySinkExtraction abiDecoderContract abiDecoderValidContract
  fragExec abiEncoderObserver instIdxIndep exprLoweringProps
  venomExecSemantics venomState compileEnv valueEncoding list rich_list

Theorem decoder_valid_bytestring_local_prefix:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD (Lit 0w)
    sb d b cap initial /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last func /\ last.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory tv v d t.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = last.cs_current_bb /\
    t.vs_inst_idx = LENGTH last.cs_current_insts /\
    local_prefix ctx func (last.cs_current_bb,LENGTH last.cs_current_insts) initial t /\
    abi_decode_frame d (type_memory_bytes ce ty) initial t /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
    fresh_vars_wrt limit_st t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_bytes_input >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all abi_decoder_valid_bytes_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st last) initial = OK actual` >>
  `val_in_memory tv v d actual.vs_memory` by metis_tac[] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `last.cs_current_insts = st.cs_current_insts ++ emitted_insts st last` by
    (fs[IS_PREFIX_APPEND, emitted_insts_def] >> simp[DROP_LENGTH_APPEND]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `LENGTH st.cs_current_insts + LENGTH (emitted_insts st last) =
    LENGTH last.cs_current_insts` by metis_tac[LENGTH_APPEND] >>
  `local_prefix ctx func (initial.vs_current_bb,
      initial.vs_inst_idx + LENGTH (emitted_insts st last)) initial
      (actual with vs_inst_idx := initial.vs_inst_idx + LENGTH (emitted_insts st last))` by
    (irule decoder_sequence_local_prefix >> asm_rewrite_tac[] >>
     qexists_tac `bb` >> asm_rewrite_tac[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qexists_tac `actual with vs_inst_idx := LENGTH last.cs_current_insts` >>
  asm_simp_tac bool_ss [venom_state_accfupds, venom_state_component_equality] >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >>
  first_assum ACCEPT_TAC
QED
