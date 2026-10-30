(* Actual scratch-index allocation and zero initialization, including site reuse. *)
Theory abiDecoderIndexInit
Ancestors
  abiDecoderReentryAllocation abiDecoderAllocation abiDecoderReentry
  abiDecoderArrayHeader abiDecoderGuards abiDecoderContract abiDecoderFrame
  emitHelperProps exprLoweringProps compileEnv emitHelper context
  venomExecSemantics venomMemProps venomState venomInst finite_map words list rich_list arithmetic

Definition abi_decode_index_init_def:
  abi_decode_index_init =
    do buf <- compile_alloc_buffer 32;
       emit_void MSTORE [buf.buf_operand; Lit 0w];
       return buf.buf_operand
    od
End

Theorem abi_decode_index_init_trace:
  abi_decode_index_init st = (ip,st') ==>
  ?buf allocation_st.
    compile_alloc_buffer 32 st = (buf,allocation_st) /\ ip = buf.buf_operand /\
    emit_void MSTORE [buf.buf_operand; Lit 0w] allocation_st = ((),st')
Proof
  strip_tac >> Cases_on `compile_alloc_buffer 32 st` >>
  rename1 `compile_alloc_buffer 32 st = (buf,allocation_st)` >>
  qexistsl_tac [`buf`, `allocation_st`] >>
  gvs[abi_decode_index_init_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_void_def, fresh_id_def, emit_def]
QED

Theorem abi_decode_index_init_shape:
  abi_decode_index_init st = (ip,st') ==>
  ip = Var (STRING #"%" (toString st.cs_next_var)) /\
  st'.cs_next_var = st.cs_next_var + 1 /\ st'.cs_next_id = st.cs_next_id + 2 /\
  st'.cs_current_bb = st.cs_current_bb /\ st'.cs_blocks = st.cs_blocks /\
  inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_decode_store_sequence:
  emit_void MSTORE [address_op;value_op] st = ((),st') /\
  eval_operand address_op s = SOME p /\ eval_operand value_op s = SOME w ==>
  run_inst_seq (emitted_insts st st') s = OK (mstore (w2n p) w s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_def, Once step_inst_base_def, exec_write2_def, mk_inst_def]
QED

Theorem abi_decoder_budget_word_bound:
  abi_decoder_budget first last b cap s ==> b + cap < dimword (:256)
Proof
  simp_tac bool_ss [abi_decoder_budget_def] >> strip_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_budget_mstore[simp]:
  abi_decoder_budget first last b cap (mstore p w s) <=>
  abi_decoder_budget first last b cap s
Proof
  simp[abi_decoder_budget_def, abi_decoder_missing_def, mstore_def,
       write_memory_with_expansion_def]
QED

Theorem abi_decode_alloc_buffer_inst_extends:
  compile_alloc_buffer n st = (buf,st') ==> inst_extends st st'
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> drule inst_extends_emit_op >> simp[]
QED

Theorem abi_decoder_operand_mstore[simp]:
  eval_operand op (mstore p w s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, mstore_def,
                        write_memory_with_expansion_def]
QED

Theorem abi_decode_index_init_sequence:
  abi_decode_index_init st = (ip,st') /\
  abi_decoder_budget first last b cap s /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    b <= p /\ p + 32 <= b + cap /\
    abi_decoder_budget first last b cap t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decode_frame p 32 s t /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `allocation_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_alloc_buffer_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocation_st) s = OK allocated` >>
  drule abi_decoder_budget_word_bound >> strip_tac >>
  `p < dimword (:256)` by decide_tac >>
  `eval_operand (Lit 0w) allocated = SOME 0w` by simp[eval_operand_def] >>
  `run_inst_seq (emitted_insts allocation_st st') allocated = OK (mstore p 0w allocated)` by
    (drule_all abi_decode_store_sequence >> simp[eval_operand_def, w2n_n2w]) >>
  `inst_extends st allocation_st /\ inst_extends allocation_st st'` by
    (conj_tac
     >- (drule abi_decode_alloc_buffer_inst_extends >> simp[]) >>
     drule inst_extends_emit_void >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK (mstore p 0w allocated)` by
    (drule_all abi_decode_sequence_chain >> simp[]) >>
  `abi_decode_frame p 32 allocated (mstore p 0w allocated)` by
    irule abi_decode_mstore_frame >>
  `abi_decoder_budget first last b cap (mstore p 0w allocated)` by simp[] >>
  `mload p (mstore p 0w allocated) = 0w` by simp[mload_mstore_same] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op (mstore p 0w allocated) = eval_operand op s` by
    simp[] >>
  qexistsl_tac [`mstore p 0w allocated`, `p`] >>
  gvs[fresh_vars_wrt_mstore,
      eval_operand_mstore, abi_decode_frame_def, mstore_def,
      write_memory_with_expansion_def] >>
  first_assum ACCEPT_TAC
QED
