Theory stmtSimLogScalarPrefix
Ancestors
  abiDecoderRange
  stmtSimLogAllocResource stmtSimLogEncodeLayout abiEncoderComplexPrefix abiBuiltinAllocation
  abiEncoderComplexCode abiDecoderIndexInit abiDecoderReentryAddress
  abiDecoderAllocation abiDecoderReentry abiDecoderGuards abiDecoderFrame
  abiDecoderArrayHeader abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv emitHelper context venomExecSemantics
  venomMemProps venomMemDefs venomState venomInst finite_map words list arithmetic
  abiDecoderFrameCompose

Theorem log_scalar_cursor_prefix_run:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
  p < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand dyn_ptr actual = SOME (n2w p) /\
    mload p actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
    fresh_vars_wrt limit_st actual /\ inst_extends st st' /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_complex_prefix_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `allocation_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all abi_builtin_alloc_buffer_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocation_st) initial = OK allocated` >>
  `eval_operand (Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))) allocated =
    SOME (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))` by simp[eval_operand_def] >>
  `run_inst_seq (emitted_insts allocation_st st') allocated =
    OK (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    (drule_all abi_decode_store_sequence >> simp[w2n_n2w]) >>
  `inst_extends allocation_st st'` by (drule inst_extends_emit_void >> simp[]) >>
  `run_inst_seq (emitted_insts st st') initial =
    OK (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    (drule_all abi_decode_sequence_chain >> simp[]) >>
  `abi_decode_frame p 32 allocated
    (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    irule abi_decode_mstore_frame >>
  qexists_tac `mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated` >>
  fs[abi_builtin_allocation_frame_def, fresh_vars_wrt_mstore, eval_operand_mstore,
      mload_mstore_same] >>
  gvs[abi_decode_frame_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem log_scalar_cursor_resource:
  stmt_state_rel ctx func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w 32)] ==>
  ?p. ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32)) /\
    p < dimword (:256) /\
    (!id b sz. id <> inst.inst_id /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      p+32 <= b \/ b+sz <= p)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all log_event_buffer_resource >>
  disch_then (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists_tac `p` >> asm_simp_tac bool_ss [] >> conj_tac
  >- decide_tac >> first_assum ACCEPT_TAC
QED
