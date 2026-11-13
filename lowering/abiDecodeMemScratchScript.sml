(* Counted scratch allocation on both fresh entry and reused instruction sites. *)
Theory abiDecodeMemScratch
Ancestors
  abiDecodeScratchMetadata
  abiEncoderWindowCursor abiEncoderWindowSequence exprSimAlloc memSafeRun
  abiDecoderIndexInit abiDecoderReentryAddress abiDecoderArrayHeader abiDecoderContract
  abiBufferAllocationCode bodyDeclWordMemory loweringHalt fragGasPathMem freshWrites venomMemProps
  bodyDeclMemoryCounted bodyDeclMemoryCore bodyAllocMemory
  allocaHistoryFragment allocaSiteResource fragGasSeqMem instMemFrontier
  fragExec fragExecMem abiDecoderRange abiDecodeMemPrimitive
  emitHelperProps exprLoweringProps compileEnv emitHelper context
  venomExecSemantics venomMemDefs venomState venomInst words finite_map list arithmetic

Theorem abi_decode_emit_alloca32_registers[local]:
  emit_op ALLOCA [Lit 32w] st = (out,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  eval_operand out t = SOME w ==>
  t.vs_vars = s.vs_vars |+ (STRING #"%" (toString st.cs_next_var),w) /\
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      eval_operand_def, AllCaseEqs()] >>
  drule abi_decoder_alloca32_registers >> simp[]
QED

Theorem abi_decode_scratch_allocate_path_mem:
  compile_alloc_buffer 32 st = (buf,st') /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  fresh_vars_wrt limit_st s /\ st.cs_next_var < limit_st.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t p. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    p+32 <= t.vs_alloca_next /\ p+32 < dimword (:256) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!q. q <> st.cs_next_id ==>
      FLOOKUP t.vs_allocas q = FLOOKUP s.vs_allocas q) /\
    (case FLOOKUP s.vs_allocas st.cs_next_id of
       NONE => p = s.vs_alloca_next | SOME (b,sz) => p = b) /\
    alloca_room ctx func t /\ alloca_inv t /\ alloca_history func t /\
    fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts
Proof
  strip_tac >>
  `emit_op ALLOCA [Lit 32w] st = (buf.buf_operand,st')` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  drule_all window_emit_alloca32_sequence >> strip_tac >>
  fs[window_seq_def] >>
  drule_all abi_decode_alloca_sequence_metadata >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges,
       inst_dload_in_section_def, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  `same_blocks st st' /\ st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'`
    by fs[inst_extends_def, same_blocks_def] >>
  drule_all body_decl_cursor_path >> strip_tac >>
  drule_all body_alloc_history >> strip_tac >>
  drule_all abi_decode_emit_alloca32_registers >> strip_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH st'.cs_current_insts`, `b`] >>
  drule alloca_room_next_lt >> strip_tac >>
  simp[eval_operand_def, lookup_var_def, alloca_room_def, alloca_inv_def,
     loweringStateRelDefsTheory.fresh_vars_wrt_def, pending_alloca_size_def,
     allocas_non_overlapping_def, alloca_next_valid_def] >>
  fs[alloca_room_def, alloca_inv_def, pending_alloca_size_def,
     allocas_non_overlapping_def, alloca_next_valid_def,
     loweringStateRelDefsTheory.fresh_vars_wrt_def] >> metis_tac[]
QED

Theorem abi_decode_index_init_path_mem:
  abi_decode_index_init st = (ip,st') /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  alloca_room ctx func s /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32) /\
  fresh_vars_wrt limit_st s /\ st.cs_next_var < limit_st.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t p. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    p+32 <= t.vs_alloca_next /\ p+32 < dimword (:256) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!q. q <> st.cs_next_id ==>
      FLOOKUP t.vs_allocas q = FLOOKUP s.vs_allocas q) /\
    (case FLOOKUP s.vs_allocas st.cs_next_id of
       NONE => p = s.vs_alloca_next | SOME (b,sz) => p = b) /\
    alloca_room ctx func t /\ alloca_inv t /\ alloca_history func t /\
    fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decode_frame p 32 s t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `cs_extends st allocation_st` by
    (drule compile_alloc_buffer_extends >> simp[]) >>
  `cs_extends allocation_st st'` by
    (irule cs_extends_emit_inst >>
     qexistsl_tac [`MSTORE`, `[buf.buf_operand; Lit 0w]`, `[]`, `()`] >>
     fs[emit_inst_def, emit_void_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all abi_decode_scratch_allocate_path_mem >> strip_tac >>
  rename1 `gas_path_mem ctx func s 0 (OK allocated)` >>
  `p < dimword (:256)` by decide_tac >>
  `lookup_var (STRING #"%" (toString st.cs_next_var)) allocated = SOME (n2w p)` by
    (qpat_x_assum `eval_operand buf.buf_operand allocated = _` mp_tac >>
     `buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var))` by metis_tac[] >>
     simp[eval_operand_def]) >>
  `w2n (n2w p:bytes32) = p` by simp[w2n_n2w] >>
  `eval_operand (Lit 0w) allocated = SOME 0w` by simp[eval_operand_def] >>
  `emit_void MSTORE [Var (STRING #"%" (toString st.cs_next_var)); Lit 0w]
     allocation_st = ((),st')` by metis_tac[] >>
  `w2n (n2w p:bytes32) + 32 <= allocated.vs_alloca_next` by simp[] >>
  drule_all annassign_word_mstore_path_mem >> simp[] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_path_mem ctx func s 0
    (OK (mstore p 0w allocated with vs_inst_idx := LENGTH st'.cs_current_insts))` by
    (drule_all gas_path_mem_then >> simp[]) >>
  qexistsl_tac [`mstore p 0w allocated with vs_inst_idx := LENGTH st'.cs_current_insts`, `p`] >>
  `abi_decode_frame p 32 allocated (mstore p 0w allocated)` by
    irule abi_decode_mstore_frame >>
  `mload p (mstore p 0w allocated with vs_inst_idx := LENGTH st'.cs_current_insts) = 0w` by
    (`mload p (mstore p 0w allocated with vs_inst_idx := LENGTH st'.cs_current_insts) =
      mload p (mstore p 0w allocated)` by simp[mload_def] >>
     simp[mload_mstore_same]) >>
  simp[] >>
  simp[eval_operand_def, alloca_room_def, alloca_inv_def,
       loweringStateRelDefsTheory.fresh_vars_wrt_def, abi_decode_frame_def,
       pending_alloca_size_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  fs[alloca_room_def, alloca_inv_def, pending_alloca_size_def,
     allocas_non_overlapping_def, alloca_next_valid_def,
     loweringStateRelDefsTheory.fresh_vars_wrt_def, abi_decode_frame_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  drule compile_alloc_buffer_code >> strip_tac >>
  simp[mstore_def, write_memory_with_expansion_def]
QED
