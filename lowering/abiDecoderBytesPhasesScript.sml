(* Structural factoring of bounded-position bytes decoding. *)
Theory abiDecoderBytesPhases
Ancestors
  abiEncoder abiDecoderRange abiDecoderGuards abiDecoderCopy abiDecoderBytesBound
  abiDecoderComposition abiDecoderContract emitHelperProps exprLoweringProps compileEnv emitHelper
  venomInst words list rich_list

Definition abi_decode_bytes_runtime_tail_def:
  abi_decode_bytes_runtime_tail dst addr cnt =
    do len_up <- emit_op ADD [cnt; Lit 31w];
       mask <- emit_op NOT [Lit 31w];
       data_sz <- emit_op AND [len_up; mask];
       last_word <- emit_op ADD [dst; data_sz];
       emit_void MSTORE [last_word; Lit 0w];
       copy_sz <- emit_op ADD [Lit 32w; cnt];
       emit_void MCOPY [dst; addr; copy_sz]
    od
End

Theorem abi_decode_bytes_position_phases:
  abi_decode_source_opcode opc ==>
  compile_abi_decode_to_buf dst pos opc base_op hi (DecBytestring n) =
    do head <- abi_decode_bytes_head pos hi;
       addr <- compile_abi_dec_addr base_op pos;
       cnt <- abi_decode_count_guard opc addr n;
       abi_decode_bytes_payload_guard head cnt hi;
       if base_op = Lit 0w then
         emit_void (abi_decode_copy_opcode opc)
           [dst; pos; Lit (n2w (32 + 32 * ((n + 31) DIV 32)))]
       else abi_decode_bytes_runtime_tail dst addr cnt
    od
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >>
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[FUN_EQ_THM, compile_abi_decode_to_buf_def, abi_decode_count_guard_def,
       abi_decode_bytes_head_def, abi_decode_bytes_payload_guard_def,
       abi_decode_bytes_runtime_tail_def, abi_decode_copy_opcode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_bytes_position_sentinel:
  abi_decode_source_opcode opc ==>
  compile_abi_decode_to_buf dst pos opc base_op (Lit 0w) (DecBytestring n) =
    do addr <- compile_abi_dec_addr base_op pos;
       cnt <- abi_decode_count_guard opc addr n;
       if base_op = Lit 0w then
         emit_void (abi_decode_copy_opcode opc)
           [dst; pos; Lit (n2w (32 + 32 * ((n + 31) DIV 32)))]
       else abi_decode_bytes_runtime_tail dst addr cnt
    od
Proof
  strip_tac >> asm_simp_tac bool_ss [abi_decode_bytes_position_phases] >>
  simp[FUN_EQ_THM, abi_decode_bytes_head_def, abi_decode_bytes_payload_guard_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_bytes_runtime_tail_shape:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') ==>
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_next_var = st.cs_next_var + 5 /\ st'.cs_next_id = st.cs_next_id + 7 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  simp[abi_decode_bytes_runtime_tail_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >>
  rpt strip_tac >> gvs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_decode_bytes_position_shape:
  compile_abi_decode_to_buf dst pos opc base_op hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_position_phases] >>
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  gvs[abi_decode_bytes_head_def, compile_abi_dec_addr_def,
      abi_decode_count_guard_def, abi_decode_bytes_payload_guard_def,
      abi_decode_bytes_runtime_tail_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decode_source_opcode_def, abi_decode_copy_opcode_def,
      is_terminator_def, is_alloca_op_def, mk_inst_def]
QED
