(* Factor the actual loop-based array decoder before its finite loop. *)
Theory abiDecoderArrayLoopInit
Ancestors
  abiDecoderIndexInit abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader
  abiDecoderGuards abiDecoderGuard abiDecoderContract abiEncoder exprLoweringProps
  emitHelperProps emitHelper compileEnv context venomInst words list rich_list arithmetic

Definition abi_decode_array_loop_init_def:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz =
    do abi_decode_dynarray_prefix src opc hi maxn abi_sz;
       cnt <- abi_decode_array_header dst src opc;
       ip <- abi_decode_index_init;
       return (ip,cnt)
    od
End

Theorem abi_decode_loop_array_phases:
  elem_dyn \/ dec_info_needs_clamp ei ==>
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz elem_dyn maxn) =
    do setup <- abi_decode_array_loop_init dst src opc hi maxn abi_sz;
       compile_abi_decode_dyn_loop dst src opc hi ei abi_sz mem_sz (FST setup) (SND setup)
    od
Proof
  strip_tac >> `~(~elem_dyn /\ ~dec_info_needs_clamp ei)` by metis_tac[] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
       abi_decode_count_guard_def, abi_decode_dynarray_end_guard_def,
       abi_decode_dynarray_end_def, abi_decode_le_guard_def,
       abi_decode_array_header_def, abi_decode_index_init_def,
       FUN_EQ_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_array_loop_init_trace:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) ==>
  ?guard_st header_st cnt ip.
    abi_decode_dynarray_prefix src opc hi maxn abi_sz st = ((),guard_st) /\
    abi_decode_array_header dst src opc guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\ setup = (ip,cnt)
Proof
  strip_tac >> Cases_on `abi_decode_dynarray_prefix src opc hi maxn abi_sz st` >>
  rename1 `abi_decode_dynarray_prefix src opc hi maxn abi_sz st = (u,guard_st)` >>
  Cases_on `u` >> Cases_on `abi_decode_array_header dst src opc guard_st` >>
  rename1 `abi_decode_array_header dst src opc guard_st = (cnt,header_st)` >>
  Cases_on `abi_decode_index_init header_st` >>
  rename1 `abi_decode_index_init header_st = (ip,after_init)` >>
  qexistsl_tac [`guard_st`, `header_st`, `cnt`, `ip`] >>
  gvs[abi_decode_array_loop_init_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

Theorem abi_decode_loop_array_trace:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz elem_dyn maxn)
    st = ((),st') /\ (elem_dyn \/ dec_info_needs_clamp ei) ==>
  ?setup loop_st.
    abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) /\
    compile_abi_decode_dyn_loop dst src opc hi ei abi_sz mem_sz (FST setup) (SND setup)
      loop_st = ((),st')
Proof
  strip_tac >> Cases_on `abi_decode_array_loop_init dst src opc hi maxn abi_sz st` >>
  rename1 `abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st)` >>
  qexistsl_tac [`setup`, `loop_st`] >>
  gvs[abi_decode_loop_array_phases, comp_bind_def]
QED

Theorem abi_decode_dynarray_prefix_shape:
  abi_decode_dynarray_prefix src opc hi maxn abi_sz st = ((),st') /\
  abi_decode_source_opcode opc ==>
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  st.cs_next_var <= st'.cs_next_var /\
  st.cs_next_id <= st'.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >>
  gvs[abi_decode_dynarray_prefix_def, abi_decode_count_guard_def,
      abi_decode_dynarray_end_guard_def, abi_decode_dynarray_end_def,
      abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decode_source_opcode_def, is_terminator_def,
      is_alloca_op_def, mk_inst_def]
QED

Theorem abi_decode_array_header_shape:
  abi_decode_array_header dst src opc st = (cnt,st') /\ abi_decode_source_opcode opc ==>
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_next_var = st.cs_next_var + 1 /\
  st'.cs_next_id = st.cs_next_id + 2 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decode_source_opcode_def, is_terminator_def,
      is_alloca_op_def, mk_inst_def]
QED
