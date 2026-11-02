(* Exact phases of the existing bytestring encoder; compiler code is unchanged. *)
Theory abiEncoderBytesCode
Ancestors
  abiEncoder emitHelper context compileEnv abiDecoderContract
  emitHelperProps exprLoweringProps venomInst words list rich_list arithmetic
Libs monadsyntax

Definition abi_encode_round_def:
  abi_encode_round len =
    do arg <- emit_op ADD [Lit 31w;len];
       emit_op AND
         [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;arg]
    od
End

Definition abi_encode_bytes_prefix_def:
  abi_encode_bytes_prefix dst src =
    do len <- emit_op MLOAD [src];
       rounded <- abi_encode_round len;
       lastptr <- emit_op ADD [dst;rounded];
       return (len,lastptr)
    od
End

Definition abi_encode_bytes_copy_def:
  abi_encode_bytes_copy dst src len lastptr =
    do emit_void MSTORE [lastptr;Lit 0w];
       copylen <- emit_op ADD [Lit 32w;len];
       emit_void MCOPY [dst;src;copylen]
    od
End

Definition abi_encode_bytes_suffix_def:
  abi_encode_bytes_suffix len =
    do rounded <- abi_encode_round len;
       emit_op ADD [Lit 32w;rounded]
    od
End

Theorem abi_encode_bytes_phases:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) =
    do ops <- abi_encode_bytes_prefix dst src;
       abi_encode_bytes_copy dst src (FST ops) (SND ops);
       abi_encode_bytes_suffix (FST ops)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, Once compile_abi_encode_child_def,
    abi_encode_bytes_prefix_def, abi_encode_bytes_copy_def, abi_encode_bytes_suffix_def,
    abi_encode_round_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_bytes_trace:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,final) ==>
  ?ops ready copied. abi_encode_bytes_prefix dst src st = (ops,ready) /\
    abi_encode_bytes_copy dst src (FST ops) (SND ops) ready = ((),copied) /\
    abi_encode_bytes_suffix (FST ops) copied = (out,final)
Proof
  simp_tac bool_ss [abi_encode_bytes_phases, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_encode_bytes_prefix dst src st = (ops,ready)` >>
  rename1 `abi_encode_bytes_copy dst src (FST ops) (SND ops) ready = ((),copied)` >>
  qexistsl_tac [`ops`, `ready`, `copied`] >> simp[]
QED

Theorem abi_encode_round_shape:
  abi_encode_round len st = (out,st') ==>
  st'.cs_next_var = st.cs_next_var + 2 /\ st'.cs_next_id = st.cs_next_id + 2 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\ inst_extends st st' /\
  out = Var (STRING #"%" (toString (st.cs_next_var + 1))) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_encode_round_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_encode_bytes_shape:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,st') ==>
  st'.cs_next_var = st.cs_next_var + 8 /\ st'.cs_next_id = st.cs_next_id + 10 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_encode_bytes_copy_shape:
  abi_encode_bytes_copy dst src len lastptr st = ((),st') ==>
  st'.cs_next_var = st.cs_next_var + 1 /\ st'.cs_next_id = st.cs_next_id + 3 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st'
Proof
  simp[abi_encode_bytes_copy_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem abi_encode_bytes_suffix_shape:
  abi_encode_bytes_suffix len st = (out,st') ==>
  st'.cs_next_var = st.cs_next_var + 3 /\ st'.cs_next_id = st.cs_next_id + 3 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st'
Proof
  simp[abi_encode_bytes_suffix_def, abi_encode_round_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED
