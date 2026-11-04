(* Exact setup, recursive body and length-store phases of lower_abi_encode.
   These equations describe the actual compiler action, including method IDs. *)
Theory abiBuiltinEncodeCode
Ancestors
  builtinAbi abiEncoder context compileEnv emitHelper emitHelperProps exprLoweringProps
  list rich_list arithmetic words venomInst

Definition abi_builtin_encode_method_id_def:
  abi_builtin_encode_method_id method_id_opt buf =
    case method_id_opt of
      NONE => return ()
    | SOME mid =>
        do mid_ptr <- emit_op ADD [buf; Lit 32w];
           emit_void MSTORE [mid_ptr; Lit (mid << 224)]
        od
End

Definition abi_builtin_encode_setup_def:
  abi_builtin_encode_setup method_id_opt maxlen =
    let mid_size = case method_id_opt of SOME _ => 4 | NONE => 0 in
    do buf <- compile_alloc_buffer (maxlen + 32 + mid_size);
       data_ptr <- emit_op ADD [buf.buf_operand; Lit (n2w (32 + mid_size))];
       abi_builtin_encode_method_id method_id_opt buf.buf_operand;
       return (buf.buf_operand,data_ptr)
    od
End

Definition abi_builtin_encode_finish_def:
  abi_builtin_encode_finish buf encoded_len mid_size =
    if mid_size > 0 then
      do total_len <- emit_op ADD [encoded_len; Lit (n2w mid_size)];
         emit_void MSTORE [buf; total_len]
      od
    else emit_void MSTORE [buf; encoded_len]
End

Theorem lower_abi_encode_phases:
  lower_abi_encode ensure method_id_opt src info maxlen =
    do ops <- abi_builtin_encode_setup method_id_opt maxlen;
       len <- compile_abi_encode_to_buf (SND ops) src info;
       abi_builtin_encode_finish (FST ops) len
         (case method_id_opt of SOME _ => 4 | NONE => 0);
       return (FST ops)
    od
Proof
  Cases_on `method_id_opt` >>
  simp_tac (srw_ss()) [FUN_EQ_THM, lower_abi_encode_def, abi_builtin_encode_setup_def,
    abi_builtin_encode_method_id_def, abi_builtin_encode_finish_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem lower_abi_encode_trace:
  lower_abi_encode ensure method_id_opt src info maxlen st = (out,final) ==>
  ?ops ready len body_end.
    abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) /\
    compile_abi_encode_to_buf (SND ops) src info ready = (len,body_end) /\
    abi_builtin_encode_finish (FST ops) len
      (case method_id_opt of SOME _ => 4 | NONE => 0) body_end = ((),final) /\
    out = FST ops
Proof
  simp_tac bool_ss [lower_abi_encode_phases, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready)` >>
  rename1 `compile_abi_encode_to_buf (SND ops) src info ready = (len,body_end)` >>
  qexistsl_tac [`ops`, `ready`, `len`, `body_end`] >> simp[]
QED

Theorem abi_builtin_encode_setup_trace:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) ==>
  ?buf allocated data_ptr address_st.
    compile_alloc_buffer (maxlen + 32 + (case method_id_opt of SOME _ => 4 | NONE => 0))
      st = (buf,allocated) /\
    emit_op ADD [buf.buf_operand; Lit (n2w (32 +
      (case method_id_opt of SOME _ => 4 | NONE => 0)))] allocated = (data_ptr,address_st) /\
    abi_builtin_encode_method_id method_id_opt buf.buf_operand address_st = ((),ready) /\
    ops = (buf.buf_operand,data_ptr)
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer _ st = (buf,allocated)` >>
  rename1 `emit_op ADD _ allocated = (data_ptr,address_st)` >>
  qexistsl_tac [`buf`, `allocated`, `data_ptr`, `address_st`] >> simp[]
QED

Theorem abi_builtin_encode_setup_shape:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) ==>
  ready.cs_next_id = st.cs_next_id + (case method_id_opt of NONE => 2 | SOME _ => 4) /\
  ready.cs_next_var = st.cs_next_var + (case method_id_opt of NONE => 2 | SOME _ => 3) /\
  ready.cs_blocks = st.cs_blocks /\ ready.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts ready.cs_current_insts /\ inst_extends st ready /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st ready)
Proof
  Cases_on `method_id_opt` >>
  simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_builtin_encode_finish_shape:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) ==>
  final.cs_next_id = st.cs_next_id + (if mid_size > 0 then 2 else 1) /\
  final.cs_next_var = st.cs_next_var + (if mid_size > 0 then 1 else 0) /\
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts final.cs_current_insts /\ inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final)
Proof
  Cases_on `mid_size > 0` >>
  simp[abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED
