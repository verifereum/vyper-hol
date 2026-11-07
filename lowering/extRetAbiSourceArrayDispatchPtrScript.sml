(* Actual AbiDynArray F dispatch, factored only at its finite phases. *)
Theory extRetAbiSourceArrayDispatchPtr
Ancestors
  extRetAbiSourceArrayStaticCountedPtr extRetScratchInitPtr extRetAbiArrayInitPtr
  abiEncoder emitHelper compileEnv fragExec words pair

Definition source_array_static_prefix_def:
  source_array_static_prefix dst src =
    do parent <- compile_alloc_buffer 32;
       emit_void MSTORE [parent.buf_operand; Lit 0w];
       count <- emit_op MLOAD [src];
       emit_void MSTORE [dst; count];
       return (parent.buf_operand,count)
    od
End

Definition source_array_static_suffix_def:
  source_array_static_suffix parent encoded =
    do old <- emit_op MLOAD [parent];
       total <- emit_op ADD [old; encoded];
       emit_void MSTORE [parent; total];
       emit_op MLOAD [parent]
    od
End

Theorem compile_abi_encode_dyn_static_phases:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz F) =
    do ops <- source_array_static_prefix dst src;
       encoded <- compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops);
       source_array_static_suffix (FST ops) encoded
    od
Proof
  simp[Once compile_abi_encode_child_def,
       source_array_static_prefix_def, source_array_static_suffix_def,
       comp_ignore_bind_def, comp_bind_assoc] >>
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> ntac 4 (pairarg_tac >> simp[])
QED

Theorem compile_abi_encode_dyn_static_trace:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz F) sa = (out,se) ==>
  ?ops sp encoded sl.
    source_array_static_prefix dst src sa = (ops,sp) /\
    compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops) sp = (encoded,sl) /\
    source_array_static_suffix (FST ops) encoded sl = (out,se)
Proof
  simp[compile_abi_encode_dyn_static_phases, comp_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> rpt strip_tac >> metis_tac[]
QED

Theorem source_array_static_prefix_trace:
  source_array_static_prefix dst src sa = (ops,sp) ==>
  ?buf s1 s2 count s3.
    compile_alloc_buffer 32 sa = (buf,s1) /\
    emit_void MSTORE [buf.buf_operand; Lit 0w] s1 = ((),s2) /\
    emit_op MLOAD [src] s2 = (count,s3) /\
    emit_void MSTORE [dst; count] s3 = ((),sp) /\
    ops = (buf.buf_operand,count)
Proof
  simp[source_array_static_prefix_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem source_array_static_prefix_frontier:
  source_array_static_prefix dst src sa = (ops,sp) ==>
  FST ops = Var (STRING #"%" (toString sa.cs_next_var)) /\
  SND ops = Var (STRING #"%" (toString (sa.cs_next_var+1))) /\
  sp.cs_next_id = sa.cs_next_id+4 /\ sp.cs_next_var = sa.cs_next_var+2 /\
  sp.cs_current_bb = sa.cs_current_bb /\ sp.cs_blocks = sa.cs_blocks
Proof
  simp[source_array_static_prefix_def, contextTheory.compile_alloc_buffer_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED
