(* The actual dynamic-array initializer allocates and stores the computed head length. *)
Theory abiEncoderArrayTailInitCode
Ancestors
  abiEncoderArrayCode abiDecoderIndexInit compileEnv context emitHelperProps exprLoweringProps
  emitHelper venomInst words list rich_list arithmetic
Libs monadsyntax

Definition abi_encode_array_tail_init_def:
  abi_encode_array_tail_init count_op asz =
    do buf <- compile_alloc_buffer 32;
       offset <- emit_op MUL [count_op;Lit (n2w asz)];
       emit_void MSTORE [buf.buf_operand;offset];
       return buf.buf_operand
    od
End

Theorem abi_encode_array_dynamic_init_split:
  abi_encode_array_dynamic_init count_op asz =
    do ip <- abi_decode_index_init;
       dyn_ptr <- abi_encode_array_tail_init count_op asz;
       return (ip,dyn_ptr)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_encode_array_dynamic_init_def, abi_encode_array_tail_init_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_array_tail_init_trace:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') ==>
  ?buf c1 offset c2.
    compile_alloc_buffer 32 st = (buf,c1) /\ dyn_ptr = buf.buf_operand /\
    emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2) /\
    emit_void MSTORE [buf.buf_operand;offset] c2 = ((),st')
Proof
  simp_tac bool_ss [abi_encode_array_tail_init_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer 32 st = (buf,c1)` >>
  rename1 `emit_op MUL [count_op;Lit (n2w asz)] c1 = (offset,c2)` >>
  qexistsl_tac [`buf`, `c1`, `offset`, `c2`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_tail_init_shape:
  abi_encode_array_tail_init count_op asz st = (dyn_ptr,st') ==>
  dyn_ptr = Var (STRING #"%" (toString st.cs_next_var)) /\
  st'.cs_next_var = st.cs_next_var+2 /\ st'.cs_next_id = st.cs_next_id+3 /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  simp[abi_encode_array_tail_init_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_TAIL_INIT_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder tail initialization code not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayTailInitCode");
