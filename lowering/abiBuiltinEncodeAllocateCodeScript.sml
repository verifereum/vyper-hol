(* The allocation/address prefix shared by both method-ID choices. *)
Theory abiBuiltinEncodeAllocateCode
Ancestors
  abiBuiltinEncodeCode abiBuiltinAllocation abiDecoderReentry abiDecoderContract
  context compileEnv emitHelper emitHelperProps exprLoweringProps venomInst words list rich_list arithmetic

Definition abi_builtin_encode_allocate_def:
  abi_builtin_encode_allocate outsz data_offset =
    do buf <- compile_alloc_buffer outsz;
       data_ptr <- emit_op ADD [buf.buf_operand;Lit (n2w data_offset)];
       return (buf.buf_operand,data_ptr)
    od
End

Theorem abi_builtin_encode_setup_allocate:
  abi_builtin_encode_setup method_id_opt maxlen =
    do ops <- abi_builtin_encode_allocate
         (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))
         (32+(case method_id_opt of NONE => 0 | SOME _ => 4));
       abi_builtin_encode_method_id method_id_opt (FST ops);
       return ops
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_builtin_encode_setup_def, abi_builtin_encode_allocate_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_builtin_encode_allocate_trace:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) ==>
  ?buf allocated data_ptr.
    compile_alloc_buffer outsz st = (buf,allocated) /\
    emit_op ADD [buf.buf_operand;Lit (n2w data_offset)] allocated = (data_ptr,address_st) /\
    ops = (buf.buf_operand,data_ptr)
Proof
  simp_tac bool_ss [abi_builtin_encode_allocate_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer outsz st = (buf,allocated)` >>
  rename1 `emit_op ADD _ allocated = (data_ptr,address_st)` >>
  qexistsl_tac [`buf`, `allocated`, `data_ptr`] >> simp[]
QED

Theorem abi_builtin_encode_setup_allocate_trace:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) ==>
  ?address_st.
    abi_builtin_encode_allocate
      (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))
      (32+(case method_id_opt of NONE => 0 | SOME _ => 4)) st = (ops,address_st) /\
    abi_builtin_encode_method_id method_id_opt (FST ops) address_st = ((),ready)
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_allocate, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_encode_allocate _ _ st = (ops,address_st)` >>
  qexists_tac `address_st` >> simp[]
QED

Theorem abi_builtin_encode_allocate_shape:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) ==>
  address_st.cs_next_id = st.cs_next_id+2 /\ address_st.cs_next_var = st.cs_next_var+2 /\
  address_st.cs_blocks = st.cs_blocks /\ address_st.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts address_st.cs_current_insts /\ inst_extends st address_st /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st address_st)
Proof
  simp[abi_builtin_encode_allocate_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_builtin_encode_allocate_live:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) ==>
  abi_decoder_operand_live address_st.cs_next_var (FST ops) /\
  abi_decoder_operand_live address_st.cs_next_var (SND ops)
Proof
  strip_tac >> drule abi_builtin_encode_allocate_trace >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `abi_decoder_operand_live address_st.cs_next_var buf.buf_operand` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `allocated.cs_next_var` >> simp[]) >>
  qpat_x_assum `ops = _` (fn th => PURE_REWRITE_TAC [th, pairTheory.FST, pairTheory.SND]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_ALLOCATE_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder allocation code not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeAllocateCode");
