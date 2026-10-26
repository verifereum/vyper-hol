(* The actual primitive AbiEncode staging is one ALLOCA and one MSTORE. *)
Theory abiBuiltinEncodeWordStageCode
Ancestors
  abiBuiltinAllocation abiDecoderReentry exprLowering context compileEnv emitHelper emitHelperProps
  exprLoweringProps venomInst words list rich_list arithmetic

Theorem abi_builtin_encode_word_info:
  is_word_type ty ==>
  type_memory_bytes ce ty = 32 /\ type_to_abi_enc_info sf ce ty = AbiCopy 32
Proof
  Cases_on `ty` >>
  FIRST [rename1 `BaseT bt` >> Cases_on `bt` >>
    FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
    simp[is_word_type_def, type_memory_bytes_def, Once type_to_abi_enc_info_def],
    simp[is_word_type_def, type_memory_bytes_def, Once type_to_abi_enc_info_def]]
QED

Theorem abi_builtin_encode_word_stage_shape:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) ==>
  staged.cs_next_id = st.cs_next_id+2 /\ staged.cs_next_var = st.cs_next_var+1 /\
  staged.cs_blocks = st.cs_blocks /\ staged.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts staged.cs_current_insts /\ inst_extends st staged /\
  abi_decoder_operand_live staged.cs_next_var buf.buf_operand /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st staged)
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_WORD_STAGE_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin word staging code not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeWordStageCode");
