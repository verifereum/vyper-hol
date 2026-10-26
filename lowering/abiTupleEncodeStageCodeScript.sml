(* Allocation plus all tuple writes stays in its actual containing block. *)
Theory abiTupleEncodeStageCode
Ancestors
  abiTupleEncodeCode abiTupleProps abiBuiltinAllocation abiDecoderReentry
  compileEnv context emitHelper emitHelperProps exprLoweringProps
  venomInst words list rich_list arithmetic

Theorem abi_tuple_encode_alloc_shape:
  compile_alloc_buffer n st = (buf,allocated) ==>
  allocated.cs_next_var = st.cs_next_var+1 /\ allocated.cs_next_id = st.cs_next_id+1 /\
  allocated.cs_blocks = st.cs_blocks /\ allocated.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts allocated.cs_current_insts /\ inst_extends st allocated /\
  abi_decoder_operand_live allocated.cs_next_var buf.buf_operand /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st allocated)
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, abi_decoder_operand_live_def,
    abi_decoder_older_vars_def, DROP_LENGTH_APPEND, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_tuple_encode_stage_shape:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) ==>
  staged.cs_next_var = st.cs_next_var+1+LENGTH xs /\ st.cs_next_id < staged.cs_next_id /\
  staged.cs_blocks = st.cs_blocks /\ staged.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts staged.cs_current_insts /\ inst_extends st staged /\
  allocated.cs_next_var <= staged.cs_next_var /\ abi_decoder_operand_live staged.cs_next_var buf.buf_operand /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st staged)
Proof
  strip_tac >> drule abi_tuple_encode_alloc_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `inst_extends st staged` by
    (irule inst_extends_trans >> qexists_tac `allocated` >> asm_simp_tac bool_ss []) >>
  `isPREFIX st.cs_current_insts staged.cs_current_insts` by
    (irule isPREFIX_TRANS >> qexists_tac `allocated.cs_current_insts` >> asm_simp_tac bool_ss []) >>
  `emitted_insts st staged = emitted_insts st allocated ++ emitted_insts allocated staged` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `allocated.cs_next_var <= staged.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live staged.cs_next_var buf.buf_operand` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `allocated.cs_next_var` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_STAGE_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple staging compiler shape not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeStageCode");
