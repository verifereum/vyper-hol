(* Predict the tuple producer's encoder-entry allocation site. Every slot
   emits ADD and a write, including raw MCOPY for zero-sized complex slots. *)
Theory abiTupleEncodeCounters
Ancestors
  abiTupleEncodePrepare abiTupleProps compileEnv context exprLowering
  emitHelper emitHelperProps exprLoweringProps words list arithmetic

Definition abi_tuple_encode_inst_count_def:
  abi_tuple_encode_inst_count (ce:compile_env) (tys:type list) =
    SUM (MAP (\ty. 2) tys)
End

Theorem abi_tuple_encode_inst_count_length:
  abi_tuple_encode_inst_count ce tys = 2 * LENGTH tys
Proof
  Induct_on `tys` >> gvs[abi_tuple_encode_inst_count_def] >> decide_tac
QED

Theorem abi_tuple_encode_slot_id:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) ==>
  final.cs_next_id = st.cs_next_id+2
Proof
  Cases_on `is_word_type ty` >>
  asm_simp_tac (srw_ss()) [compile_abi_tuple_slot_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_tuple_encode_store_id:
  !xs ce buf off st final. compile_store_abi_tuple ce buf off xs st = ((),final) ==>
    final.cs_next_id = st.cs_next_id+abi_tuple_encode_inst_count ce (MAP SND xs)
Proof
  Induct >- simp[compile_store_abi_tuple_def, comp_return_def, abi_tuple_encode_inst_count_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> drule abi_tuple_encode_slot_id >> strip_tac >>
  first_x_assum drule >> asm_simp_tac bool_ss [abi_tuple_encode_inst_count_def, MAP, SUM, ADD_ASSOC]
QED

Theorem abi_tuple_encode_stage_id:
  compile_alloc_buffer n st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) ==>
  staged.cs_next_id = st.cs_next_id+1+abi_tuple_encode_inst_count ce (MAP SND xs)
Proof
  strip_tac >> drule abi_tuple_encode_alloc_shape >> strip_tac >>
  drule abi_tuple_encode_store_id >> asm_simp_tac bool_ss []
QED
