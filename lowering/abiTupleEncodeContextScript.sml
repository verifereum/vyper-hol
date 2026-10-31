(* Actual tuple staging and encoder fragments inherit outer code containment. *)
Theory abiTupleEncodeContext
Ancestors
  abiTupleEncodePrepare abiTupleEncodeCounters abiBuiltinEncodeWord fragExec compileEnv words
  list arithmetic

Theorem abi_tuple_encode_context:
  compile_alloc_buffer n st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  lower_abi_encode ensure method_id_opt source_buf.buf_operand info maxlen staged = (out,final) /\
  fn_has_code st final func ==>
  fn_has_code st staged func /\ fn_has_code staged final func /\
  st.cs_next_var <= staged.cs_next_var /\ staged.cs_next_var <= final.cs_next_var /\
  st.cs_next_id < staged.cs_next_id /\ staged.cs_next_id <= final.cs_next_id /\
  staged.cs_blocks = st.cs_blocks /\
  staged.cs_next_id = st.cs_next_id+1+abi_tuple_encode_inst_count ce (MAP SND xs)
Proof
  strip_tac >> drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule_all abi_tuple_encode_stage_id >> strip_tac >>
  drule lower_abi_encode_extends >> strip_tac >>
  `cs_extends st staged` by
    (irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  drule_all fn_has_code_split >> strip_tac >> asm_simp_tac bool_ss [] >> decide_tac
QED
