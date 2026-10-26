(* Split the actual word dispatcher fragment at its constructed source. *)
Theory abiBuiltinEncodeWordContext
Ancestors
  abiBuiltinEncodeWordStageCode abiBuiltinEncodeAppend fragExec compileEnv
  words list arithmetic

Theorem abi_builtin_encode_word_context:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
  lower_abi_encode ensure method_id_opt buf.buf_operand info maxlen staged = (out,final) /\
  fn_has_code st final func ==>
  fn_has_code st staged func /\ fn_has_code staged final func /\
  staged.cs_next_var <= final.cs_next_var /\ staged.cs_next_id <= final.cs_next_id /\
  staged.cs_blocks = st.cs_blocks /\ staged.cs_next_var = st.cs_next_var+1 /\
  staged.cs_next_id = st.cs_next_id+2
Proof
  strip_tac >> drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule lower_abi_encode_extends >> strip_tac >>
  `cs_extends st staged` by
    (irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  drule_all fn_has_code_split >> strip_tac >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_WORD_CONTEXT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin word context not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeWordContext");
