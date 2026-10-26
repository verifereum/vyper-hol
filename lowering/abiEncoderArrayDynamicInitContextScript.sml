(* Exact code boundaries for the two actual dynamic-loop scratch initializers. *)
Theory abiEncoderArrayDynamicInitContext
Ancestors
  abiEncoderArrayTailInitCode abiEncoderArrayScalarCode abiDecoderIndexInit abiDecoderContract
  fragExec compileEnv emitHelperProps venomInst words list rich_list arithmetic

Theorem abi_encode_array_dynamic_init_trace:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) ==>
  ?ip after_index dyn_ptr.
    abi_decode_index_init start = (ip,after_index) /\
    abi_encode_array_tail_init count_op asz after_index = (dyn_ptr,owner_st) /\ ptrs = (ip,dyn_ptr)
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_init_split, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_index_init start = (ip,after_index)` >>
  rename1 `abi_encode_array_tail_init count_op asz after_index = (dyn_ptr,prepared)` >>
  qexistsl_tac [`ip`, `after_index`, `dyn_ptr`] >> asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_init_context:
  abi_encode_array_dynamic_init count_op asz start = (ptrs,owner_st) /\ fn_has_code start owner_st func ==>
  ?ip after_index dyn_ptr.
    abi_decode_index_init start = (ip,after_index) /\
    abi_encode_array_tail_init count_op asz after_index = (dyn_ptr,owner_st) /\ ptrs = (ip,dyn_ptr) /\
    fn_has_code start after_index func /\ fn_has_code after_index owner_st func /\
    after_index.cs_next_var = start.cs_next_var+1 /\ after_index.cs_next_id = start.cs_next_id+2 /\
    owner_st.cs_next_var = start.cs_next_var+3 /\ owner_st.cs_next_id = start.cs_next_id+5
Proof
  strip_tac >> drule abi_encode_array_dynamic_init_trace >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_encode_array_tail_init_shape >> strip_tac >>
  `cs_extends start after_index /\ cs_extends after_index owner_st` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  mp_tac (Q.SPECL [`start`, `after_index`, `owner_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`ip`, `after_index`, `dyn_ptr`] >> asm_simp_tac arith_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_DYNAMIC_INIT_CONTEXT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder dynamic initialization context not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayDynamicInitContext");
