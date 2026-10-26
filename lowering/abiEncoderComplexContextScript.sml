(* Split a real dynamic complex encoder into its three executable CFG phases. *)
Theory abiEncoderComplexContext
Ancestors
  abiEncoderComplexCode abiEncoderComplexPrefix abiEncoderMemberCode abiEncoderAddressReach
  abiDecoderContract fragExec emitHelperProps compileEnv valueEncoding venomState words list arithmetic

Theorem abi_encoder_complex_dynamic_context:
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  ?dyn_ptr prepared ignored middle.
    abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\
    compile_abi_encode_complex_elems dst src infos 0 0 dyn_ptr prepared = (ignored,middle) /\
    emit_op MLOAD [dyn_ptr] middle = (out,end_st) /\
    fn_has_code st prepared func /\ fn_has_code prepared middle func /\ fn_has_code middle end_st func /\
    prepared.cs_next_id = st.cs_next_id+2 /\ prepared.cs_next_var = st.cs_next_var+1 /\
    prepared.cs_next_id <= middle.cs_next_id /\ middle.cs_next_id < end_st.cs_next_id /\
    prepared.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var < end_st.cs_next_var /\
    (prepared.cs_blocks = middle.cs_blocks \/
      !bb. lookup_block middle.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `cs_extends st prepared` by
    (irule cs_extends_same_block >> fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends prepared end_st` by
    (irule cs_extends_trans >> qexists_tac `middle` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `prepared`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`prepared`, `middle`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `middle.cs_next_id < end_st.cs_next_id /\ middle.cs_next_var < end_st.cs_next_var` by decide_tac >>
  qexistsl_tac [`dyn_ptr`, `prepared`, `ignored`, `middle`] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `_ \/ _` mp_tac >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_COMPLEX_CONTEXT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder complex context not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderComplexContext");
