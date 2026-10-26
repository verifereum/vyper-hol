(* Actual complex encoder phases, including the parent's private tail cursor. *)
Theory abiEncoderComplexCode
Ancestors
  abiEncoder compileEnv emitHelper venomInst list words arithmetic
Libs monadsyntax

Definition abi_encode_complex_prefix_def:
  abi_encode_complex_prefix infos =
    do cursor <- compile_alloc_buffer 32;
       emit_void MSTORE [cursor.buf_operand;
         Lit (n2w (SUM (MAP (\(_,abi_sz:num,_,_). abi_sz) infos)))];
       return cursor.buf_operand
    od
End

Theorem abi_encoder_complex_static_trace:
  ~EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) ==>
  ?ignored. compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st = (ignored,end_st) /\
    out = Lit (n2w (SUM (MAP (\(_,abi_sz:num,_,_). abi_sz) infos)))
Proof
  Cases_on `infos`
  >- (simp[Once compile_abi_encode_child_def, comp_return_def] >>
      simp[Once compile_abi_encode_child_def, comp_return_def]) >>
  rename1 `compile_abi_encode_to_buf dst src (AbiComplex (entry::rest)) st = (out,end_st)` >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [Once compile_abi_encode_child_def, LET_THM,
    comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,end_st)` >>
  qexists_tac `ignored` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_complex_dynamic_phases:
  EXISTS (\(_,_,_,dyn). dyn) infos ==>
  compile_abi_encode_to_buf dst src (AbiComplex infos) =
    do dyn_ptr <- abi_encode_complex_prefix infos;
       compile_abi_encode_complex_elems dst src infos 0 0 dyn_ptr;
       emit_op MLOAD [dyn_ptr]
    od
Proof
  Cases_on `infos` >- simp[] >> strip_tac >>
  asm_simp_tac bool_ss [FUN_EQ_THM, Once compile_abi_encode_child_def,
    abi_encode_complex_prefix_def, LET_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encoder_complex_dynamic_trace:
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) ==>
  ?dyn_ptr prepared ignored middle.
    abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\
    compile_abi_encode_complex_elems dst src infos 0 0 dyn_ptr prepared = (ignored,middle) /\
    emit_op MLOAD [dyn_ptr] middle = (out,end_st)
Proof
  strip_tac >> drule abi_encoder_complex_dynamic_phases >> disch_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_encode_complex_prefix infos st = (dyn_ptr,prepared)` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,middle)` >>
  qexistsl_tac [`dyn_ptr`, `prepared`, `ignored`, `middle`] >> asm_simp_tac bool_ss []
QED
