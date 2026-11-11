(* Normalize the exact singleton staging branch, without re-simulating it. *)
Theory bodyIntCallStageCompile
Ancestors exprLowering context compileEnv

Theorem intcall_stage_memory_cons:
  vv_type vv = ty ==>
  compile_stage_intcall_args ce (vv::vals) (F::flags) (ty::tys) =
    do op <- unwrap_value ce vv;
       buf <- compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty));
       compile_store_memory ce op buf.buf_operand ty ty;
       rest <- compile_stage_intcall_args ce vals flags tys;
       return (buf.buf_operand::rest)
    od
Proof
  strip_tac >> simp[compile_stage_intcall_args_def] >>
  `((case ty of BaseT (BytesT (Dynamic _)) => T
       | BaseT (StringT _) => T | _ => F) = is_bytestring_type ty)` by
    (Cases_on `ty` >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
     rename1 `BytesT sz` >> Cases_on `sz` >> simp[is_bytestring_type_def]) >>
  simp[compile_store_memory_def, comp_bind_def, comp_return_def, FUN_EQ_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `is_word_type ty` >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `is_bytestring_type ty` >> simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]
QED
