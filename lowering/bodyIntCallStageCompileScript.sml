(* Normalize the staging branches of one argument and split them into their
   compiler steps, without re-simulating them. *)
Theory bodyIntCallStageCompile
Ancestors exprLowering context compileEnv

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_stage_memory_cons:
  compile_stage_intcall_args cfn ce (e::es) (F::flags) (ty::tys) =
    do vv <- cfn ce (expr_type e) e;
       buf <- compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty));
       op <- unwrap_value ce vv;
       compile_store_memory ce op buf.buf_operand ty (vv_type vv);
       rest <- compile_stage_intcall_args cfn ce es flags tys;
       return (buf.buf_operand::rest)
    od
Proof
  `(case ty of BaseT (BytesT (Dynamic _)) => T
      | BaseT (StringT _) => T | _ => F) = is_bytestring_type ty` by
    (Cases_on `ty` >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def] >>
     rename1 `BytesT sz` >> Cases_on `sz` >> simp[is_bytestring_type_def]) >>
  `!src dst. comp_ignore_bind (compile_store_bytestring src dst) (comp_return ()) =
     compile_store_bytestring src dst` by
    (rw[FUN_EQ_THM, comp_ignore_bind_def, comp_bind_def, comp_return_def,
        pairTheory.UNCURRY] >>
     metis_tac[pairTheory.PAIR, oneTheory.one]) >>
  simp[compile_stage_intcall_args_def, compile_store_memory_def]
QED

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_stage_word_parts:
  compile_stage_intcall_args cfn ce (e::es) (T::flags) (ty::tys) sa = (ops,sn) ==>
  ?vv s1 op sm rest.
    cfn ce (expr_type e) e sa = (vv,s1) /\
    unwrap_value ce vv s1 = (op,sm) /\
    compile_stage_intcall_args cfn ce es flags tys sm = (rest,sn) /\
    ops = op::rest
Proof
  rw[compile_stage_intcall_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem intcall_stage_memory_parts:
  compile_stage_intcall_args cfn ce (e::es) (F::flags) (ty::tys) sa = (ops,sn) ==>
  ?vv s1 buf s2 op s3 s4 rest.
    cfn ce (expr_type e) e sa = (vv,s1) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) s1 = (buf,s2) /\
    unwrap_value ce vv s2 = (op,s3) /\
    compile_store_memory ce op buf.buf_operand ty (vv_type vv) s3 = ((),s4) /\
    compile_stage_intcall_args cfn ce es flags tys s4 = (rest,sn) /\
    ops = buf.buf_operand::rest
Proof
  rw[intcall_stage_memory_cons, comp_bind_def, comp_ignore_bind_def,
     comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[oneTheory.one]
QED
