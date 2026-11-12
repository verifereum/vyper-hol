(* Normalize the exact singleton staging branch, without re-simulating it. *)
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
  cheat
QED
