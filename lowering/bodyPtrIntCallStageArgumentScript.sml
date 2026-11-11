Theory bodyPtrIntCallStageArgument
Ancestors exprLowering compileEnv context list

(* Expose precisely the head segment, without executing the recursive tail.
   Destination and source annotations remain distinct in the typed store. *)
Theorem intcall_stage_memory_cons_decompose:
  compile_stage_intcall_args ce (vv::vals) (F::flags) (ty::tys) sa =
    (ops,sb) <=>
  ?src sm allocation sn su rest.
    unwrap_value ce vv sa = (src,sm) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm =
      (allocation,sn) /\
    (if is_word_type ty then
       emit_void MSTORE [allocation.buf_operand;src]
     else if (case ty of BaseT (BytesT (Dynamic _)) => T
                        | BaseT (StringT _) => T | _ => F) then
       do compile_store_bytestring src allocation.buf_operand;
          return () od
     else compile_store_memory ce src allocation.buf_operand ty (vv_type vv)) sn =
      ((),su) /\
    compile_stage_intcall_args ce vals flags tys su = (rest,sb) /\
    ops = allocation.buf_operand::rest
Proof
  Cases_on `unwrap_value ce vv sa` >>
  rename1 `unwrap_value ce vv sa = (src,sm)` >>
  Cases_on `compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm` >>
  simp[Once compile_stage_intcall_args_def, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED
