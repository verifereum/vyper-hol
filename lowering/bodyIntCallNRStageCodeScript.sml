(* Current interleaved staging compiler endpoints. *)
Theory bodyIntCallNRStageCode
Ancestors
  exprLowering exprLoweringProps fragExec

Theorem intcall_stage_current_stack_parts:
  compile_stage_intcall_args cfn ce (e::es) (T::flags) (ty::tys) sa = (ops,sb) ==>
  ?vv s1 op s2 rest.
    cfn ce (expr_type e) e sa = (vv,s1) /\
    unwrap_value ce vv s1 = (op,s2) /\
    compile_stage_intcall_args cfn ce es flags tys s2 = (rest,sb) /\
    ops = op::rest
Proof
  Cases_on `cfn ce (expr_type e) e sa` >>
  rename1 `cfn ce (expr_type e) e sa = (vv,s1)` >>
  Cases_on `unwrap_value ce vv s1` >>
  rename1 `unwrap_value ce vv s1 = (op,s2)` >>
  Cases_on `compile_stage_intcall_args cfn ce es flags tys s2` >>
  simp[compile_stage_intcall_args_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem intcall_stage_current_memory_parts:
  compile_stage_intcall_args cfn ce (e::es) (F::flags) (ty::tys) sa = (ops,sb) ==>
  ?vv s1 buf s2 op s3 s4 rest.
    cfn ce (expr_type e) e sa = (vv,s1) /\
    compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) s1 = (buf,s2) /\
    unwrap_value ce vv s2 = (op,s3) /\
    (if is_word_type ty then emit_void MSTORE [buf.buf_operand;op] s3 = ((),s4)
     else if is_bytestring_type ty then
       compile_store_bytestring op buf.buf_operand s3 = ((),s4)
     else compile_store_memory ce op buf.buf_operand ty (vv_type vv) s3 = ((),s4)) /\
    compile_stage_intcall_args cfn ce es flags tys s4 = (rest,sb) /\
    ops = buf.buf_operand::rest
Proof
  Cases_on `cfn ce (expr_type e) e sa` >>
  rename1 `cfn ce (expr_type e) e sa = (vv,s1)` >>
  Cases_on `compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) s1` >>
  rename1 `compile_alloc_buffer _ s1 = (buf,s2)` >>
  Cases_on `unwrap_value ce vv s2` >>
  rename1 `unwrap_value ce vv s2 = (op,s3)` >>
  Cases_on `ty` >>
  gvs[compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt`) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  fs[compile_stage_intcall_args_def, compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_return_def, compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.is_bytestring_type_def, compileEnvTheory.is_word_type_def] >>
  rpt (pairarg_tac >> fs[compileEnvTheory.comp_bind_def,
                        compileEnvTheory.comp_return_def,
                        compileEnvTheory.comp_ignore_bind_def]) >> rpt strip_tac >>
  metis_tac[pairTheory.PAIR]
QED

(* Code extraction needs no staging-specific duplicate of generic algebra:
   use fragExec.fn_has_code_split (or fn_has_code_mid) at the endpoints above,
   obtaining cs_extends from ci_mono_def and composing by ci_mono_trans.
   In particular no monotonicity of the arbitrary cfn is assumed here;
   consumers supply its actual compilation interval evidence. *)
