Theory bodyPtrBytestringBuiltinsSliceGuardAbort
Ancestors
  bodyPtrBytestringBuiltinsSliceGuardFrame bodyPtrBytestringBuiltinsBounds
  exprLowering builtinBytes builtinStrings compileEnv emitHelper
  bodyPtrBytestringBuiltinsSliceDispatch exprSimConvert exprBopLowering
  bodyPtrBytestringBuiltinsSliceGuardFixture fragExec venomExecSemantics venomState venomInst exprLoweringProps list

Theorem slice_guard_eval_exception:
  !cx st. eval_expr cx slice_guard_expr st =
    (INR (Error (RuntimeError "Div0")), st)
Proof
  rpt gen_tac >> EVAL_TAC >> simp[vyperStateTheory.return_def]
QED

Theorem slice_guard_literal_prefix:
  (!cenv ty sa. lower_value compile_expr cenv ty
    (Literal (BaseT (UintT 256)) (IntL 0)) sa = (Lit 0w,sa)) /\
  (!cenv ty sa. lower_value compile_expr cenv ty
    (Literal (BaseT (UintT 256)) (IntL 1)) sa = (Lit 1w,sa))
Proof
  conj_tac >> rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem slice_guard_compile_prefix:
  compile_expr order_ptr_env ty slice_guard_expr sa = (vv,sb) ==>
  ?out data s3 addr s4.
    compile_slice_out_buf 64 sa = ((out,data),s3) /\
    lower_value compile_expr order_ptr_env ty
      (extcode_addr_expr slice_guard_source) s3 = (addr,s4) /\
    as_ptr_val (BaseT (BytesT (Dynamic 1))) LocMemory
      (compile_slice_extcode addr (Lit 0w) (Lit 1w) out data s4) = (vv,sb)
Proof
  simp[slice_guard_expr_def] >> strip_tac >>
  drule_at Any slice_extcode_compile_cut >>
  (impl_tac >- EVAL_TAC) >>
  simp[slice_guard_literal_prefix] >>
  `type_memory_bytes order_ptr_env (BaseT (BytesT (Dynamic 1))) = 64` by EVAL_TAC >>
  simp[]
QED


Theorem slice_guard_address_cut:
  lower_value compile_expr order_ptr_env ty
    (extcode_addr_expr slice_guard_source) sa = (op,sb) ==>
  ?x sm. compile_binop Div (Lit 1w) (Lit 0w) (BaseT (UintT 256)) NONE NONE sa = (x,sm) /\
    compile_type_convert x (mk_convert_op (BaseT (UintT 256)) (BaseT AddressT)) sm = (op,sb)
Proof
  simp[slice_guard_source_def, extcode_addr_expr_def] >> strip_tac >>
  drule_at Any lower_value_convert >>
  (impl_tac >- EVAL_TAC) >> strip_tac >>
  drule lower_value_bop >> (impl_tac >- EVAL_TAC) >>
  simp[slice_guard_literal_prefix] >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >> metis_tac[]
QED

Theorem slice_guard_division_emission:
  compile_binop Div (Lit 1w) (Lit 0w) (BaseT (UintT 256)) NONE NONE sa = (x,sb) ==>
  ?z s1 nz s2 s3.
    emit_op ISZERO [Lit 0w] sa = (z,s1) /\
    emit_op ISZERO [z] s1 = (nz,s2) /\
    emit_void ASSERT [nz] s2 = ((),s3) /\
    emit_op venomInst$Div [Lit 1w; Lit 0w] s3 = (x,sb)
Proof
  simp[compile_binop_def, compile_safe_div_def,
       compileEnvTheory.is_decimal_type_def, compileEnvTheory.is_signed_type_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

