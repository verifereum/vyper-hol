Theory bodyPtrPrecompileBuiltinsRecoveryRunner
Ancestors bodyPtrPrecompileBuiltinsECMulRunner bodyPtrPrecompileBuiltinsRecoveryTail
          vyperTypeSystem exprLoweringProps exprLowering emitHelper compileEnv
          exprSimHypsDefs exprSimWordArgs exprSimPrecompiles vyperInterpreter vyperState vyperContext

Theorem recovery_body_pre_shape:
  expr_body_pre cenv cx env (Builtin ann ECRecover args) es ==>
  ann = BaseT AddressT /\
  ?ah av ar aq. args = [ah;av;ar;aq] /\
    expr_type ah = BaseT (BytesT (Fixed 32)) /\
    (expr_type av = BaseT (UintT 8) \/ expr_type av = BaseT (UintT 256) \/
     expr_type av = BaseT (BytesT (Fixed 32))) /\
    (expr_type ar = BaseT (UintT 256) \/ expr_type ar = BaseT (BytesT (Fixed 32))) /\
    (expr_type aq = BaseT (UintT 256) \/ expr_type aq = BaseT (BytesT (Fixed 32)))
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `well_typed_builtin_app _ ECRecover _` mp_tac >>
  simp[well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem recovery_compile_operands:
  compile_expr cenv ty (Builtin ann ECRecover [ah;av;ar;aq]) sa = (vv,sb) ==>
  ?h v r q s1 s2 s3 sm res.
    lower_value compile_expr cenv ty ah sa = (h,s1) /\
    lower_value compile_expr cenv ty av s1 = (v,s2) /\
    lower_value compile_expr cenv ty ar s2 = (r,s3) /\
    lower_value compile_expr cenv ty aq s3 = (q,sm) /\
    compile_ecrecover h v r q sm = (res,sb) /\ vv = StackValue ann res
Proof
  `compile_expr cenv ty (Builtin ann ECRecover [ah;av;ar;aq]) sa =
    compile_builtin_dispatch cenv ann ty ECRecover [ah;av;ar;aq] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `ah` >> simp[names_builtin_def] >>
     Cases_on `av` >> simp[names_builtin_def] >>
     Cases_on `ar` >> simp[names_builtin_def]) >>
  simp[] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `compile_ecrecover vh vv' vr vs' st4` >>
  gvs[as_stack_val_def]
QED
