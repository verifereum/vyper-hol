Theory bodyPtrPopGuardNormalization
Ancestors
  bodyPtrPopGlobalLoweringInputs bodyPtrPopGlobalLegality exprLowering
  exprCallBounds vyperAST

Theorem pop_empty_intcall_callback_independent:
  compile_call f ce rt ty (IntCall fid) [] d st =
  compile_call g ce rt ty (IntCall fid) [] d st
Proof
  simp[compile_call_def, compile_multi_vvs_def]
QED

Theorem pop_global_replace_guard:
  expr_child_callback (base_assignment_target_size pop_global_target + 259)
    compile_expr pop_global_package_env (BaseT (UintT 256))
      (Call (BaseT (UintT 256)) (IntCall (NONE,"replace")) [] NONE) sc =
  compile_call compile_expr pop_global_package_env
    (BaseT (UintT 256)) (BaseT (UintT 256))
    (IntCall (NONE,"replace")) [] NONE sc
Proof
  simp[expr_child_callback_def, pop_global_target_def] >>
  simp[Once compile_expr_def] >>
  simp[expr_type_def, compile_call_def, compile_multi_vvs_def]
QED
