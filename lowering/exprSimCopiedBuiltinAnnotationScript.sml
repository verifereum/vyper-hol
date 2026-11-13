Theory exprSimCopiedBuiltinAnnotation
Ancestors
  exprSimCopiedAnnotation exprLowering context vyperAST

Theorem builtin_result_type:
  vv_type (FST (compile_builtin_dispatch_body cfn ce rt ty bi args st)) = rt
Proof
  (Cases_on `bi` >> simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[stack_result_type, ptr_result_type, literal_result_type, vv_type_def] >>
  rpt (IF_CASES_TAC >> simp[stack_result_type, ptr_result_type, literal_result_type, vv_type_def]))
  >~ [`compile_keccak256_word p s`]
  >- (Cases_on `expr_type (HD args)` >> simp[stack_result_type] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> simp[stack_result_type] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[stack_result_type])
  >~ [`compile_sha256_word p s`]
  >- (Cases_on `expr_type (HD args)` >> simp[stack_result_type] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> simp[stack_result_type] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[stack_result_type])
  >- (Cases_on `o'` >> simp[ptr_result_type])
  >- (Cases_on `HD (TL args)` >> simp[stack_result_type] >>
      rename1 `Builtin a inner es` >> Cases_on `inner` >>
      simp[stack_result_type] >> rpt (pairarg_tac >> gvs[]) >>
      simp[stack_result_type] >> IF_CASES_TAC >> simp[stack_result_type]) >>
  Cases_on `method_id_literal (HD args)` >>
  simp[ptr_result_type, literal_result_type, stack_result_type]
QED
