Theory exprSimCopiedAnnotation
Ancestors
  exprLowering loweringPosts vyperAST compileEnv valueEncoding context combin

Theorem literal_result_type:
  vv_type (FST (compile_literal_vv ty l st)) = ty
Proof
  Cases_on `l` >>
  TRY (rename1 `BoolL b` >> Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def, vv_type_def] >> NO_TAC) >>
  simp[compile_literal_vv_def, comp_return_def, comp_bind_def, comp_ignore_bind_def, vv_type_def] >>
  rpt (CASE_TAC >> simp[compile_literal_vv_def, comp_return_def, comp_bind_def, comp_ignore_bind_def, vv_type_def]) >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_type_def]
QED

Theorem name_result_type:
  vv_type (FST (compile_name_vv ce ty id st)) = ty
Proof
  simp[compile_name_vv_def] >>
  rpt CASE_TAC >> simp[comp_return_def, comp_bind_def, comp_ignore_bind_def, vv_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_type_def]
QED

Theorem attribute_result_type:
  vv_type (FST (compile_attribute cfn ce rt ty e fld st)) = rt
Proof
  simp[compile_attribute_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_type_def]
QED

Theorem subscript_result_type:
  vv_type (FST (compile_subscript cfn ce rt ty e idx st)) = rt
Proof
  simp[compile_subscript_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `place_type ce e` >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_type_def] >>
  rename1 `type_CASE bt _ _ _ _ _ _` >> Cases_on `bt` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[vv_type_def]
QED

Theorem stack_result_type:
  vv_type (FST (as_stack_val ty p)) = ty
Proof
  Cases_on `p` >> simp[as_stack_val_def, vv_type_def]
QED

Theorem ptr_result_type:
  vv_type (FST (as_ptr_val ty loc p)) = ty
Proof
  Cases_on `p` >> simp[as_ptr_val_def, vv_type_def]
QED


Theorem addmod_names_result_type[local]:
  vv_type (FST (compile_addmod_names ce rt aty a bty b mty m st)) = rt
Proof
  simp[compile_addmod_names_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[stack_result_type]
QED

Theorem mulmod_names_result_type[local]:
  vv_type (FST (compile_mulmod_names ce rt aty a bty b mty m st)) = rt
Proof
  simp[compile_mulmod_names_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[stack_result_type]
QED

Theorem powmod_names_result_type[local]:
  vv_type (FST (compile_powmod256_names ce rt aty a bty b st)) = rt
Proof
  simp[compile_powmod256_names_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[stack_result_type]
QED

Theorem type_builtin_result_type[local]:
  vv_type (FST (compile_type_builtin_dispatch_body cfn ce rt ty tb dest args st)) = rt
Proof
  Cases_on `tb` >> simp[compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[stack_result_type, ptr_result_type, vv_type_def] >>
  rpt (IF_CASES_TAC >> simp[stack_result_type, ptr_result_type, vv_type_def]) >>
  Cases_on `dest` >> simp[stack_result_type]
QED

Theorem call_result_type[local]:
  vv_type (FST (compile_call cfn ce rt ty tgt args drv st)) =
    (case tgt of IntCall fid => ce.ce_func_return_type (nsid_to_string fid)
               | _ => rt)
Proof
  Cases_on `tgt` >> TRY (PairCases_on `p`) >> simp[compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (IF_CASES_TAC >> simp[vv_type_def, stack_result_type]) >>
  TRY (Cases_on `return_buf` >> simp[vv_type_def] >>
       rpt (pairarg_tac >> gvs[]) >> simp[vv_type_def] >> NO_TAC) >>
  Cases_on `args` >> simp[] >> rpt (pairarg_tac >> gvs[]) >>
  simp[vv_type_def] >> rpt (IF_CASES_TAC >> simp[vv_type_def]) >>
  TRY (Cases_on `t`) >> simp[] >> rpt (pairarg_tac >> gvs[]) >>
  simp[vv_type_def] >> rpt (IF_CASES_TAC >> simp[vv_type_def]) >>
  TRY (Cases_on `t'`) >> simp[vv_type_def, stack_result_type]
QED
