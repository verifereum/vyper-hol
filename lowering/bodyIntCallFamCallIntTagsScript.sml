(* Callback-parametric output annotations; no semantic scalar assumptions. *)
Theory bodyIntCallFamCallIntTags
Ancestors
  exprLowering context state_transformer

Theorem intcall_as_stack_val_tag[simp]:
  vv_type (FST (as_stack_val ty result)) = ty
Proof
  Cases_on `result` >> simp[as_stack_val_def, vv_type_def]
QED

Theorem intcall_as_ptr_val_tag[simp]:
  vv_type (FST (as_ptr_val ty loc result)) = ty
Proof
  Cases_on `result` >> simp[as_ptr_val_def, vv_type_def]
QED

Theorem intcall_literal_tag:
  vv_type (FST (compile_literal_vv ty lit st)) = ty
Proof
  Cases_on `lit`
  >~ [`BoolL flag`] >- (Cases_on `flag` >> simp[compile_literal_vv_def,
      compileEnvTheory.comp_return_def, vv_type_def])
  >~ [`BytesL bs`] >- (
      Cases_on `ty` >> simp[compile_literal_vv_def,
        compileEnvTheory.comp_return_def, vv_type_def, compileEnvTheory.comp_bind_def] >>
      qmatch_goalsub_rename_tac `BaseT bt` >> Cases_on `bt` >>
      simp[compileEnvTheory.comp_return_def, vv_type_def, compileEnvTheory.comp_bind_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >>
      simp[compileEnvTheory.comp_return_def, vv_type_def, compileEnvTheory.comp_bind_def] >>
      pairarg_tac >> simp[vv_type_def])
  >~ [`StringL str`] >- (
      Cases_on `ty` >> simp[compile_literal_vv_def,
        compileEnvTheory.comp_return_def, vv_type_def, compileEnvTheory.comp_bind_def] >>
      pairarg_tac >> simp[vv_type_def])
  >> simp[compile_literal_vv_def, compileEnvTheory.comp_return_def, vv_type_def]
QED

Theorem intcall_type_builtin_tag:
  vv_type (FST (compile_type_builtin_dispatch_body cb ce ann ty tb target args st)) = ann
Proof
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, pairTheory.ELIM_UNCURRY,
       vv_type_def] >>
  rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, vv_type_def]) >>
  Cases_on `target` >> simp[]
QED

Theorem intcall_builtin_tag:
  vv_type (FST (compile_builtin_dispatch_body cb ce ann ty bi args st)) = ann
Proof
  Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def, pairTheory.ELIM_UNCURRY,
       vv_type_def, intcall_literal_tag] >>
  rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, vv_type_def, intcall_literal_tag])
  >~ [`compile_keccak256_word`] >- (
    Cases_on `expr_type (HD args)` >> simp[] >>
    qmatch_goalsub_rename_tac `BaseT bt` >> Cases_on `bt` >> simp[] >>
    rename1 `BytesT bound` >> Cases_on `bound` >> simp[])
  >~ [`compile_sha256_word`] >- (
    Cases_on `expr_type (HD args)` >> simp[] >>
    qmatch_goalsub_rename_tac `BaseT bt` >> Cases_on `bt` >> simp[] >>
    rename1 `BytesT bound` >> Cases_on `bound` >> simp[])
  >~ [`compile_make_tuple`] >- (
    BasicProvers.TOP_CASE_TAC >> simp[])
  >~ [`compile_var_array_membership`] >- (
    Cases_on `HD (TL args)` >> simp[] >>
    rpt (BasicProvers.TOP_CASE_TAC >> simp[]))
  >> BasicProvers.TOP_CASE_TAC >> simp[intcall_literal_tag]
QED

Theorem intcall_name_tag:
  vv_type (FST (compile_name_vv ce ann id st)) = ann
Proof
  simp[compile_name_vv_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       pairTheory.ELIM_UNCURRY, vv_type_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       pairTheory.ELIM_UNCURRY, vv_type_def]
QED

Theorem intcall_addmod_names_tag:
  vv_type (FST (compile_addmod_names ce ann aty a bty b mty m st)) = ann
Proof
  simp[compile_addmod_names_def, pairTheory.ELIM_UNCURRY]
QED

Theorem intcall_mulmod_names_tag:
  vv_type (FST (compile_mulmod_names ce ann aty a bty b mty m st)) = ann
Proof
  simp[compile_mulmod_names_def, pairTheory.ELIM_UNCURRY]
QED

Theorem intcall_powmod_names_tag:
  vv_type (FST (compile_powmod256_names ce ann aty a bty b st)) = ann
Proof
  simp[compile_powmod256_names_def, pairTheory.ELIM_UNCURRY]
QED

Theorem intcall_attribute_tag:
  vv_type (FST (compile_attribute cb ce ann ty base_e fld st)) = ann
Proof
  simp[compile_attribute_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def, pairTheory.ELIM_UNCURRY, vv_type_def]
QED

Theorem intcall_subscript_tag:
  vv_type (FST (compile_subscript cb ce ann ty base_e idx_e st)) = ann
Proof
  simp[compile_subscript_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def, pairTheory.ELIM_UNCURRY] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       pairTheory.ELIM_UNCURRY, vv_type_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       pairTheory.ELIM_UNCURRY, vv_type_def]
QED
