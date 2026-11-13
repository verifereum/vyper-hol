Theory exprSimCopiedAnnotation
Ancestors
  exprLowering loweringPosts vyperAST compileEnv valueEncoding context combin exprCallBounds

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

Theorem invalid_result_type[local]:
  vv_type (FST (invalid_expr_call ty st)) = ty
Proof
  simp[invalid_expr_call_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[vv_type_def]
QED

Theorem compile_expr_array_result_type_from_builtin:
  (!cfn ce rt ty bi args st.
    vv_type (FST (compile_builtin_dispatch_body cfn ce rt ty bi args st)) = rt) ==>
  (!ce ty e sa vv sb et bd.
    expr_type e = ArrayT et bd /\ post_value_type ce e = expr_type e /\
    compile_expr ce ty e sa = (vv,sb) ==> vv_type vv = ArrayT et bd)
Proof
  strip_tac >>
  `!ce rt ty bi args st.
     vv_type (FST (compile_builtin_dispatch ce rt ty bi args st)) = rt`
    by simp[cj 2 compile_expr_raw_def] >>
  `!p ce rt ty bi args st.
     vv_type (FST (if p then compile_builtin_dispatch ce rt ty bi args st
                       else invalid_expr_call rt st)) = rt`
    by (rpt gen_tac >> Cases_on `p` >> simp[invalid_result_type]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def] >>
  (Cases_on `e` >> simp[compile_expr_body_def, expr_type_def] >> strip_tac)
  >~ [`compile_name_vv ce rt id st = (vv,sb)`]
  >- metis_tac[name_result_type, pairTheory.FST]
  >~ [`compile_literal_vv rt l st = (vv,sb)`]
  >- metis_tac[literal_result_type, pairTheory.FST] >>
  gvs[vv_type_def]
  >~ [`expr_type (TopLevelName a id)`]
  >- (Cases_on `FLOOKUP ce.ce_module_vars id` >> gvs[]
      >- (rpt (pairarg_tac >> gvs[]) >> gvs[vv_type_def]) >>
      rename1 `SOME loc` >> Cases_on `loc` >> gvs[] >>
      rpt (pairarg_tac >> gvs[]) >> gvs[vv_type_def]) >>
  all_tac
  >~ [`expr_type (IfExp t c a b)`]
  >- (rpt (pairarg_tac >> gvs[]) >>
      Cases_on `is_word_type (ArrayT et bd)` >> gvs[vv_type_def]) >>
  all_tac
  >~ [`expr_type (StructLit t p l)`]
  >- (rpt (pairarg_tac >> gvs[]) >> gvs[vv_type_def])
  >~ [`compile_subscript cfn ce rt ty obj idx st = (vv,sb)`]
  >- metis_tac[subscript_result_type, pairTheory.FST]
  >~ [`compile_attribute cfn ce rt ty obj fld st = (vv,sb)`]
  >- metis_tac[attribute_result_type, pairTheory.FST] >>
  all_tac
  >~ [`expr_type (Pop t target)`]
  >- (rpt (pairarg_tac >> gvs[]) >> gvs[vv_type_def])
  >~ [`expr_type (Call t target args drv)`]
  >- (Cases_on `target` >>
      gvs[post_value_type_def, lowered_value_type_def, expr_type_def,
          is_word_type_def, is_bytestring_type_def] >>
      qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _`
        (mp_tac o AP_TERM ``(vv_type o FST):vyper_value # compile_state -> type``) >>
      simp[combinTheory.o_DEF, call_result_type])
  >~ [`expr_type (TypeBuiltin t tb dest args)`]
  >- (qpat_x_assum `compile_type_builtin_dispatch _ _ _ _ _ _ _ = _`
        (mp_tac o AP_TERM ``(vv_type o FST):vyper_value # compile_state -> type``) >>
      simp[combinTheory.o_DEF, Once compile_expr_raw_def,
           type_builtin_result_type]) >>
  qpat_x_assum `_ = (vv,sb)`
    (mp_tac o AP_TERM ``(vv_type o FST):vyper_value # compile_state -> type``) >>
  simp[combinTheory.o_DEF] >>
  Cases_on `l` >> simp[] >>
  rename1 `h::tl` >> Cases_on `tl` >> simp[]
  >- (Cases_on `h` >> simp[]) >>
  rename1 `h::h2::tl2` >> Cases_on `tl2` >> simp[]
  >- (Cases_on `h` >> simp[] >> Cases_on `h2` >> simp[] >>
      Cases_on `b` >> simp[powmod_names_result_type]) >>
  rename1 `h::h2::h3::tl3` >> Cases_on `tl3` >> simp[]
  >- (Cases_on `h` >> simp[] >> Cases_on `h2` >> simp[] >>
      Cases_on `h3` >> simp[] >> Cases_on `b` >>
      simp[addmod_names_result_type, mulmod_names_result_type]) >>
  Cases_on `h` >> simp[] >> Cases_on `h2` >> simp[] >>
  Cases_on `h3` >> simp[]
QED
