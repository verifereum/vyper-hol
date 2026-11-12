(* Static result annotations are independent of recursive callback results. *)
Theory bodyIntCallCompilerTags
Ancestors exprLowering context compileEnv supportedExprTraverse vyperAST

Theorem intcall_as_stack_val_tag[simp]:
  vv_type (FST (as_stack_val ty p)) = ty
Proof
  Cases_on `p` >> simp[as_stack_val_def, vv_type_def]
QED

Theorem intcall_as_ptr_val_tag[simp]:
  vv_type (FST (as_ptr_val ty loc p)) = ty
Proof
  Cases_on `p` >> simp[as_ptr_val_def, vv_type_def]
QED

Theorem intcall_type_dispatch_body_tag:
  vv_type (FST (compile_type_builtin_dispatch_body cfn ce tag ty tb rt es st)) = tag
Proof
  Cases_on `tb` >> simp[compile_type_builtin_dispatch_body_def] >>
  simp[pairTheory.ELIM_UNCURRY, vv_type_def] >>
  rpt IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, vv_type_def] >>
  Cases_on `rt` >> simp[]
QED

Theorem intcall_literal_vv_tag:
  vv_type (FST (compile_literal_vv tag l st)) = tag
Proof
  Cases_on `l` >>
  simp[compile_literal_vv_def, comp_return_def, comp_bind_def,
       pairTheory.ELIM_UNCURRY, vv_type_def] >>
  rpt CASE_TAC >>
  simp[comp_return_def, comp_bind_def, pairTheory.ELIM_UNCURRY, vv_type_def] >>
  rename1 `BoolL b` >> Cases_on `b` >>
  simp[compile_literal_vv_def, comp_return_def, vv_type_def]
QED

Theorem intcall_builtin_dispatch_body_tag:
  vv_type (FST (compile_builtin_dispatch_body cfn ce tag ty bi es st)) = tag
Proof
  Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def, pairTheory.ELIM_UNCURRY, vv_type_def] >>
  rpt (IF_CASES_TAC >>
       simp[pairTheory.ELIM_UNCURRY, vv_type_def, intcall_literal_vv_tag])
  >~ [`compile_keccak256_word`]
  >- (Cases_on `expr_type (HD es)` >> simp[] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[])
  >~ [`compile_sha256_word`]
  >- (Cases_on `expr_type (HD es)` >> simp[] >>
      rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[])
  >~ [`compile_make_tuple`]
  >- (rename1 `option_CASE opt _ _` >> Cases_on `opt` >> simp[])
  >~ [`method_id_literal`]
  >- (Cases_on `method_id_literal (HD es)` >>
      simp[intcall_literal_vv_tag, pairTheory.ELIM_UNCURRY] >>
      IF_CASES_TAC >> simp[])
  >> Cases_on `HD (TL es)` >> simp[pairTheory.ELIM_UNCURRY]
  >~ [`builtin_CASE inner`]
  >- (Cases_on `inner` >> simp[pairTheory.ELIM_UNCURRY] >>
      IF_CASES_TAC >> simp[])
  >> Cases_on `method_id_literal (HD es)` >> simp[intcall_literal_vv_tag]
QED

Theorem intcall_subscript_tag:
  vv_type (FST (compile_subscript cfn ce tag ty base_e idx st)) = tag
Proof
  simp[compile_subscript_def, comp_bind_def, comp_return_def,
       pairTheory.ELIM_UNCURRY] >>
  Cases_on `place_type ce base_e` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def,
       pairTheory.ELIM_UNCURRY, vv_type_def] >>
  rename1 `ValPT bt` >> Cases_on `bt` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def,
       pairTheory.ELIM_UNCURRY, vv_type_def]
QED

Theorem intcall_attribute_tag:
  vv_type (FST (compile_attribute cfn ce tag ty base_e fld st)) = tag
Proof
  simp[compile_attribute_def, comp_bind_def, comp_return_def,
       pairTheory.ELIM_UNCURRY, vv_type_def]
QED

Theorem intcall_name_tag:
  vv_type (FST (compile_name_vv ce tag id st)) = tag
Proof
  simp[compile_name_vv_def] >> Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def,
       pairTheory.ELIM_UNCURRY, vv_type_def] >>
  rename1 `SOME vl` >> Cases_on `vl` >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def,
       pairTheory.ELIM_UNCURRY, vv_type_def]
QED

Theorem intcall_expr_body_tag:
  (!ce tag ty bi es st.
     vv_type (FST (bfn ce tag ty bi es st)) = tag) /\
  (!ce tag ty tb rt es st.
     vv_type (FST (tfn ce tag ty tb rt es st)) = tag) /\
  ~expr_effect_root e ==>
  vv_type (FST (compile_expr_body cfn bfn tfn ce ty e st)) = expr_type e
Proof
  strip_tac >> Cases_on `e` >>
  gvs[expr_effect_root_def, compile_expr_body_def, expr_type_def,
      pairTheory.ELIM_UNCURRY, vv_type_def, intcall_literal_vv_tag,
      intcall_subscript_tag, intcall_attribute_tag, intcall_name_tag]
  >~ [`FLOOKUP ce.ce_module_vars nsid`]
  >- (Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[vv_type_def] >>
      rename1 `SOME vl` >> Cases_on `vl` >> simp[vv_type_def])
  >~ [`if is_word_type rt then _ else _`]
  >- (IF_CASES_TAC >> simp[vv_type_def])
  >> rename1 `list_CASE args _ _` >>
  namedCases_on `args` ["", "head tail"] >> simp[] >>
  Cases_on `head` >> simp[] >>
  namedCases_on `tail` ["", "head2 tail2"] >> simp[] >>
  Cases_on `head2` >> simp[] >>
  namedCases_on `tail2` ["", "head3 tail3"] >> simp[]
  >~ [`builtin_CASE bi`]
  >- (Cases_on `bi` >>
      simp[compile_powmod256_names_def, pairTheory.ELIM_UNCURRY])
  >> Cases_on `head3` >> simp[] >>
  Cases_on `tail3` >> simp[] >>
  rename1 `builtin_CASE bi` >> Cases_on `bi` >>
  simp[compile_addmod_names_def, compile_mulmod_names_def, pairTheory.ELIM_UNCURRY]
QED

Theorem intcall_compile_expr_tag:
  ~expr_has_effect e ==>
  vv_type (FST (compile_expr ce ty e st)) = expr_type e
Proof
  strip_tac >>
  `~expr_effect_root e` by
    metis_tac[expr_has_effect_def, supported_expr_exists_root] >>
  once_rewrite_tac[compile_expr_raw_def] >>
  irule intcall_expr_body_tag >> simp[] >> conj_tac >> rpt gen_tac >>
  IF_CASES_TAC >> simp[exprCallBoundsTheory.invalid_expr_call_def, vv_type_def] >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[intcall_builtin_dispatch_body_tag, intcall_type_dispatch_body_tag,
       pairTheory.ELIM_UNCURRY, vv_type_def]
QED
