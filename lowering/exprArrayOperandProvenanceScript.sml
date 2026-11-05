(* Shared operand provenance for typed array expressions. *)
Theory exprArrayOperandProvenance
Ancestors
  exprSimHyps exprOperandVar exprSafeOperandBuiltins exprLowering
  vyperTypeSystem exprSimWordBuiltins emitHelper compileEnv

(* The name case uses the pointer invariant in expr_body_pre, not reservation. *)
Theorem array_builtin_result_origins[local]:
  well_typed_builtin_app (ArrayT et bd) bi ts ==>
  bi = ECAdd \/ bi = ECMul \/ bi = MakeArray (SOME et) bd
Proof
  Cases_on `bi` >>
  simp[well_typed_builtin_app_def, is_numeric_type_def, is_bool_type_def,
       is_uint256_type_def, is_bytes32_type_def, is_flag_type_def]
  >~ [`MakeArray elem bound`] >- (Cases_on `elem` >> gvs[well_typed_builtin_app_def])
  >~ [`well_typed_binop _ bop _ _`] >-
    (Cases_on `bop` >> simp[well_typed_binop_def, is_numeric_type_def,
                          is_int_type_def, is_bool_type_def, is_flag_type_def])
  >~ [`env_item_type item`] >- (Cases_on `item` >> simp[env_item_type_def]) >>
  rename1 `account_item_type item` >> Cases_on `item` >> simp[account_item_type_def]
QED

Theorem compile_array_expr_not_label:
  expr_body_pre cenv cx env obj es /\ expr_type obj = ArrayT et bd /\
  compile_expr cenv ty obj sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> Cases_on `obj` >> gvs[vyperASTTheory.expr_type_def]
  >~ [`Name _ id`] >- suspend "name"
  >~ [`Literal _ lit`] >- suspend "literal"
  >~ [`IfExp _ ce te ee`] >- suspend "ifexp"
  >~ [`Builtin _ bi args`] >- suspend "builtin"
  >~ [`TypeBuiltin _ tb target args`] >- suspend "typebuiltin"
  >~ [`Subscript _ be ie`] >- suspend "subscript"
  >~ [`Attribute _ be fld`] >- suspend "attribute"
  >~ [`StructLit _ id fields`] >- suspend "struct"
  >~ [`FlagMember _ id mem`] >- suspend "flag"
  >~ [`TopLevelName _ id`] >- suspend "topname"
  >~ [`Call _ target args drv`] >- suspend "call"
  >> suspend "pop"
QED

Resume compile_array_expr_not_label[name]:
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  gvs[compile_expr_def, compile_name_vv_def, contextTheory.vv_operand_def,
      contextTheory.mk_ptr_def, comp_return_def]
QED
Resume compile_array_expr_not_label[literal]:
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def]
QED
Resume compile_array_expr_not_label[flag]:
  gvs[expr_body_pre_def, well_typed_expr_def]
QED
Resume compile_array_expr_not_label[struct]:
  gvs[expr_body_pre_def, well_typed_expr_def]
QED
Resume compile_array_expr_not_label[ifexp]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def, is_word_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def, is_word_type_def,
      contextTheory.vv_operand_def, contextTheory.mk_ptr_def]
QED
Resume compile_array_expr_not_label[topname]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def, AllCaseEqs(), contextTheory.vv_operand_def,
       contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def]
QED
Resume compile_array_expr_not_label[subscript]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> metis_tac[compile_subscript_not_label]
QED
Resume compile_array_expr_not_label[attribute]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule compile_attribute_safe_operand >> simp[exprSafeOperandTheory.safe_operand_def]
QED
Resume compile_array_expr_not_label[pop]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[cj 3 subscript_pop_not_label]
QED
Resume compile_array_expr_not_label[builtin]:
  `bi = ECAdd \/ bi = ECMul \/ bi = MakeArray (SOME et) bd` by
    (irule array_builtin_result_origins >>
     gvs[expr_body_pre_def, well_typed_expr_def] >> metis_tac[]) >>
  `~names_builtin bi args` by
    (gvs[] >> namedCases_on `args` ["", "a rest"] >> simp[names_builtin_def] >>
     Cases_on `a` >> simp[names_builtin_def] >>
     namedCases_on `rest` ["", "b rest2"] >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def] >>
     namedCases_on `rest2` ["", "d rest3"] >> simp[names_builtin_def] >>
     Cases_on `d` >> simp[names_builtin_def] >>
     Cases_on `rest3` >> simp[names_builtin_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch] >>
  pure_rewrite_tac[CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)] >>
  gvs[] >>
  simp[compile_builtin_dispatch_body_def, as_ptr_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  qmatch_asmsub_abbrev_tac `as_ptr_val _ _ res` >> Cases_on `res` >>
  gvs[as_ptr_val_def, contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  fs[markerTheory.Abbrev_def] >>
  metis_tac[ec_arith_result_not_label,
            compiler_make_array_result, exprSafeOperandTheory.alloc_buffer_not_label]
QED
Resume compile_array_expr_not_label[typebuiltin]:
  `well_typed_expr env (TypeBuiltin (ArrayT et bd) tb target args)` by
    gvs[expr_body_pre_def] >>
  Cases_on `tb` >>
  gvs[well_typed_expr_def, type_builtin_result_ok_def,
      well_typed_type_builtin_args_def, is_numeric_type_def]
  >~ [`valid_conversion src (ArrayT _ _)`] >-
    (Cases_on `src` >> gvs[valid_conversion_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[valid_conversion_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >>
  pure_rewrite_tac[CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
  simp[compile_type_builtin_dispatch_body_def, is_word_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def]
  >~ [`compile_builtin_empty_complex _ _ _ = _`] >-
    metis_tac[compile_empty_not_label] >>
  qmatch_asmsub_abbrev_tac `as_ptr_val _ _ res` >> Cases_on `res` >>
  gvs[as_ptr_val_def, contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  fs[markerTheory.Abbrev_def] >> metis_tac[lower_abi_decode_not_label]
QED
Resume compile_array_expr_not_label[call]:
  `well_typed_expr env (Call (ArrayT et bd) target args drv)` by
    gvs[expr_body_pre_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  Cases_on `target` >>
  gvs[well_typed_expr_def, raw_call_return_type_def]
  >~ [`IntCall fid`] >- metis_tac[compile_internal_call_not_label]
  >~ [`ExtCall _ _ _ _`] >-
   (qmatch_asmsub_rename_tac `ExtCall stat skip fsig opts` >>
    PairCases_on `fsig` >>
    gvs[compile_call_def] >> Cases_on `args` >>
    gvs[contextTheory.vv_operand_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    gvs[AllCaseEqs(), contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
    metis_tac[compile_external_call_not_label]) >>
  gvs[AllCaseEqs()]
QED
Finalise compile_array_expr_not_label
