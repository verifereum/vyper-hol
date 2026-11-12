(* Safe point operands. Each theorem below restates the private theorem of
   the same name in exprSimECArith; proofs from
   alan-ref/base/exprSimECArithScript.sml.txt:61-316. *)
Theory bodyMemEcArithSafe
Ancestors
  exprSimSource exprSimProps exprSimHypsDefs exprSimDefs loweringPosts
  exprOperandVar exprSafeOperand exprSafeOperandBuiltins fragExec
  exprSimHash exprSimWordBuiltins exprLowering exprSimHyps exprSimPrecompiles
  exprSimOperands exprSimLiteralBuffer exprSimCalldataSlice entryDecodeStaticProps
  builtinMisc venomInst exprLoweringProps venomExecSemantics venomState
  vyperTypeSystem vyperContext valueEncoding vyperTyping valueEncodingProofs
  vyperTypeBuiltins vyperValueOperation vyperValue vyperAssignPreservesType compileEnv

Theorem lower_value_name_safe_operand[local]:
  expr_body_pre cenv cx env (Name ann id) es /\
  local_ptrs_reserved cenv sa /\
  lower_value compile_expr cenv ann (Name ann id) sa = (op,sb) ==>
  safe_operand sb op
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  gvs[lower_value_def, compile_expr_def, compile_name_vv_def,
      unwrap_value_def, comp_bind_def, comp_return_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def,
      is_word_type_def] >>
  Cases_on `is_word_type ann`
  >- (gvs[] >> drule compile_ptr_load_safe_operand >> simp[]) >>
  gvs[comp_return_def, safe_operand_def] >>
  metis_tac[environment_var_not_fresh]
QED

Theorem ec_point_builtin_cases[local]:
  well_typed_builtin_app (ArrayT (BaseT (UintT 256)) (Fixed 2)) bi ts ==>
  bi = ECAdd \/ bi = ECMul \/
  bi = MakeArray (SOME (BaseT (UintT 256))) (Fixed 2)
Proof
  Cases_on `bi` >>
  simp[well_typed_builtin_app_def, is_numeric_type_def, is_bool_type_def,
       is_uint256_type_def, is_bytes32_type_def, is_flag_type_def]
  >~ [`MakeArray et bd`] >- (Cases_on `et` >> gvs[well_typed_builtin_app_def])
  >~ [`well_typed_binop _ bop _ _`] >-
    (Cases_on `bop` >> simp[well_typed_binop_def, is_numeric_type_def,
                          is_int_type_def, is_bool_type_def, is_flag_type_def])
  >~ [`env_item_type ei`] >- (Cases_on `ei` >> simp[env_item_type_def]) >>
  rename1 `account_item_type ai` >> Cases_on `ai` >> simp[account_item_type_def]
QED

Theorem ec_point_builtin_not_label[local]:
  well_typed_expr env (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bi args) /\
  compile_builtin_dispatch_body cfn cenv
    (ArrayT (BaseT (UintT 256)) (Fixed 2)) ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >>
  `bi = ECAdd \/ bi = ECMul \/
   bi = MakeArray (SOME (BaseT (UintT 256))) (Fixed 2)` by
    (irule ec_point_builtin_cases >>
     gvs[well_typed_expr_def] >> metis_tac[]) >>
  gvs[compile_builtin_dispatch_body_def, as_ptr_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `as_ptr_val _ _ res` >>
  Cases_on `res` >>
  gvs[as_ptr_val_def, contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  fs[markerTheory.Abbrev_def] >>
  metis_tac[ec_arith_result_not_label,
            compiler_make_array_result, alloc_buffer_not_label]
QED

Theorem ec_point_type_builtin_cases[local]:
  type_builtin_result_ok tenv tb (ArrayT (BaseT (UintT 256)) (Fixed 2)) target ts /\
  well_typed_type_builtin_args tb target ts ==>
  tb = Empty \/ ?ensure. tb = AbiDecode ensure
Proof
  Cases_on `tb` >>
  simp[type_builtin_result_ok_def, well_typed_type_builtin_args_def,
       is_numeric_type_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `valid_conversion src (ArrayT _ _)` >>
  Cases_on `src` >> gvs[valid_conversion_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[valid_conversion_def]
QED

Theorem ec_point_type_builtin_not_label[local]:
  well_typed_expr env
    (TypeBuiltin (ArrayT (BaseT (UintT 256)) (Fixed 2)) tb target args) /\
  compile_type_builtin_dispatch_body cfn cenv
    (ArrayT (BaseT (UintT 256)) (Fixed 2)) ty tb target args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >>
  `(tb = Empty \/ ?ensure. tb = AbiDecode ensure) /\
   target = ArrayT (BaseT (UintT 256)) (Fixed 2)` by
    (gvs[well_typed_expr_def] >> conj_tac
     >- metis_tac[ec_point_type_builtin_cases] >>
     Cases_on `tb` >> gvs[type_builtin_result_ok_def]) >>
  gvs[compile_type_builtin_dispatch_body_def, is_word_type_def,
      is_bytestring_type_def, contextTheory.vv_operand_def,
      contextTheory.mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[contextTheory.vv_operand_def, contextTheory.mk_ptr_def])
  >- (simp[contextTheory.base_ptr_def] >> metis_tac[compile_empty_not_label]) >>
  qmatch_asmsub_abbrev_tac `as_ptr_val _ _ res` >>
  Cases_on `res` >>
  gvs[as_ptr_val_def, contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  fs[markerTheory.Abbrev_def] >> metis_tac[lower_abi_decode_not_label]
QED

Theorem ec_point_call_not_label[local]:
  well_typed_expr env
    (Call (ArrayT (BaseT (UintT 256)) (Fixed 2)) target args drv) /\
  compile_call cfn cenv (ArrayT (BaseT (UintT 256)) (Fixed 2))
    ty target args drv sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `target` >>
  simp[well_typed_expr_def, raw_call_return_type_def]
  >~ [`IntCall fid`] >- metis_tac[compile_internal_call_not_label]
  >~ [`ExtCall _ _ _ _`] >-
   (qmatch_goalsub_rename_tac `ExtCall stat skip fsig opts` >>
    PairCases_on `fsig` >>
  rpt strip_tac >> gvs[well_typed_expr_def] >>
  gvs[compile_call_def] >>
  Cases_on `args` >> gvs[contextTheory.vv_operand_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[compile_external_call_not_label]) >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ec_point_lower_value_safe_operand:
  expr_body_pre cenv cx env e es /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  local_ptrs_reserved cenv sa /\
  lower_value compile_expr cenv (ArrayT (BaseT (UintT 256)) (Fixed 2)) e sa = (op,sb) ==>
  safe_operand sb op
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (metis_tac[compile_lower_value_var]) >>
  Cases_on `e` >> gvs[vyperASTTheory.expr_type_def]
  >~ [`Name _ id`] >- metis_tac[lower_value_name_safe_operand]
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

Resume ec_point_lower_value_safe_operand[literal]:
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def]
QED
Resume ec_point_lower_value_safe_operand[flag]:
  gvs[expr_body_pre_def, well_typed_expr_def]
QED
Resume ec_point_lower_value_safe_operand[struct]:
  gvs[expr_body_pre_def, well_typed_expr_def]
QED
Resume ec_point_lower_value_safe_operand[ifexp]:
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def, is_word_type_def, unwrap_value_def,
       contextTheory.mk_ptr_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def, is_word_type_def, unwrap_value_def,
      contextTheory.mk_ptr_def, comp_return_def, safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[topname]:
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def, AllCaseEqs(), unwrap_value_def,
       contextTheory.mk_ptr_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperASTTheory.expr_type_def, unwrap_value_def, is_word_type_def,
      contextTheory.mk_ptr_def, comp_return_def] >>
  drule ensure_memory_not_label >> simp[] >> strip_tac >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[subscript]:
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule compile_subscript_not_label >> strip_tac >>
  `!l. op <> Label l` by metis_tac[unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[attribute]:
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule compile_attribute_safe_operand >>
  simp[safe_operand_def] >> strip_tac >>
  `!l. op <> Label l` by metis_tac[unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[call]:
  `well_typed_expr env (Call (ArrayT (BaseT (UintT 256)) (Fixed 2)) target args drv)` by
    gvs[expr_body_pre_def] >>
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  `!l. vv_operand vv <> Label l` by metis_tac[ec_point_call_not_label] >>
  `!l. op <> Label l` by metis_tac[unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[pop]:
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  drule (cj 3 subscript_pop_not_label) >> strip_tac >>
  `!l. op <> Label l` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def, is_word_type_def] >> strip_tac >>
     qmatch_asmsub_abbrev_tac `mk_ptr _ loc` >>
     Cases_on `loc` >> gvs[contextTheory.mk_ptr_def, comp_return_def] >>
     drule ensure_memory_not_label >> simp[]) >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[builtin]:
  `well_typed_expr env (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bi args)` by
    gvs[expr_body_pre_def] >>
  `bi = ECAdd \/ bi = ECMul \/ bi = MakeArray (SOME (BaseT (UintT 256))) (Fixed 2)` by
    (irule ec_point_builtin_cases >> gvs[well_typed_expr_def] >> metis_tac[]) >>
  `~names_builtin bi args` by
    (gvs[] >> namedCases_on `args` ["", "a rest"] >> simp[names_builtin_def] >>
     Cases_on `a` >> simp[names_builtin_def] >>
     namedCases_on `rest` ["", "b rest2"] >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def] >>
     namedCases_on `rest2` ["", "d rest3"] >> simp[names_builtin_def] >>
     Cases_on `d` >> simp[names_builtin_def] >>
     Cases_on `rest3` >> simp[names_builtin_def]) >>
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch] >>
  pure_rewrite_tac[CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)] >>
  strip_tac >>
  `!l. vv_operand vv <> Label l` by metis_tac[ec_point_builtin_not_label] >>
  `!l. op <> Label l` by metis_tac[unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[typebuiltin]:
  `well_typed_expr env (TypeBuiltin (ArrayT (BaseT (UintT 256)) (Fixed 2)) tb target args)` by
    gvs[expr_body_pre_def] >>
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  FULL_SIMP_TAC bool_ss [CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
  `!l. vv_operand vv <> Label l` by metis_tac[ec_point_type_builtin_not_label] >>
  `!l. op <> Label l` by metis_tac[unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Finalise ec_point_lower_value_safe_operand
