(*
 * Expression simulation: ecadd, ecmul (#636, Builtins row 8)
 *
 * ecadd(a, b) compiles both point operands (compile_expr, unwrap_value),
 * ecmul(a, k) the point and then the scalar (lower_value); only then does
 * compile_ecadd_points / compile_ecmul_point (builtinMisc) ALLOCA the
 * precompile input, load each point word from the operand pointers and
 * store it into the input, ALLOCA a 64-byte output, STATICCALL precompile 6
 * or 7, ASSERT its success word and return the output pointer.
 *
 * The first point's bytes must survive the second operand's fragment and
 * the stores into the input.  The point sits in one of the first
 * fragment's allocations (expr_post_operand_kept_stable) or in a live
 * local (expr_post_operand_local_kept, by expr_post's locals_kept);
 * expr_val_at keeps those two cases apart, and the input, a fresh
 * ALLOCA, is clear of both.  take_outcome answers the call with precompile_result
 * (extCallOracle), which runs verifereum's ecadd/ecmul on the decoded
 * words, as evaluate_ecadd/evaluate_ecmul do: an invalid point fails the
 * call, so the ASSERT reverts where the source raises.  The ALLOCA, the
 * call and the ASSERT are exprSimPrecompiles' shared pieces, also used by
 * ecrecover.
 *
 * TOP-LEVEL:
 *   compile_ecadd_call_sim, compile_ecmul_call_sim — expr_vv_ok of ECAdd
 *   and ECMul (exprSimBuiltins' compile_ecadd_sim, compile_ecmul_sim)
 *)
Theory exprSimECArith
Ancestors
  exprOperandVar exprSafeOperand fragExec exprSimHash exprSimWordBuiltins
  exprLowering exprSimHyps exprSimPrecompiles exprSimOperands
  exprSimUnwrap exprSimBuffer exprSimCalldataSlice entryDecodeStaticProps
  builtinMisc loweringSlice venomInst exprLoweringProps venomExecSemantics
  venomState vyperTypeSystem vyperContext valueEncoding exprSim
  vyperTyping valueEncodingProofs vyperTypeBuiltins vyperValueOperation
  vyperValue vyperAssignPreservesType compileEnv extCallOracle byte
  vfmBuffer venomMemDefs vfmTypes vfmExecution bn254 list rich_list
  numposrep cv_std[ignore_grammar]

Theorem ec_alloc_buffer_not_label[local]:
  compile_alloc_buffer bytes sa = (buf,sb) ==>
  !l. buf.buf_operand <> Label l
Proof
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  drule emit_op_safe_operand >> simp[safe_operand_def]
QED

Theorem ec_ensure_memory_not_label[local]:
  compile_ensure_in_memory p loc bytes wc ctor sa = (op,sb) /\
  (!l. p <> Label l) ==> !l. op <> Label l
Proof
  Cases_on `loc` >> simp[contextTheory.compile_ensure_in_memory_def, comp_return_def]
  >- metis_tac[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[ec_alloc_buffer_not_label]
QED

Theorem ec_unwrap_value_not_label[local]:
  unwrap_value cenv vv sa = (op,sb) /\
  (!l. vv_operand vv <> Label l) ==> !l. op <> Label l
Proof
  Cases_on `vv` >> simp[unwrap_value_def, contextTheory.vv_operand_def, comp_return_def]
  >- metis_tac[] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >> simp[]
  >- metis_tac[compile_ptr_load_safe_operand, safe_operand_def] >>
  Cases_on `p.ptr_location` >> simp[comp_return_def] >>
  metis_tac[ec_ensure_memory_not_label]
QED

Theorem ec_point_name_safe_operand[local]:
  expr_sim_pre cenv cx env
    (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) id) es /\
  local_ptrs_reserved cenv sa /\
  lower_value compile_expr cenv (ArrayT (BaseT (UintT 256)) (Fixed 2))
    (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) id) sa = (op,sb) ==>
  safe_operand sb op
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  gvs[lower_value_def, compile_expr_def, compile_name_vv_def,
      unwrap_value_def, comp_bind_def, comp_return_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def,
      is_word_type_def, safe_operand_def] >>
  metis_tac[environment_var_not_fresh]
QED

Theorem ec_attribute_safe_operand[local]:
  compile_attribute cfn cenv ret_ty ty base_e fname sa = (vv,sb) ==>
  safe_operand sb (vv_operand vv)
Proof
  simp[compile_attribute_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[emit_op_safe_operand]
QED

Theorem ec_mapping_subscript_not_label[local]:
  compile_mapping_subscript bop kop sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[compile_mapping_subscript_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_op_safe_operand >> simp[safe_operand_def]
QED

Theorem ec_array_subscript_not_label[local]:
  compile_array_subscript bop idx dyn cnt ws sz signed load sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_op_safe_operand >> simp[safe_operand_def]
QED

Theorem ec_dynarray_pop_not_label[local]:
  compile_dynarray_pop bop ws sz load store sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[compile_dynarray_pop_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_op_safe_operand >> simp[safe_operand_def]
QED

Theorem ec_subscript_not_label[local]:
  compile_subscript cfn cenv rt ty base_e idx_e sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_subscript_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `place_type cenv base_e` >> simp[]
  >- (simp[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      simp[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
      metis_tac[ec_mapping_subscript_not_label]) >>
  rename1 `ValPT bty` >> Cases_on `bty` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[ec_array_subscript_not_label, emit_op_safe_operand,
            compile_tuple_subscript_def, safe_operand_def]
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

Theorem ecadd_result_not_label[local]:
  compile_ecadd_points p1 p2 sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[compile_ecadd_points_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[ec_alloc_buffer_not_label]
QED

Theorem ecmul_result_not_label[local]:
  compile_ecmul_point p scalar sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[compile_ecmul_point_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[ec_alloc_buffer_not_label]
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
  metis_tac[ecadd_result_not_label, ecmul_result_not_label,
            compiler_make_array_result, ec_alloc_buffer_not_label]
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

Theorem ec_decode_not_label[local]:
  lower_abi_decode data_op info amin amax bytes sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinAbiTheory.lower_abi_decode_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[ec_alloc_buffer_not_label]
QED

Theorem ec_empty_not_label[local]:
  compile_builtin_empty_complex bytes bs sa = (op,sb) ==> !l. op <> Label l
Proof
  Cases_on `bs` >>
  simp[builtinSimpleTheory.compile_builtin_empty_complex_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[ec_alloc_buffer_not_label]
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
  >- metis_tac[ec_empty_not_label] >>
  qmatch_asmsub_abbrev_tac `as_ptr_val _ _ res` >>
  Cases_on `res` >>
  gvs[as_ptr_val_def, contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  fs[markerTheory.Abbrev_def] >> metis_tac[ec_decode_not_label]
QED

Theorem ec_default_return_result[local]:
  compile_default_return_path cenv rt dt buf res dop addr skip mn mx info sa =
    (op,sb) ==> op = res
Proof
  simp[compile_default_return_path_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem ec_external_call_not_label[local]:
  compile_external_call_kwargs cenv addr vals tys msz asz mid rsz mn rms
    stat value gas skip hasdef dop rt dt einfo dinfo sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[compile_external_call_kwargs_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `rsz = 0` >> simp[comp_return_def] >>
  Cases_on `hasdef` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[ec_default_return_result, ec_alloc_buffer_not_label]
QED

Theorem ec_internal_call_not_label[local]:
  compile_call cfn cenv rt ty (IntCall fid) args drv sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> gvs[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac ec_alloc_buffer_not_label >>
  gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def]
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
  >~ [`IntCall fid`] >- metis_tac[ec_internal_call_not_label]
  >~ [`ExtCall _ _ _ _`] >-
   (qmatch_goalsub_rename_tac `ExtCall stat skip fsig opts` >>
    PairCases_on `fsig` >>
  rpt strip_tac >> gvs[well_typed_expr_def] >>
  gvs[compile_call_def] >>
  Cases_on `args` >> gvs[contextTheory.vv_operand_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[ec_external_call_not_label]) >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ec_point_lower_value_safe_operand[local]:
  expr_sim_pre cenv cx env e es /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  local_ptrs_reserved cenv sa /\
  lower_value compile_expr cenv (ArrayT (BaseT (UintT 256)) (Fixed 2)) e sa = (op,sb) ==>
  safe_operand sb op
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (metis_tac[compile_lower_value_var]) >>
  Cases_on `e` >> gvs[vyperASTTheory.expr_type_def]
  >~ [`Name _ id`] >- metis_tac[ec_point_name_safe_operand]
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
  gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_literal_def]
QED
Resume ec_point_lower_value_safe_operand[flag]:
  gvs[expr_sim_pre_def, well_typed_expr_def]
QED
Resume ec_point_lower_value_safe_operand[struct]:
  gvs[expr_sim_pre_def, well_typed_expr_def]
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
  drule ec_ensure_memory_not_label >> simp[] >> strip_tac >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[subscript]:
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule ec_subscript_not_label >> strip_tac >>
  `!l. op <> Label l` by metis_tac[ec_unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[attribute]:
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule ec_attribute_safe_operand >>
  simp[safe_operand_def] >> strip_tac >>
  `!l. op <> Label l` by metis_tac[ec_unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[call]:
  `well_typed_expr env (Call (ArrayT (BaseT (UintT 256)) (Fixed 2)) target args drv)` by
    gvs[expr_sim_pre_def] >>
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  `!l. vv_operand vv <> Label l` by metis_tac[ec_point_call_not_label] >>
  `!l. op <> Label l` by metis_tac[ec_unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[pop]:
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  drule ec_dynarray_pop_not_label >> strip_tac >>
  `!l. op <> Label l` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_value_def, is_word_type_def] >> strip_tac >>
     Cases_on `loc` >> gvs[contextTheory.mk_ptr_def, comp_return_def] >>
     drule ec_ensure_memory_not_label >> simp[]) >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[builtin]:
  `well_typed_expr env (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) bi args)` by
    gvs[expr_sim_pre_def] >>
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
  `!l. op <> Label l` by metis_tac[ec_unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Resume ec_point_lower_value_safe_operand[typebuiltin]:
  `well_typed_expr env (TypeBuiltin (ArrayT (BaseT (UintT 256)) (Fixed 2)) tb target args)` by
    gvs[expr_sim_pre_def] >>
  gvs[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  gvs[vyperASTTheory.expr_type_def] >>
  FULL_SIMP_TAC bool_ss [CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
  `!l. vv_operand vv <> Label l` by metis_tac[ec_point_type_builtin_not_label] >>
  `!l. op <> Label l` by metis_tac[ec_unwrap_value_not_label] >>
  Cases_on `op` >> gvs[safe_operand_def]
QED
Finalise ec_point_lower_value_safe_operand

Theorem ecadd_types[local]:
  well_typed_builtin_app ty ECAdd ts ==>
  ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ts = [ArrayT (BaseT (UintT 256)) (Fixed 2);
        ArrayT (BaseT (UintT 256)) (Fixed 2)]
Proof
  simp[well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `ts` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem ecmul_types[local]:
  well_typed_builtin_app ty ECMul ts ==>
  ty = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ts = [ArrayT (BaseT (UintT 256)) (Fixed 2); BaseT (UintT 256)]
Proof
  simp[well_typed_builtin_app_def] >> strip_tac >>
  Cases_on `ts` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem ec_point_footprint[local]:
  val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v = 64
Proof
  Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]
QED

(* val_wf is a memory-capacity condition, not semantic typing. *)
Theorem ec_point_val_wf_not_typing[local]:
  val_wf (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) NoneV /\
  extract_ec_point NoneV = NONE
Proof
  simp[val_wf_def, extract_ec_point_def]
QED

Theorem ec_point_local_window[local]:
  local_region cenv es.scopes s n b sz /\
  b <= w2n w /\
  w2n w + val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v <= b + sz /\
  (dynarray_local cenv n /\
   ~dynarray_type (ArrayT (BaseT (UintT 256)) (Fixed 2)) ==>
   b + 32 <= w2n w) /\
  locals_kept cenv es s s' ==>
  mem_bytes_at (w2n w) 64 s'.vs_memory =
  mem_bytes_at (w2n w) 64 s.vs_memory
Proof
  simp[ec_point_footprint, dynarray_type_def] >> strip_tac >>
  gvs[locals_kept_def] >> first_x_assum irule >>
  qexistsl_tac [`b`, `n`, `sz`] >> simp[]
QED

Theorem ec_uint256_encoding[local]:
  value_has_type (BaseTV (UintT 256)) v ==>
  ?i. v = IntV i /\ 0 <= i /\ Num i < 2 ** 256 /\
      typed_val_to_w256 (BaseTV (UintT 256)) v = n2w (Num i)
Proof
  Cases_on `v` >> simp[value_has_type_def, typed_val_to_w256_def,
    val_to_w256_def, integer_wordTheory.i2w_def] >>
  strip_tac >> `~(i < 0)` by intLib.ARITH_TAC >> simp[]
QED

Theorem ec_point_index_memory[local]:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (ArrayV av) /\
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
    (ArrayV av) off mem /\ j < 2 ==>
  ?i. array_index (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) av (&j) =
        SOME (IntV i) /\
      0 <= i /\ Num i < 2 ** 256 /\
      mem_word_at (off + j * 32) mem = n2w (Num i)
Proof
  Cases_on `av` >> simp[value_has_type_def, val_in_memory_def] >>
  strip_tac >>
  Cases_on `ALOOKUP l j`
  >- (simp[array_index_def, default_value_def] >>
      first_x_assum (qspec_then `j` mp_tac) >>
      simp[default_value_def, val_in_memory_def, type_memory_size_def,
           val_to_w256_def, integer_wordTheory.i2w_def]) >>
  drule_all valueEncodingProofsTheory.sparse_has_type_lookup >>
  disch_then (strip_assume_tac o REWRITE_RULE [value_has_type_def]) >>
  drule ec_uint256_encoding >> strip_tac >> gvs[] >>
  drule_all kvs_in_memory_lookup >>
  simp[array_index_def, val_in_memory_def, type_memory_size_def,
       val_to_w256_def, integer_wordTheory.i2w_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >> simp[]
QED
Theorem ec_point_typed_extract[local]:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v ==>
  ?x y. extract_ec_point v = SOME (x,y) /\
        0 <= x /\ Num x < 2 ** 256 /\
        0 <= y /\ Num y < 2 ** 256
Proof
  strip_tac >>
  drule extract_ec_point_uint256_2_not_none >>
  Cases_on `extract_ec_point v` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `v` >> gvs[extract_ec_point_def, AllCaseEqs()] >>
  imp_res_tac array_index_has_type >>
  gvs[value_has_type_def, well_formed_type_value_def]
QED

Theorem ec_point_memory_words[local]:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v op s ==>
  ?w x y. eval_operand op s = SOME w /\
    extract_ec_point v = SOME (x,y) /\
    0 <= x /\ Num x < 2 ** 256 /\ 0 <= y /\ Num y < 2 ** 256 /\
    mem_word_at (w2n w) s.vs_memory = n2w (Num x) /\
    mem_word_at (w2n w + 32) s.vs_memory = n2w (Num y)
Proof
  strip_tac >>
  gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
      type_slot_size_def, wordsTheory.dimword_def] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  drule ec_point_index_memory >> disch_then drule >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  drule ec_point_index_memory >> disch_then drule >>
  disch_then (qspec_then `1` mp_tac) >> simp[] >> strip_tac >>
  simp[extract_ec_point_def] >> metis_tac[]
QED

Theorem ec_point_operand_kept[local]:
  expr_post func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_post func cenv cx e2 es1 s1 s2 t es' v2 y u /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  (!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w) /\
  local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
  s1.cs_next_id <= s2.cs_next_id ==>
  expr_val_rel cx (expr_type e1) v1 x u /\
  expr_val_at cenv cx (expr_type e1) sa s2 es' v1 x u
Proof
  strip_tac >>
  `?w. eval_operand x t = SOME w` by
    fs[expr_post_def, expr_val_rel_def] >>
  `eval_operand x u = SOME w` by metis_tac[] >>
  `expr_val_at cenv cx (expr_type e1) sa s1 es1 v1 x t` by
    gvs[expr_post_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  strip_tac
  >- (`expr_val_in_alloca cenv cx (expr_type e1) sa s1 es1 v1 x t` by
        (simp[expr_val_in_alloca_def, evaluate_type_def, is_word_type_def,
              type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
         qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
      drule_all expr_post_operand_kept_stable >> strip_tac >>
      drule expr_val_in_alloca_at >> strip_tac >>
      gvs[expr_val_at_def, evaluate_type_def, is_word_type_def,
          type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
      metis_tac[]) >>
  conj_tac
  >- (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _`)
    expr_post_operand_local_kept >>
  simp[is_word_type_def, dynarray_type_def, evaluate_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  disch_then irule >>
  simp[is_word_type_def, dynarray_type_def, evaluate_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  conj_tac >- gvs[expr_post_def] >>
  qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
  gvs[dynarray_type_def]) >>
  `local_region cenv es'.scopes u n b sz` by
    (irule exprSimOpsTheory.local_region_frame_fwd >>
     qexistsl_tac [`t`, `s1`, `es1.scopes`] >> simp[] >>
     gvs[expr_post_def]) >>
  simp[expr_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  disj2_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[] >>
  gvs[dynarray_type_def]
QED

Theorem ecadd_precompile_words[local]:
  precompile_result 6w
    (word_to_bytes (x1:bytes32) T ++ word_to_bytes (y1:bytes32) T ++
     word_to_bytes (x2:bytes32) T ++ word_to_bytes (y2:bytes32) T) =
  SOME (OPTION_MAP (\(x,y).
    PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
    (vfmExecution$ecadd (w2n x1,w2n y1) (w2n x2,w2n y2)))
Proof
  rewrite_tac[precompile_result_ecadd, take_pad_word_prefix] >>
  simp[take_pad_0_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, listTheory.TAKE_APPEND1,
       listTheory.DROP_APPEND, listTheory.TAKE_LENGTH_TOO_LONG,
       listTheory.DROP_LENGTH_TOO_LONG, PAD_RIGHT,
       num_of_be_bytes_word32, word_to_bytes_word_of_bytes_32,
       word_of_bytes_be_def]
QED

Theorem ecmul_precompile_words[local]:
  precompile_result 7w
    (word_to_bytes (x:bytes32) T ++ word_to_bytes (y:bytes32) T ++
     word_to_bytes (n:bytes32) T) =
  SOME (OPTION_MAP (\(x,y).
    PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
    (vfmExecution$ecmul (w2n x,w2n y) (w2n n)))
Proof
  rewrite_tac[precompile_result_ecmul, take_pad_word_prefix] >>
  simp[take_pad_0_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, listTheory.TAKE_APPEND1,
       listTheory.DROP_APPEND, listTheory.TAKE_LENGTH_TOO_LONG,
       listTheory.DROP_LENGTH_TOO_LONG, PAD_RIGHT,
       num_of_be_bytes_word32, word_to_bytes_word_of_bytes_32,
       word_of_bytes_be_def]
QED

Theorem ecadd_success_bounds[local]:
  vfmExecution$ecadd a b = SOME (x,y) ==>
  x < 2 ** 256 /\ y < 2 ** 256
Proof
  simp[vfmExecutionTheory.ecadd_def, AllCaseEqs()] >> strip_tac >>
  mp_tac (Q.SPECL [`a`, `b`] addAffine_bounded) >> gvs[]
QED

Theorem ecmul_success_bounds[local]:
  vfmExecution$ecmul a n = SOME (x,y) ==>
  x < 2 ** 256 /\ y < 2 ** 256
Proof
  simp[vfmExecutionTheory.ecmul_def, AllCaseEqs()] >> strip_tac >>
  mp_tac (Q.SPECL [`a`, `n`] mulAffine_bounded) >>
  PairCases_on `a` >> gvs[bn254Theory.validAffine_def]
QED

Theorem ec_result_memory[local]:
  mem_word_at off mem = n2w x /\ mem_word_at (off + 32) mem = n2w y ==>
  val_in_memory (ArrayTV (BaseTV (UintT 256)) (Fixed 2))
    (mk_ec_result (x,y)) off mem
Proof
  strip_tac >>
  simp[mk_ec_result_def, make_array_value_def, enumerate_static_array_def,
       default_value_def] >>
  Cases_on `x = 0` >> Cases_on `y = 0` >>
  gvs[val_in_memory_def, val_to_w256_def, integer_wordTheory.i2w_def,
      type_memory_size_def, default_value_def] >>
  rpt strip_tac >> `i = 0 \/ i = 1` by decide_tac >> gvs[]
QED

Theorem ecadd_source_result[local]:
  extract_ec_point v1 = SOME (x1,y1) /\
  extract_ec_point v2 = SOME (x2,y2) ==>
  evaluate_ecadd [v1;v2] =
    case vfmExecution$ecadd (Num x1,Num y1) (Num x2,Num y2) of
      NONE => INR (RuntimeError "ECAdd invalid point")
    | SOME r => INL (mk_ec_result r)
Proof
  simp[evaluate_ecadd_def]
QED

Theorem ecmul_source_result[local]:
  extract_ec_point v = SOME (x,y) ==>
  evaluate_ecmul [v;IntV scalar] =
    case vfmExecution$ecmul (Num x,Num y) (Num scalar) of
      NONE => INR (RuntimeError "ECMul invalid point")
    | SOME r => INL (mk_ec_result r)
Proof
  simp[evaluate_ecmul_def]
QED

Theorem ecadd_precompile_success[local]:
  vfmExecution$ecadd (w2n x1,w2n y1) (w2n x2,w2n y2) = SOME (x,y) ==>
  precompile_result 6w
    (word_to_bytes (x1:bytes32) T ++ word_to_bytes (y1:bytes32) T ++
     word_to_bytes (x2:bytes32) T ++ word_to_bytes (y2:bytes32) T) =
  SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T))
Proof
  strip_tac >> drule ecadd_success_bounds >> strip_tac >>
  simp[ecadd_precompile_words, padded_num_to_be_bytes_word32]
QED

Theorem ecmul_precompile_success[local]:
  vfmExecution$ecmul (w2n px,w2n py) (w2n scalar) = SOME (x,y) ==>
  precompile_result 7w
    (word_to_bytes (px:bytes32) T ++ word_to_bytes (py:bytes32) T ++
     word_to_bytes (scalar:bytes32) T) =
  SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T))
Proof
  strip_tac >> drule ecmul_success_bounds >> strip_tac >>
  simp[ecmul_precompile_words, padded_num_to_be_bytes_word32]
QED

Theorem ec_result_bytes_length[local]:
  LENGTH (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T) = 64
Proof
  simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem ecadd_points_code_shape[local]:
  compile_ecadd_points p1 p2 sa = (op,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_ecadd_points_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       same_blocks_def, mk_inst_def, is_terminator_def]
QED

Theorem ecmul_point_code_shape[local]:
  compile_ecmul_point p scalar sa = (op,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_ecmul_point_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       same_blocks_def, mk_inst_def, is_terminator_def]
QED

Theorem ec_emit_mload_run[local]:
  emit_op MLOAD [pop] sa = (dst,sb) /\
  eval_operand pop s = SOME w ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (mem_word_at (w2n w) s.vs_memory) s)
Proof
  strip_tac >> drule emitHelperPropsTheory.emitted_insts_emit_op >>
  strip_tac >> simp[run_inst_seq_def] >>
  drule emitHelperPropsTheory.step_MLOAD >>
  simp[valueEncodingPropsTheory.mem_word_at_eq_mload]
QED

(* Each interleaved scratch write keeps both words of every disjoint point.
   The two point operands themselves need not be disjoint. *)
Theorem ec_point_words_scratch_store[local]:
  !base sz point off w s.
  regions_disjoint base sz point 64 /\ off + 32 <= sz ==>
  mem_word_at point (mstore (base + off) w s).vs_memory =
    mem_word_at point s.vs_memory /\
  mem_word_at (point + 32) (mstore (base + off) w s).vs_memory =
    mem_word_at (point + 32) s.vs_memory
Proof
  rpt gen_tac >> simp[compileEnvTheory.regions_disjoint_def] >>
  strip_tac >> conj_tac >>
  irule valueEncodingPropsTheory.mstore_mem_word_at_disjoint >> decide_tac
QED

(* A single point word is loaded before its scratch store, in the exact
   four-instruction order emitted by both EC lowering helpers. *)
Theorem ec_point_word_transfer_run[local]:
  (do src <- emit_op ADD [point_op; Lit poff];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value]
   od) sa = ((),sb) /\
  eval_operand point_op s = SOME point /\
  eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword + boff))
        (mem_word_at (w2n (point + poff)) s.vs_memory) s).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  `!q k z t. MEM q [point_op;base_op] /\ sa.cs_next_var <= k ==>
     eval_operand q (update_var (STRING #"%" (toString k)) z t) =
     eval_operand q t` by
    (rpt gen_tac >> strip_tac >> Cases_on `q` >>
     simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
     IF_CASES_TAC >> gvs[] >>
     qpat_x_assum `!x. _ ==> not_fresh_at sa x`
       (qspec_then `STRING #"%" (toString k)` mp_tac) >>
     simp[not_fresh_at_def]) >>
  qpat_x_assum `_ sa = ((),sb)` mp_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_pure2_def, bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_read1_def,
       bind_outputs_def, eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var,
       valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[run_inst_seq_def] >>
  qpat_x_assum `!q k z t. _` kall_tac >>
  simp[mload_def, mstore_def, update_var_def] >>
  rpt strip_tac >> simp[emitHelperPropsTheory.lookup_var_update_var] >>
  gvs[not_fresh_at_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ec_point_word_transfer_shape[local]:
  (do src <- emit_op ADD [point_op; Lit poff];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value]
   od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 3 /\
  sb.cs_next_id = sa.cs_next_id + 4
Proof
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem ec_point_transfers_run[local]:
  (do src <- emit_op ADD [point_op; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  (do src <- emit_op ADD [point_op; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit (boff+32w)];
      emit_void MSTORE [dst; value] od) sb = ((),sc) /\
  eval_operand point_op s = SOME point /\ eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n (bword+boff) + 64 < dimword (:256) /\
  regions_disjoint (w2n (bword+boff)) 64 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword+boff)+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n (bword+boff)) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  drule_all ec_point_word_transfer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK s1` >>
  qpat_assum `_ sa = ((),sb)`
    (strip_assume_tac o MATCH_MP ec_point_word_transfer_shape) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `_ = s`
       (mp_tac o AP_TERM ``\st. st.vs_labels``) >> simp[]) >>
  `eval_operand point_op s1 = SOME point /\ eval_operand base_op s1 = SOME bword` by
    (conj_tac >> Cases_on `point_op` >> Cases_on `base_op` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sb x` by metis_tac[] >>
  drule_all ec_point_word_transfer_run >> strip_tac >>
  `w2n (point+32w) = w2n point+32 /\
   w2n ((bword+boff)+32w) = w2n (bword+boff)+32` by
    (conj_tac >> irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `mem_word_at (w2n point+32) s1.vs_memory =
   mem_word_at (w2n point+32) s.vs_memory` by
    (simp[] >> irule valueEncodingPropsTheory.mstore_mem_word_at_disjoint >>
     gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  qexists_tac `t` >> conj_tac >- metis_tac[run_inst_seq_append] >>
  conj_tac
  >- (qpat_x_assum `t.vs_memory = _` mp_tac >>
      qpat_x_assum `s1.vs_memory = _` mp_tac >>
      pure_asm_rewrite_tac [wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_0] >>
      ntac 2 strip_tac >>
      qpat_x_assum `t.vs_memory = _` SUBST1_TAC >>
      drule mstore_equal_memory >>
      disch_then (qspecl_then
        [`w2n (bword+boff)+32`, `mem_word_at (w2n point+32) s.vs_memory`]
        mp_tac) >> simp[NoAsms]) >>
  conj_tac
  >- (qpat_assum `_ = s1`
        (mp_tac o AP_TERM ``\st. st with
          <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>``) >> simp[]) >>
  metis_tac[]
QED

(* Scratch separation consumes the allocation/local placement disjunction,
   rather than assuming that every point came from a fresh allocation. *)
Theorem ec_point_scratch_disjoint[local]:
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa sb es v pop s /\
  eval_operand pop s = SOME w /\
  (!aid b sz. aid < sb.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint scratch scratch_size b sz) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint scratch scratch_size b sz) ==>
  regions_disjoint scratch scratch_size (w2n w) 64
Proof
  simp[expr_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  strip_tac >> gvs[]
  >- (first_x_assum drule >> simp[] >>
      simp[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  first_x_assum drule >>
  simp[compileEnvTheory.regions_disjoint_def] >> decide_tac
QED

Theorem ec_result_val_wf[local]:
  val_wf (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (mk_ec_result (x,y))
Proof
  simp[mk_ec_result_def, make_array_value_def, enumerate_static_array_def,
       default_value_def] >>
  Cases_on `x = 0` >> Cases_on `y = 0` >>
  simp[val_wf_def, type_memory_size_def]
QED

Theorem ec_result_pointer_post[local]:
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  stmt_state_rel func cenv cx es' t /\ wb_frame cenv es sa s0 t /\
  eval_operand pop t = SOME w /\
  mem_bytes_at (w2n w) 64 t.vs_memory =
    word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,64) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b sz. local_region cenv es'.scopes t name b sz ==>
     regions_disjoint (w2n w) 64 b sz) ==>
  vv_post func cenv cx e es sa sb s0 es' (Value (mk_ec_result (x,y)))
    (FST (as_ptr_val (expr_type e) LocMemory (pop,sb))) t
Proof
  strip_tac >>
  `mem_bytes_at (w2n w) 32 t.vs_memory = word_to_bytes (n2w x:bytes32) T /\
   mem_bytes_at (w2n w+32) 32 t.vs_memory = word_to_bytes (n2w y:bytes32) T` by
    (irule mem_bytes_at_split_eq >>
     simp[LENGTH_word_to_bytes, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  `mem_word_at (w2n w) t.vs_memory = n2w x /\
   mem_word_at (w2n w+32) t.vs_memory = n2w y` by
    gvs[mem_bytes_at_word_eq] >>
  drule_all ec_result_memory >> strip_tac >>
  simp[exprLoweringTheory.as_ptr_val_def, contextTheory.mk_ptr_def,
       vv_post_def, vv_holds_def, vv_at_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def,
       evaluate_type_def, is_word_type_def, ec_result_val_wf,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  conj_tac
  >- (disj1_tac >> qexistsl_tac [`aid`, `w2n w`, `64`] >>
      simp[] >> gvs[compileEnvTheory.regions_disjoint_def]) >>
  gvs[exprSimWordArgsTheory.wb_frame_def] >> metis_tac[]
QED

Theorem ec_point_fresh_scratch_disjoint[local]:
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sa es v pop s /\
  eval_operand pop s = SOME w /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint scratch len b sz) /\
  (!name b sz. local_region cenv es.scopes t name b sz ==>
     regions_disjoint scratch len b sz) ==>
  regions_disjoint scratch len (w2n w) 64
Proof
  strip_tac >> irule ec_point_scratch_disjoint >>
  qexistsl_tac [`cenv`, `cx`, `es`, `pop`, `s`, `lo`, `sa`, `v`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
      irule exprSimOpsTheory.local_region_frame_fwd >>
      qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]) >>
  metis_tac[]
QED

Theorem ecadd_input_stores_shape[local]:
  (do xp <- emit_op ADD [p1; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p1; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp2 <- emit_op ADD [p2; Lit 0w];
      x2 <- emit_op MLOAD [xp2];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x2];
      yp2 <- emit_op ADD [p2; Lit 32w];
      y2 <- emit_op MLOAD [yp2];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y2] od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 12 /\
  sb.cs_next_id = sa.cs_next_id + 16
Proof
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem ecmul_input_stores_shape[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 7 /\
  sb.cs_next_id = sa.cs_next_id + 10
Proof
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem ecmul_buffers_shape[local]:
  (do ib <- context$compile_alloc_buffer 96;
      xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [dst2; scalar];
      ob <- context$compile_alloc_buffer 64;
      return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) ==>
  ?ib sa sb ob.
    context$compile_alloc_buffer 96 sf = (ib,sa) /\
    (do xp <- emit_op ADD [p; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst1; y];
        dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
    context$compile_alloc_buffer 64 sb = (ob,sm) /\
    ip = ib.buf_operand /\ op = ob.buf_operand /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sm /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
    local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sb.cs_next_id < sm.cs_next_id /\
    (?x. ip = Var x /\ not_fresh_at sa x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >>
  ` (do ib <- context$compile_alloc_buffer 96;
        (do xp <- emit_op ADD [p; Lit 0w];
            x <- emit_op MLOAD [xp];
            dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
            emit_void MSTORE [dst0; x];
            yp <- emit_op ADD [p; Lit 32w];
            y <- emit_op MLOAD [yp];
            dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
            emit_void MSTORE [dst1; y];
            dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
            emit_void MSTORE [dst2; scalar] od);
        ob <- context$compile_alloc_buffer 64;
        return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  drule (BETA_RULE (Q.INST [`payload` |->
    `\ib. do xp <- emit_op ADD [p; Lit 0w];
             x <- emit_op MLOAD [xp];
             dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
             emit_void MSTORE [dst0; x];
             yp <- emit_op ADD [p; Lit 32w];
             y <- emit_op MLOAD [yp];
             dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
             emit_void MSTORE [dst1; y];
             dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
             emit_void MSTORE [dst2; scalar] od`] (SPEC_ALL allocated_payload_shape))) >>
  disch_then (qspecl_then [`func`, `cenv`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> drule ecmul_input_stores_shape >> simp[]) >>
  strip_tac >> gvs[] >>
  drule ecmul_input_stores_shape >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem ecadd_buffers_shape[local]:
  (do ib <- context$compile_alloc_buffer 128;
      xp <- emit_op ADD [p1; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p1; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp2 <- emit_op ADD [p2; Lit 0w];
      x2 <- emit_op MLOAD [xp2];
      dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [dst2; x2];
      yp2 <- emit_op ADD [p2; Lit 32w];
      y2 <- emit_op MLOAD [yp2];
      dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [dst3; y2];
      ob <- context$compile_alloc_buffer 64;
      return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) ==>
  ?ib sa sb ob.
    context$compile_alloc_buffer 128 sf = (ib,sa) /\
    (do xp <- emit_op ADD [p1; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p1; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst1; y];
        xp2 <- emit_op ADD [p2; Lit 0w];
        x2 <- emit_op MLOAD [xp2];
        dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst2; x2];
        yp2 <- emit_op ADD [p2; Lit 32w];
        y2 <- emit_op MLOAD [yp2];
        dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [dst3; y2] od) sa = ((),sb) /\
    context$compile_alloc_buffer 64 sb = (ob,sm) /\
    ip = ib.buf_operand /\ op = ob.buf_operand /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sb ++
      emitted_insts sb sm /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sb.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
    local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    sb.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id < sb.cs_next_id /\
    sb.cs_next_id < sm.cs_next_id /\
    (?x. ip = Var x /\ not_fresh_at sa x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >>
  ` (do ib <- context$compile_alloc_buffer 128;
        (do xp <- emit_op ADD [p1; Lit 0w];
            x <- emit_op MLOAD [xp];
            dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
            emit_void MSTORE [dst0; x];
            yp <- emit_op ADD [p1; Lit 32w];
            y <- emit_op MLOAD [yp];
            dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
            emit_void MSTORE [dst1; y];
            xp2 <- emit_op ADD [p2; Lit 0w];
            x2 <- emit_op MLOAD [xp2];
            dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
            emit_void MSTORE [dst2; x2];
            yp2 <- emit_op ADD [p2; Lit 32w];
            y2 <- emit_op MLOAD [yp2];
            dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
            emit_void MSTORE [dst3; y2] od);
        ob <- context$compile_alloc_buffer 64;
        return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  drule (BETA_RULE (Q.INST [`payload` |->
    `\ib. do xp <- emit_op ADD [p1; Lit 0w];
             x <- emit_op MLOAD [xp];
             dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
             emit_void MSTORE [dst0; x];
             yp <- emit_op ADD [p1; Lit 32w];
             y <- emit_op MLOAD [yp];
             dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
             emit_void MSTORE [dst1; y];
             xp2 <- emit_op ADD [p2; Lit 0w];
             x2 <- emit_op MLOAD [xp2];
             dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
             emit_void MSTORE [dst2; x2];
             yp2 <- emit_op ADD [p2; Lit 32w];
             y2 <- emit_op MLOAD [yp2];
             dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
             emit_void MSTORE [dst3; y2] od`] (SPEC_ALL allocated_payload_shape))) >>
  disch_then (qspecl_then [`func`, `cenv`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> drule ecadd_input_stores_shape >> simp[]) >>
  strip_tac >> gvs[] >>
  drule ecadd_input_stores_shape >> strip_tac >> simp[] >> metis_tac[]
QED

(* Package the two interleaved transfers as the actual point payload. *)
Theorem ec_point_pair_transfer_run[local]:
  (do src <- emit_op ADD [point_op; Lit 0w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit boff];
      emit_void MSTORE [dst; value];
      src <- emit_op ADD [point_op; Lit 32w];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [base_op; Lit (boff+32w)];
      emit_void MSTORE [dst; value] od) sa = ((),sc) /\
  eval_operand point_op s = SOME point /\ eval_operand base_op s = SOME bword /\
  (!x. MEM (Var x) [point_op;base_op] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n (bword+boff) + 64 < dimword (:256) /\
  regions_disjoint (w2n (bword+boff)) 64 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n (bword+boff)+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n (bword+boff)) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  ` (do (do src <- emit_op ADD [point_op; Lit 0w];
            value <- emit_op MLOAD [src];
            dst <- emit_op ADD [base_op; Lit boff];
            emit_void MSTORE [dst; value] od);
        src <- emit_op ADD [point_op; Lit 32w];
        value <- emit_op MLOAD [src];
        dst <- emit_op ADD [base_op; Lit (boff+32w)];
        emit_void MSTORE [dst; value] od) sa = ((),sc)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  pop_assum mp_tac >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >> rename1 `_ sa = (u,sb)` >>
  Cases_on `u` >> strip_tac >>
  drule_all ec_point_transfers_run >> strip_tac >>
  qpat_assum `_ sa = ((),sb)`
    (strip_assume_tac o MATCH_MP ec_point_word_transfer_shape) >>
  qpat_assum `_ sb = ((),sc)`
    (strip_assume_tac o MATCH_MP ec_point_word_transfer_shape) >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >> simp[rich_listTheory.DROP_APPEND1]) >>
  qexists_tac `t` >> simp[] >> gvs[venom_state_component_equality]
QED

Theorem ecmul_input_stores_run[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;ib;scalar] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\ w2n bw + 96 < dimword (:256) /\
  regions_disjoint (w2n bw) 96 (w2n point) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+64) wscalar
        (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
          (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  ` (do (do xp <- emit_op ADD [p; Lit 0w];
            x <- emit_op MLOAD [xp];
            dst0 <- emit_op ADD [ib; Lit 0w];
            emit_void MSTORE [dst0; x];
            yp <- emit_op ADD [p; Lit 32w];
            y <- emit_op MLOAD [yp];
            dst1 <- emit_op ADD [ib; Lit 32w];
            emit_void MSTORE [dst1; y] od);
        dst2 <- emit_op ADD [ib; Lit 64w];
        emit_void MSTORE [dst2; scalar] od) sa = ((),sb)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  pop_assum mp_tac >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >> rename1 `_ sa = (u,sc)` >>
  Cases_on `u` >> strip_tac >>
  `!x. MEM (Var x) [p;ib] ==> not_fresh_at sa x` by
    (gvs[] >> metis_tac[]) >>
  `w2n bw + 64 < dimword (:256) /\
   regions_disjoint (w2n bw) 64 (w2n point) 64` by
    (gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  drule (Q.INST [`boff` |-> `0w`] (SPEC_ALL ec_point_pair_transfer_run)
    |> SRULE [wordsTheory.WORD_ADD_0]) >>
  disch_then (qspecl_then [`s`, `point`, `bw`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK s1` >>
  `sc.cs_next_var = sa.cs_next_var + 6 /\
   sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    (qpat_x_assum `_ sa = ((),sc)` mp_tac >>
     simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `_ with <|vs_memory := _; vs_vars := _|> = _`
      (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  `eval_operand ib s1 = SOME bw /\ eval_operand scalar s1 = SOME wscalar` by
    (conj_tac >> Cases_on `ib` >> Cases_on `scalar` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [ib;scalar] ==> not_fresh_at sc x` by
    (gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  qpat_x_assum `_ sc = ((),sb)` mp_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  `eval_operand scalar
      (update_var (STRING #"%" (toString (sa.cs_next_var+6))) (bw+64w) s1) =
    SOME wscalar` by
    (Cases_on `scalar` >> gvs[eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var] >>
     IF_CASES_TAC >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  once_rewrite_tac[emitted_insts_def] >>
  simp[rich_listTheory.DROP_APPEND1] >> rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_assum `run_inst_seq (emitted_insts sa sc) s = _`
    (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
  simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
       exec_pure2_def, bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, step_inst_base_def, exec_write2_def,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  simp[run_inst_seq_def] >>
  `w2n (bw+64w) = w2n bw+64` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  conj_tac
  >- (simp[GSYM dftCommutationTheory.update_var_mstore_commute, update_var_def] >>
      drule mstore_equal_memory >>
      disch_then (qspecl_then [`w2n bw+64`, `wscalar`] mp_tac) >> simp[]) >>
  conj_tac
  >- (simp[mstore_def, update_var_def, NoAsms] >>
      first_assum ACCEPT_TAC) >>
  rpt strip_tac >> simp[emitHelperPropsTheory.lookup_var_update_var] >>
  IF_CASES_TAC
  >- (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  metis_tac[]
QED

Theorem ecadd_input_stores_run[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp <- emit_op ADD [q; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x];
      yp <- emit_op ADD [q; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) [p;q;ib] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\ w2n bw + 128 < dimword (:256) /\
  regions_disjoint (w2n bw) 128 (w2n point) 64 /\
  regions_disjoint (w2n bw) 128 (w2n point2) 64 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+96) (mem_word_at (w2n point2+32) s.vs_memory)
        (mstore (w2n bw+64) (mem_word_at (w2n point2) s.vs_memory)
          (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
            (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s)))).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >>
  ` (do (do xp <- emit_op ADD [p; Lit 0w];
            x <- emit_op MLOAD [xp];
            dst0 <- emit_op ADD [ib; Lit 0w];
            emit_void MSTORE [dst0; x];
            yp <- emit_op ADD [p; Lit 32w];
            y <- emit_op MLOAD [yp];
            dst1 <- emit_op ADD [ib; Lit 32w];
            emit_void MSTORE [dst1; y] od);
        xp <- emit_op ADD [q; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst2 <- emit_op ADD [ib; Lit 64w];
        emit_void MSTORE [dst2; x];
        yp <- emit_op ADD [q; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst3 <- emit_op ADD [ib; Lit 96w];
        emit_void MSTORE [dst3; y] od) sa = ((),sb)` by
    (simp[comp_ignore_bind_def, comp_bind_assoc] >>
     simp[GSYM comp_ignore_bind_def]) >>
  pop_assum mp_tac >>
  simp[Once comp_ignore_bind_def, Once comp_bind_def] >>
  pairarg_tac >> simp[] >> rename1 `_ sa = (u,sc)` >>
  Cases_on `u` >> strip_tac >>
  `!x. MEM (Var x) [p;ib] ==> not_fresh_at sa x` by
    (gvs[] >> metis_tac[]) >>
  `w2n bw + 64 < dimword (:256) /\
   regions_disjoint (w2n bw) 64 (w2n point) 64` by
    (gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  drule (Q.INST [`boff` |-> `0w`] (SPEC_ALL ec_point_pair_transfer_run)
    |> SRULE [wordsTheory.WORD_ADD_0]) >>
  disch_then (qspecl_then [`s`, `point`, `bw`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK s1` >>
  qpat_x_assum `_ sa = ((),sb)` kall_tac >>
  `sc.cs_next_var = sa.cs_next_var + 6 /\
   sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    (qpat_x_assum `_ sa = ((),sc)` mp_tac >>
     simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `_ with <|vs_memory := _; vs_vars := _|> = _`
      (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  `eval_operand q s1 = SOME point2 /\ eval_operand ib s1 = SOME bw` by
    (conj_tac >> Cases_on `q` >> Cases_on `ib` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [q;ib] ==> not_fresh_at sc x` by
    (gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  `w2n (bw+64w) = w2n bw+64` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `w2n (bw+64w) + 64 < dimword (:256) /\
   regions_disjoint (w2n (bw+64w)) 64 (w2n point2) 64` by
    (gvs[compileEnvTheory.regions_disjoint_def] >> decide_tac) >>
  drule (Q.INST [`boff` |-> `64w`] (SPEC_ALL ec_point_pair_transfer_run)
    |> SRULE [wordsTheory.word_add_n2w]) >>
  disch_then (qspecl_then [`s1`, `point2`, `bw`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  `sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb` by
    (qpat_x_assum `_ sc = ((),sb)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  qpat_x_assum `_ sa = ((),sc)` kall_tac >>
  `emitted_insts sa sb = emitted_insts sa sc ++ emitted_insts sc sb` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  `mem_word_at (w2n point2) s1.vs_memory = mem_word_at (w2n point2) s.vs_memory /\
   mem_word_at (w2n point2+32) s1.vs_memory =
     mem_word_at (w2n point2+32) s.vs_memory` by
    (qspecl_then [`w2n bw`, `128`, `w2n point2`, `32`,
       `mem_word_at (w2n point+32) s.vs_memory`,
       `mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s`]
       mp_tac ec_point_words_scratch_store >> simp[] >>
     qspecl_then [`w2n bw`, `128`, `w2n point2`, `0`,
       `mem_word_at (w2n point) s.vs_memory`, `s`]
       mp_tac ec_point_words_scratch_store >> simp[]) >>
  qexists_tac `t` >>
  conj_tac
  >- (simp[] >> qpat_assum `run_inst_seq (emitted_insts sa sc) s = _`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `t.vs_memory = _` mp_tac >> simp[] >>
      drule mstore_equal_memory >>
      disch_then (qspecl_then [`w2n bw+64`, `mem_word_at (w2n point2) s.vs_memory`]
        (mp_tac o AP_TERM ``\z. z.vs_memory``)) >> simp[] >> strip_tac >>
      drule mstore_equal_memory >>
      disch_then (qspecl_then [`w2n bw+96`, `mem_word_at (w2n point2+32) s.vs_memory`]
        assume_tac) >> simp[]) >>
  conj_tac >- gvs[venom_state_component_equality] >>
  rpt strip_tac >>
  `not_fresh_at sc x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD,
       arithmeticTheory.LESS_EQ_TRANS]) >> metis_tac[]
QED

Theorem ecmul_input_stores_sim[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; scalar] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;ib;scalar] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\ w2n bw + 96 < dimword (:256) /\
  regions_disjoint (w2n bw) 96 (w2n point) 64 /\
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 96 b sz) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n bw) 96 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes wscalar T
Proof
  rpt strip_tac >> drule_all ecmul_input_stores_run >> strip_tac >>
  `!b len. regions_disjoint (w2n bw) 96 b len ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `b + len <= w2n bw \/ w2n bw + 96 <= b` by
       gvs[compileEnvTheory.regions_disjoint_def] >>
     simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]) >>
  drule_all scratch_memory_frame >> strip_tac >>
  qexists_tac `t` >> simp[scratch_three_word_stores]
QED

Theorem ecadd_input_stores_sim[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp <- emit_op ADD [q; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst2 <- emit_op ADD [ib; Lit 64w];
      emit_void MSTORE [dst2; x];
      yp <- emit_op ADD [q; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst3 <- emit_op ADD [ib; Lit 96w];
      emit_void MSTORE [dst3; y] od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand q s = SOME point2 /\
  eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) [p;q;ib] ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n point2 + 64 < dimword (:256) /\ w2n bw + 128 < dimword (:256) /\
  regions_disjoint (w2n bw) 128 (w2n point) 64 /\
  regions_disjoint (w2n bw) 128 (w2n point2) 64 /\
  stmt_state_rel func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 128 b sz) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n bw) 128 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2+32) s.vs_memory) T
Proof
  rpt strip_tac >> drule_all ecadd_input_stores_run >> strip_tac >>
  `!b len. regions_disjoint (w2n bw) 128 b len ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     `b + len <= w2n bw \/ w2n bw + 128 <= b` by
       gvs[compileEnvTheory.regions_disjoint_def] >>
     simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]) >>
  drule_all scratch_memory_frame >> strip_tac >>
  qexists_tac `t` >> simp[scratch_four_word_stores]
QED

Theorem ecmul_buffers_run[local]:
  (do ib <- context$compile_alloc_buffer 96;
      xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [dst1; y];
      dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [dst2; scalar];
      ob <- context$compile_alloc_buffer 64;
      return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) /\
  eval_operand p s = SOME point /\ eval_operand scalar s = SOME wscalar /\
  (!x. MEM (Var x) [p;scalar] ==> not_fresh_at sf x) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  w2n point + 64 < dimword (:256) ==>
  ?t pi po aid. run_inst_seq (emitted_insts sf sm) s = OK t /\
    stmt_state_rel func cenv cx es t /\ wb_frame cenv es sf s t /\
    eval_operand ip t = SOME pi /\ eval_operand op t = SOME po /\
    w2n pi + 96 < dimword (:256) /\ w2n po + 64 < dimword (:256) /\
    mem_bytes_at (w2n pi) 96 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes wscalar T /\
    FLOOKUP t.vs_allocas aid = SOME (w2n po,64) /\
    sf.cs_next_id <= aid /\ aid < sm.cs_next_id /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n po) 64 b sz) /\
    (!old b sz. old < sf.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (b,sz) ==>
      regions_disjoint (w2n po) 64 b sz) /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >> drule_all ecmul_buffers_shape >> strip_tac >>
  qpat_x_assum `_ sf = ((ip,op),sm)` kall_tac >>
  `96 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sa) s = OK s1` >>
  rename1 `FLOOKUP s1.vs_allocas sf.cs_next_id = SOME (w2n wi,96)` >>
  `regions_disjoint (w2n wi) 96 (w2n point) 64` by
    (drule_all ec_point_fresh_scratch_disjoint >> simp[]) >>
  `eval_operand p s1 = SOME point /\ eval_operand scalar s1 = SOME wscalar` by
    (conj_tac >> Cases_on `p` >> Cases_on `scalar` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [p;ib.buf_operand;scalar] ==> not_fresh_at sa x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!aid b sz. aid < sf.cs_next_id /\
     FLOOKUP s1.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wi) 96 b sz` by
    (rpt strip_tac >> irule state_allocations_disjoint >>
     qexistsl_tac [`sf.cs_next_id`,`aid`,`cenv`,`cx`,`es`,`func`,`s1`] >>
     simp[] >> decide_tac) >>
  `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
  drule_all ecmul_input_stores_sim >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s1 = OK s2` >>
  qpat_x_assum `do _ od sa = _` kall_tac >>
  qpat_x_assum `context$compile_alloc_buffer 96 _ = _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` kall_tac >>
  `s2.vs_allocas = s1.vs_allocas /\ s2.vs_labels = s1.vs_labels` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_labels)``) >> simp[]) >>
  `wb_frame cenv es sf s s2` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`es`,`sf`,`s1`] >> simp[]) >>
  `!z. not_fresh_at sf z ==> lookup_var z s2 = lookup_var z s` by
    (qx_gen_tac `z` >> strip_tac >>
     `not_fresh_at sa z` by
       (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[]) >>
  `!z. ip = Var z ==> not_fresh_at sb z` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand ip s2 = SOME wi` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`u` |-> `s2`, `outsz` |-> `64`, `input_word` |-> `wi`]
                 (SPEC_ALL alloc_buffer_finish)) >>
  (impl_tac >- (simp[wordsTheory.dimword_def] >> decide_tac)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sb sm) s2 = OK s3` >>
  rename1 `FLOOKUP s3.vs_allocas sb.cs_next_id = SOME (w2n wo,64)` >>
  qexistsl_tac [`s3`, `wi`, `wo`, `sb.cs_next_id`] >>
  conj_tac
  >- (asm_rewrite_tac[] >> rewrite_tac[GSYM APPEND_ASSOC] >>
      qpat_assum `run_inst_seq (emitted_insts sf sa) s = _`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      qpat_assum `run_inst_seq (emitted_insts sa sb) s1 = _`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      first_assum ACCEPT_TAC) >>
  gvs[eval_operand_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem ecadd_buffers_run[local]:
  (do ib <- context$compile_alloc_buffer 128;
      xp <- emit_op ADD [p1; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p1; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
      emit_void MSTORE [dst1; y];
      xp2 <- emit_op ADD [p2; Lit 0w];
      x2 <- emit_op MLOAD [xp2];
      dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
      emit_void MSTORE [dst2; x2];
      yp2 <- emit_op ADD [p2; Lit 32w];
      y2 <- emit_op MLOAD [yp2];
      dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
      emit_void MSTORE [dst3; y2];
      ob <- context$compile_alloc_buffer 64;
      return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)) /\
  eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME point2 /\
  (!x. MEM (Var x) [p1;p2] ==> not_fresh_at sf x) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v1 p1 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v2 p2 s /\
  w2n point + 64 < dimword (:256) /\ w2n point2 + 64 < dimword (:256) ==>
  ?t pi po aid. run_inst_seq (emitted_insts sf sm) s = OK t /\
    stmt_state_rel func cenv cx es t /\ wb_frame cenv es sf s t /\
    eval_operand ip t = SOME pi /\ eval_operand op t = SOME po /\
    w2n pi + 128 < dimword (:256) /\ w2n po + 64 < dimword (:256) /\
    mem_bytes_at (w2n pi) 128 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2+32) s.vs_memory) T /\
    FLOOKUP t.vs_allocas aid = SOME (w2n po,64) /\
    sf.cs_next_id <= aid /\ aid < sm.cs_next_id /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n po) 64 b sz) /\
    (!old b sz. old < sf.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (b,sz) ==>
      regions_disjoint (w2n po) 64 b sz) /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (?x. ip = Var x /\ not_fresh_at sm x) /\
    (?x. op = Var x /\ not_fresh_at sm x)
Proof
  rpt strip_tac >> drule_all ecadd_buffers_shape >> strip_tac >>
  qpat_x_assum `_ sf = ((ip,op),sm)` kall_tac >>
  `128 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sa) s = OK s1` >>
  rename1 `FLOOKUP s1.vs_allocas sf.cs_next_id = SOME (w2n wi,128)` >>
  `regions_disjoint (w2n wi) 128 (w2n point) 64` by
    (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ p2 _` kall_tac >>
     drule_all ec_point_fresh_scratch_disjoint >> simp[]) >>
  `regions_disjoint (w2n wi) 128 (w2n point2) 64` by
    (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ p1 _` kall_tac >>
     drule_all ec_point_fresh_scratch_disjoint >> simp[]) >>
  `eval_operand p1 s1 = SOME point /\ eval_operand p2 s1 = SOME point2` by
    (conj_tac >> Cases_on `p1` >> Cases_on `p2` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. MEM (Var x) [p1;p2;ib.buf_operand] ==> not_fresh_at sa x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!aid b sz. aid < sf.cs_next_id /\
     FLOOKUP s1.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wi) 128 b sz` by
    (rpt strip_tac >> irule state_allocations_disjoint >>
     qexistsl_tac [`sf.cs_next_id`,`aid`,`cenv`,`cx`,`es`,`func`,`s1`] >>
     simp[] >> decide_tac) >>
  `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
  drule_all ecadd_input_stores_sim >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s1 = OK s2` >>
  `wb_frame cenv es sf s s2` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`cx`,`func`] >> simp[]) >>
     qexistsl_tac [`es`,`sf`,`s1`] >> simp[]) >>
  `!z. not_fresh_at sf z ==> lookup_var z s2 = lookup_var z s` by
    (qx_gen_tac `z` >> strip_tac >>
     `not_fresh_at sa z` by
       (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >> simp[]) >>
  `!z. ip = Var z ==> not_fresh_at sb z` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand ip s2 = SOME wi` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`u` |-> `s2`, `outsz` |-> `64`, `input_word` |-> `wi`]
                 (SPEC_ALL alloc_buffer_finish)) >>
  (impl_tac >- (simp[wordsTheory.dimword_def] >> decide_tac)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sb sm) s2 = OK s3` >>
  rename1 `FLOOKUP s3.vs_allocas sb.cs_next_id = SOME (w2n wo,64)` >>
  qexistsl_tac [`s3`, `wi`, `wo`, `sb.cs_next_id`] >>
  conj_tac
  >- (asm_rewrite_tac[] >> rewrite_tac[GSYM APPEND_ASSOC] >>
      qpat_assum `run_inst_seq (emitted_insts sf sa) s = _`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      qpat_assum `run_inst_seq (emitted_insts sa sb) s1 = _`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      first_assum ACCEPT_TAC) >>
  gvs[eval_operand_def] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Theorem ecmul_point_prefix[local]:
  compile_ecmul_point p scalar sf = (res,sb) ==>
  ?ip op sm.
    (do ib <- context$compile_alloc_buffer 96;
        xp <- emit_op ADD [p; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst1; y];
        dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst2; scalar];
        ob <- context$compile_alloc_buffer 64;
        return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL [gas; Lit 7w; ip; Lit 96w; op; Lit 64w];
        emit_void ASSERT [success]; return op od) sm = (res,sb) /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    (!i. MEM i (emitted_insts sf sm) ==> MEM i (emitted_insts sf sb)) /\
    sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_id <= sb.cs_next_id /\
    (local_ptrs_reserved cenv sf ==> local_ptrs_reserved cenv sm)
Proof
  simp[compile_ecmul_point_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2,
       local_ptrs_reserved_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >>
  disch_then (qspecl_then [`n1`,`sz1`] strip_assume_tac) >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem ec_suffix_failure[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit 64w];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!z. ip = Var z ==> not_fresh_at sm z) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME NONE ==>
  ?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u
Proof
  strip_tac >> irule computed_suffix_failure >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`ip`,`op`,`64w`,`res`,`wo`] >> simp[]
QED

Theorem ec_suffix_pointer_post[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit 64w];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip st = SOME wi /\ eval_operand op st = SOME wo /\
  (!z. ip = Var z ==> not_fresh_at sm z) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\
  precompile_result (venom_call_request st target 0w wi insz T).cr_target
    (venom_call_request st target 0w wi insz T).cr_data =
    SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T)) /\
  stmt_state_rel func cenv cx es st /\ local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel func cenv cx es s0 /\ local_ptrs_reserved cenv sf /\
  wb_frame cenv es sf s0 st /\ w2n wo + 64 < dimword (:256) /\
  FLOOKUP st.vs_allocas aid = SOME (w2n wo,64) /\
  sf.cs_next_id <= aid /\ aid < sm.cs_next_id /\
  (!name b sz. local_region cenv es.scopes st name b sz ==>
     regions_disjoint (w2n wo) 64 b sz) /\
  (!old b sz. old < sf.cs_next_id /\ FLOOKUP st.vs_allocas old = SOME (b,sz) ==>
     regions_disjoint (w2n wo) 64 b sz) /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  ?t. run_inst_seq (emitted_insts sm sb) st = OK t /\
      vv_post func cenv cx e es sf sb s0 es (Value (mk_ec_result (x,y)))
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
Proof
  strip_tac >> drule_all computed_suffix_success >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ st = OK t` >>
  qexists `t` >> conj_tac >- simp[] >>
  qpat_x_assum `Abbrev _` kall_tac >>
  drule_all computed_suffix_output >> strip_tac >>
  `stmt_state_rel func cenv cx es t /\ wb_frame cenv es sf st t` by
    (irule computed_suffix_preserves >>
     simp[] >>
     goal_assum (drule_at (Pat `(_ : operand # compile_state) = _`)) >> simp[] >>
     metis_tac[]) >>
  `wb_frame cenv es sf s0 t` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`cx`,`func`] >> simp[]) >>
     qexistsl [`es`,`sf`,`st`] >> simp[]) >>
  `mem_bytes_at (w2n wo) 64 t.vs_memory =
    word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T` by
    (qpat_x_assum `t.vs_memory = _` (fn th => rewrite_tac[th]) >>
     simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, LENGTH_word_to_bytes,
          fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     irule (SRULE [LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
       (Q.INST [`bytes` |-> `word_to_bytes (n2w x:bytes32) T ++
                            word_to_bytes (n2w y:bytes32) T`]
         exprSimHashTheory.hash_write_memory_read_self))) >>
  drule computed_suffix_shape >> strip_tac >>
  `!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n wo) 64 b sz` by
    (rpt strip_tac >>
     qpat_x_assum `!name b sz. local_region cenv es.scopes st name b sz ==> _` irule >>
     qexists `name` >> irule exprSimOpsTheory.local_region_frame >>
     simp[] >> conj_tac
     >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sm`,`es.scopes`,`t`] >> simp[]) >>
  irule ec_result_pointer_post >> simp[] >>
  qexists `aid` >> gvs[] >> metis_tac[]
QED

Theorem ecmul_point_run[local]:
  compile_ecmul_point p scalar sf = (res,sb) /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand p s = SOME point /\ eval_operand scalar s = SOME wscalar /\
  (!z. MEM (Var z) [p;scalar] ==> not_fresh_at sf z) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  w2n point + 64 < dimword (:256) /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  case vfmExecution$ecmul
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n wscalar) of
    NONE => ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t
  | SOME (x,y) => ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
      vv_post func cenv cx e es sf sb s es (Value (mk_ec_result (x,y)))
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
Proof
  strip_tac >> drule ecmul_point_prefix >>
  disch_then (qspec_then `cenv` strip_assume_tac) >>
  qpat_x_assum `compile_ecmul_point _ _ _ = _` kall_tac >>
  `!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)` by metis_tac[] >>
  drule_all ecmul_buffers_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sm) s = OK st` >>
  rename1 `w2n wi + 96 < dimword (:256)` >>
  qpat_x_assum `do _ od sf = _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` kall_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[] >>
  `(!z. ip = Var z ==> not_fresh_at sm z) /\
   (!z. op = Var z ==> not_fresh_at sm z)` by
    (conj_tac >> rpt strip_tac >> gvs[]) >>
  `precompile_result (venom_call_request st 7w 0w wi 96w T).cr_target
      (venom_call_request st 7w 0w wi 96w T).cr_data =
    precompile_result 7w
      (word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
       word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
       word_to_bytes wscalar T)` by
    simp[venomCallOracleDefsTheory.venom_call_request_def, venomStateTheory.read_memory_def,
         GSYM mem_bytes_at_def, wordsTheory.dimword_def,
         wordsTheory.w2w_n2w, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  Cases_on `vfmExecution$ecmul
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n wscalar)`
  >- (`precompile_result (venom_call_request st 7w 0w wi 96w T).cr_target
         (venom_call_request st 7w 0w wi 96w T).cr_data = SOME NONE` by
        simp[ecmul_precompile_words] >>
      `?u. run_inst_seq (emitted_insts sm sb) st = Abort Revert_abort u` by
        (irule ec_suffix_failure >> goal_assum (drule_at Any) >> simp[] >>
         qexistsl [`ip`,`op`,`res`,`po`] >> simp[]) >>
      pop_assum strip_assume_tac >>
      drule run_inst_seq_append >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
      simp[]) >>
  rename1 `vfmExecution$ecmul _ _ = SOME r` >>
  PairCases_on `r` >> simp[] >>
  `precompile_result (venom_call_request st 7w 0w wi 96w T).cr_target
      (venom_call_request st 7w 0w wi 96w T).cr_data =
    SOME (SOME (word_to_bytes (n2w r0:bytes32) T ++ word_to_bytes (n2w r1:bytes32) T))` by
    (asm_rewrite_tac[] >> irule ecmul_precompile_success >> simp[]) >>
  `?t. run_inst_seq (emitted_insts sm sb) st = OK t /\
       vv_post func cenv cx e es sf sb s es (Value (mk_ec_result (r0,r1)))
         (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t` by
    (irule ec_suffix_pointer_post >> simp[] >>
     goal_assum (drule_at (Pat `(_ : operand # compile_state) = _`)) >> simp[] >>
     qexists_tac `aid` >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_assum `run_inst_seq (emitted_insts sf sm) s = OK st`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts sm sb` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ecadd_points_prefix[local]:
  compile_ecadd_points p1 p2 sf = (res,sb) ==>
  ?ip op sm.
    (do ib <- context$compile_alloc_buffer 128;
        xp <- emit_op ADD [p1; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p1; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
        emit_void MSTORE [dst1; y];
        xp2 <- emit_op ADD [p2; Lit 0w];
        x2 <- emit_op MLOAD [xp2];
        dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
        emit_void MSTORE [dst2; x2];
        yp2 <- emit_op ADD [p2; Lit 32w];
        y2 <- emit_op MLOAD [yp2];
        dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
        emit_void MSTORE [dst3; y2];
        ob <- context$compile_alloc_buffer 64;
        return (ib.buf_operand,ob.buf_operand) od) sf = ((ip,op),sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL [gas; Lit 6w; ip; Lit 128w; op; Lit 64w];
        emit_void ASSERT [success]; return op od) sm = (res,sb) /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    (!i. MEM i (emitted_insts sf sm) ==> MEM i (emitted_insts sf sb)) /\
    sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
    sm.cs_next_id <= sb.cs_next_id /\
    (local_ptrs_reserved cenv sf ==> local_ptrs_reserved cenv sm)
Proof
  simp[compile_ecadd_points_def, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_APPEND2,
       local_ptrs_reserved_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >>
  disch_then (qspecl_then [`n1`,`sz1`] strip_assume_tac) >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem ecadd_points_run[local]:
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME point2 /\
  (!z. MEM (Var z) [p1;p2] ==> not_fresh_at sf z) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v1 p1 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v2 p2 s /\
  w2n point + 64 < dimword (:256) /\ w2n point2 + 64 < dimword (:256) /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  case vfmExecution$ecadd
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory))
    (w2n (mem_word_at (w2n point2) s.vs_memory),
     w2n (mem_word_at (w2n point2+32) s.vs_memory)) of
    NONE => ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t
  | SOME (x,y) => ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
      vv_post func cenv cx e es sf sb s es (Value (mk_ec_result (x,y)))
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
Proof
  strip_tac >> drule ecadd_points_prefix >>
  disch_then (qspec_then `cenv` strip_assume_tac) >>
  qpat_x_assum `compile_ecadd_points _ _ _ = _` kall_tac >>
  `!i. MEM i (emitted_insts sf sm) ==> MEM i (fn_insts func)` by metis_tac[] >>
  drule_all ecadd_buffers_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sm) s = OK st` >>
  rename1 `w2n wi + 128 < dimword (:256)` >>
  qpat_x_assum `do _ od sf = _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ p1 _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ p2 _` kall_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[] >>
  `(!z. ip = Var z ==> not_fresh_at sm z) /\
   (!z. op = Var z ==> not_fresh_at sm z)` by
    (conj_tac >> rpt strip_tac >> gvs[]) >>
  `precompile_result (venom_call_request st 6w 0w wi 128w T).cr_target
      (venom_call_request st 6w 0w wi 128w T).cr_data =
    precompile_result 6w
      (word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
       word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
       word_to_bytes (mem_word_at (w2n point2) s.vs_memory) T ++
       word_to_bytes (mem_word_at (w2n point2+32) s.vs_memory) T)` by
    simp[venomCallOracleDefsTheory.venom_call_request_def, venomStateTheory.read_memory_def,
         GSYM mem_bytes_at_def, wordsTheory.dimword_def,
         wordsTheory.w2w_n2w, fcpLib.INDEX_CONV ``dimindex(:160)``] >>
  Cases_on `vfmExecution$ecadd
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory))
    (w2n (mem_word_at (w2n point2) s.vs_memory),
     w2n (mem_word_at (w2n point2+32) s.vs_memory))`
  >- (`precompile_result (venom_call_request st 6w 0w wi 128w T).cr_target
         (venom_call_request st 6w 0w wi 128w T).cr_data = SOME NONE` by
        simp[ecadd_precompile_words] >>
      `?u. run_inst_seq (emitted_insts sm sb) st = Abort Revert_abort u` by
        (irule ec_suffix_failure >> goal_assum (drule_at Any) >> simp[] >>
         qexistsl [`ip`,`op`,`res`,`po`] >> simp[]) >>
      pop_assum strip_assume_tac >>
      drule run_inst_seq_append >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  rename1 `vfmExecution$ecadd _ _ = SOME r` >>
  PairCases_on `r` >> simp[] >>
  `precompile_result (venom_call_request st 6w 0w wi 128w T).cr_target
      (venom_call_request st 6w 0w wi 128w T).cr_data =
    SOME (SOME (word_to_bytes (n2w r0:bytes32) T ++ word_to_bytes (n2w r1:bytes32) T))` by
    (asm_rewrite_tac[] >> irule ecadd_precompile_success >> simp[]) >>
  `?t. run_inst_seq (emitted_insts sm sb) st = OK t /\
       vv_post func cenv cx e es sf sb s es (Value (mk_ec_result (r0,r1)))
         (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t` by
    (irule ec_suffix_pointer_post >> simp[] >>
     goal_assum (drule_at (Pat `(_ : operand # compile_state) = _`)) >> simp[] >>
     qexists_tac `aid` >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  qpat_assum `run_inst_seq (emitted_insts sf sm) s = OK st`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem ecadd_pre_types[local]:
  expr_sim_pre cenv cx env (Builtin ann ECAdd args) es ==>
  ann = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?a b. args = [a;b] /\
    expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type b = ArrayT (BaseT (UintT 256)) (Fixed 2)
Proof
  simp[expr_sim_pre_def, well_typed_expr_def] >> strip_tac >>
  drule ecadd_types >> strip_tac >> gvs[MAP_EQ_CONS] >> metis_tac[]
QED

Theorem ecmul_pre_types[local]:
  expr_sim_pre cenv cx env (Builtin ann ECMul args) es ==>
  ann = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?a b. args = [a;b] /\
    expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type b = BaseT (UintT 256)
Proof
  simp[expr_sim_pre_def, well_typed_expr_def] >> strip_tac >>
  drule ecmul_types >> strip_tac >> gvs[MAP_EQ_CONS] >> metis_tac[]
QED

Theorem compile_ecmul_operands[local]:
  compile_expr cenv ty (Builtin ann ECMul [a;b]) sa = (vv,sb) ==>
  ?p scalar s1 sm res.
    lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
    lower_value compile_expr cenv (BaseT (UintT 256)) b s1 = (scalar,sm) /\
    compile_ecmul_point p scalar sm = (res,sb) /\
    vv = FST (as_ptr_val ann LocMemory (res,sb))
Proof
  `compile_expr cenv ty (Builtin ann ECMul [a;b]) sa =
    compile_builtin_dispatch cenv ann ty ECMul [a;b] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `a` >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def]) >>
  simp[] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  Cases_on `compile_ecmul_point p s'' st2` >> gvs[as_ptr_val_def]
QED

Theorem compile_ecadd_operands[local]:
  compile_expr cenv ty (Builtin ann ECAdd [a;b]) sa = (vv,sb) ==>
  ?p q s1 sm res.
    lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
    lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
    compile_ecadd_points p q sm = (res,sb) /\
    vv = FST (as_ptr_val ann LocMemory (res,sb))
Proof
  `compile_expr cenv ty (Builtin ann ECAdd [a;b]) sa =
    compile_builtin_dispatch cenv ann ty ECAdd [a;b] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `a` >> simp[names_builtin_def] >>
     Cases_on `b` >> simp[names_builtin_def]) >>
  simp[] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `as_ptr_val ann LocMemory (compile_ecadd_points p1 p2 st2a) = _` >>
  Cases_on `compile_ecadd_points p1 p2 st2a` >> gvs[as_ptr_val_def]
QED

Theorem ec_point_pointer_bound[local]:
  stmt_state_rel func cenv cx es s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo hi es v p s /\
  eval_operand p s = SOME w ==>
  w2n w + 64 < dimword (:256)
Proof
  simp[expr_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def,
       ec_point_footprint] >> strip_tac >> gvs[] >>
  irule (SRULE [wordsTheory.dimword_def] hash_live_footprint_bound) >>
  goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem ecmul_memory_semantics[local]:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  value_has_type (BaseTV (UintT 256)) scalar /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p s /\
  expr_val_rel cx (BaseT (UintT 256)) scalar q s ==>
  ?point sw.
    eval_operand p s = SOME point /\ eval_operand q s = SOME sw /\
    evaluate_ecmul [v;scalar] =
      (case vfmExecution$ecmul
        (w2n (mem_word_at (w2n point) s.vs_memory),
         w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n sw) of
         NONE => INR (RuntimeError "ECMul invalid point")
       | SOME r => INL (mk_ec_result r))
Proof
  strip_tac >> drule_all ec_point_memory_words >> strip_tac >>
  drule ec_uint256_encoding >> strip_tac >> gvs[] >>
  qpat_x_assum `expr_val_rel cx (BaseT (UintT 256)) _ _ _` mp_tac >>
  simp[expr_val_rel_def, evaluate_type_def, is_word_type_def] >>
  strip_tac >> gvs[] >>
  simp[evaluate_ecmul_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem ecadd_memory_semantics[local]:
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 p2 s ==>
  ?point point2.
    eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME point2 /\
    evaluate_ecadd [v1;v2] =
      (case vfmExecution$ecadd
        (w2n (mem_word_at (w2n point) s.vs_memory),
         w2n (mem_word_at (w2n point+32) s.vs_memory))
        (w2n (mem_word_at (w2n point2) s.vs_memory),
         w2n (mem_word_at (w2n point2+32) s.vs_memory)) of
         NONE => INR (RuntimeError "ECAdd invalid point")
       | SOME r => INL (mk_ec_result r))
Proof
  strip_tac >>
  qpat_assum `value_has_type _ v1` (mp_then Any mp_tac ec_point_memory_words) >>
  disch_then drule >> strip_tac >>
  qpat_assum `value_has_type _ v2` (mp_then Any mp_tac ec_point_memory_words) >>
  disch_then drule >> strip_tac >>
  qexistsl [`w`,`w'`] >>
  gvs[evaluate_ecadd_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem ecmul_point_frag[local]:
  compile_ecmul_point p scalar sf = (res,sb) /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  (!z. MEM (Var z) [p;scalar] ==> not_fresh_at sf z) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  value_has_type (BaseTV (UintT 256)) k /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p s /\
  expr_val_rel cx (BaseT (UintT 256)) k scalar s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  frag_exec ctx sf sb (\t. t = s)
    (\t. ?a. evaluate_ecmul [v;k] = INL a /\
      vv_post func cenv cx e es sf sb s es (Value a)
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t)
    (expr_exit (case evaluate_ecmul [v;k] of
       INL a => INL (Value a) | INR err => INR (Error err)))
Proof
  strip_tac >>
  drule_all ecmul_memory_semantics >> strip_tac >>
  `w2n point + 64 < dimword (:256)` by
    (irule ec_point_pointer_bound >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> qexists_tac `func` >> simp[]) >>
  drule_all ecmul_point_run >>
  drule ecmul_point_code_shape >> strip_tac >>
  Cases_on `vfmExecution$ecmul
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n sw)`
  >- (simp[] >> strip_tac >> irule frag_exec_run_inst_seq >>
      gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
      rpt strip_tac >> gvs[expr_exit_def]) >>
  rename1 `vfmExecution$ecmul _ _ = SOME pair` >>
  PairCases_on `pair` >> simp[] >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ecadd_points_frag[local]:
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  stmt_state_rel func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  (!z. MEM (Var z) [p1;p2] ==> not_fresh_at sf z) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 p2 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v1 p1 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v2 p2 s /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  frag_exec ctx sf sb (\t. t = s)
    (\t. ?a. evaluate_ecadd [v1;v2] = INL a /\
      vv_post func cenv cx e es sf sb s es (Value a)
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t)
    (expr_exit (case evaluate_ecadd [v1;v2] of
       INL a => INL (Value a) | INR err => INR (Error err)))
Proof
  strip_tac >>
  qpat_assum `value_has_type _ v1`
    (mp_then Any mp_tac ecadd_memory_semantics) >>
  disch_then (qspec_then `v2` mp_tac) >>
  disch_then (qspecl_then [`s`, `p2`, `p1`, `cx`] mp_tac) >>
  simp[] >> strip_tac >>
  `w2n point + 64 < dimword (:256)` by
    (irule ec_point_pointer_bound >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> qexists_tac `func` >> simp[]) >>
  `w2n point2 + 64 < dimword (:256)` by
    (irule ec_point_pointer_bound >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> qexists_tac `func` >> simp[]) >>
  drule_all ecadd_points_run >>
  drule ecadd_points_code_shape >> strip_tac >>
  Cases_on `vfmExecution$ecadd
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory))
    (w2n (mem_word_at (w2n point2) s.vs_memory),
     w2n (mem_word_at (w2n point2+32) s.vs_memory))`
  >- (simp[] >> strip_tac >> irule frag_exec_run_inst_seq >>
      gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
      rpt strip_tac >> gvs[expr_exit_def]) >>
  rename1 `vfmExecution$ecadd _ _ = SOME pair` >>
  PairCases_on `pair` >> simp[] >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ec_point_operands_then[local]:
  expr_sim ctx func cenv cx ty1 a es /\
  expr_sim ctx func cenv cx ty2 b es1 /\
  lower_value compile_expr cenv ty1 a sa = (p,s1) /\
  lower_value compile_expr cenv ty2 b s1 = (q,sm) /\
  (do r <- eval_expr cx a; read_result cx r od) es = (r1,es1) /\
  (do r <- eval_expr cx b; read_result cx r od) es1 = (r2,es2) /\
  expr_res_ok r1 /\ expr_res_ok r2 /\
  fn_has_code sa s1 func /\ fn_has_code s1 sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv s1 /\
  cs_extends sa s1 /\ cs_extends s1 sm /\ cs_extends sm sb /\
  expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  (!z. p = Var z ==> not_fresh_at s1 z) /\ (!l. p <> Label l) /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\ s1.cs_next_id <= sm.cs_next_id /\
  (!r. expr_exit r1 r ==> R r) /\
  (!v r. r1 = INL v /\ expr_exit r2 r ==> R r) /\
  (!v1 v2 t u. r1 = INL v1 /\ r2 = INL v2 /\
    expr_post func cenv cx a es sa s1 s0 es1 v1 p t /\
    expr_post func cenv cx b es1 s1 sm t es2 v2 q u /\
    expr_val_rel cx (expr_type a) v1 p u /\
    expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u ==>
    frag_exec ctx sm sb (\s. s = u) Q R) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s) Q R
Proof
  strip_tac >>
  `frag_exec ctx sa s1 (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
     (\t. ?v1. r1 = INL v1 /\ expr_post func cenv cx a es sa s1 s0 es1 v1 p t) R` by
    (irule frag_exec_pre_exit >>
     qexistsl_tac [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`, `expr_exit r1`] >>
     simp[] >> irule exprSimWordArgsTheory.expr_sim_apply >> simp[] >> metis_tac[]) >>
  dxrule frag_exec_then >> disch_then irule >>
  conj_tac >-
   (gen_tac >> simp[] >> strip_tac >>
    `stmt_state_rel func cenv cx es1 t` by gvs[expr_post_def] >>
    `frag_exec ctx s1 sm (\s. s = t)
       (\u. ?v2. r2 = INL v2 /\ expr_post func cenv cx b es1 s1 sm t es2 v2 q u) R` by
      (irule frag_exec_pre_exit >>
       qexistsl_tac [`\s. s = t /\ stmt_state_rel func cenv cx es1 s`, `expr_exit r2`] >>
       simp[] >> irule exprSimWordArgsTheory.expr_sim_apply >> simp[] >> metis_tac[]) >>
    dxrule frag_exec_then >> disch_then irule >> simp[] >>
    gen_tac >> simp[] >> strip_tac >>
    `?w. eval_operand p t = SOME w /\ eval_operand p t' = SOME w` by
      (metis_tac[expr_post_operand_word]) >>
    `!w. eval_operand p t = SOME w ==> eval_operand p t' = SOME w` by
      metis_tac[optionTheory.SOME_11] >>
    `expr_val_rel cx (expr_type a) v1 p t' /\
     expr_val_at cenv cx (expr_type a) sa sm es2 v1 p t'` by
      (metis_tac[ec_point_operand_kept]) >>
    first_x_assum irule >> qexists_tac `t` >> gvs[]) >>
  metis_tac[cs_extends_trans]
QED

Theorem ec_two_args_source[local]:
  bt <> Len /\ builtin_args_length_ok bt 2 /\
  eval_expr cx (Builtin ann bt [a;b]) es = (res,es') /\
  (do r <- eval_expr cx a; read_result cx r od) es = (r1,es1) /\
  (do r <- eval_expr cx b; read_result cx r od) es1 = (r2,es2) ==>
  (!ex. r1 = INR ex ==> res = INR ex) /\
  (!v ex. r1 = INL v /\ r2 = INR ex ==> res = INR ex) /\
  (!v1 v2. r1 = INL v1 /\ r2 = INL v2 ==>
    es' = es2 /\ res =
      (case exprSimWordArgs$builtin_result cx es2.accounts ann bt
              [expr_type a;expr_type b] [v1;v2] of
         INL v => INL (Value v) | INR ex => INR ex))
Proof
  strip_tac >>
  `?rr. (do r <- eval_expr cx (Builtin ann bt [a;b]);
      read_result cx r od) es = (rr,es') /\
      res = (case rr of INL v => INL (Value v) | INR ex => INR ex)` by
    (Cases_on `res`
     >- (drule eval_expr_builtin_value >> strip_tac >>
         qexists_tac `INL v` >>
         gvs[vyperStateTheory.bind_def, vyperStateTheory.read_result_def,
             vyperStateTheory.return_def]) >>
     qexists_tac `INR y` >> simp[vyperStateTheory.bind_def]) >>
  `builtin_args_length_ok bt (LENGTH [a;b])` by simp[] >>
  drule_all exprSimWordArgsTheory.eval_expr_builtin_cases >> strip_tac >>
  drule exprSimWordArgsTheory.eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  drule exprSimWordArgsTheory.eval_exprs_cons_cases >> strip_tac >>
  gvs[exprSimWordArgsTheory.eval_exprs_nil]
QED

Theorem ec_binary_call_then[local]:
  expr_sim_below cenv (list_size expr_size [a;b]) /\
  expr_sim_pre cenv cx env (Builtin ann bt [a;b]) es /\
  bt <> Len /\ builtin_args_length_ok bt 2 /\
  expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
  lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
  cs_extends sm sb /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  eval_expr cx (Builtin ann bt [a;b]) es = (res,es') /\
  (!es1 es2 v1 v2 t u.
    (do r <- eval_expr cx a; read_result cx r od) es = (INL v1,es1) /\
    (do r <- eval_expr cx b; read_result cx r od) es1 = (INL v2,es2) /\
    expr_post func cenv cx a es sa s1 s0 es1 v1 p t /\
    expr_post func cenv cx b es1 s1 sm t es2 v2 q u /\
    expr_val_rel cx (expr_type a) v1 p u /\
    expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u /\
    expr_result_typed env a (Value v1) /\ expr_result_typed env b (Value v2) /\
    stmt_state_rel func cenv cx es2 u /\ local_ptrs_reserved cenv sm /\
    fn_has_code sm sb func /\
    (!z. MEM (Var z) [p;q] ==> not_fresh_at sm z) ==>
    frag_exec ctx sm sb (\s. s = u)
      (\s. ?v. exprSimWordArgs$builtin_result cx es2.accounts ann bt
                  [expr_type a;expr_type b] [v1;v2] = INL v /\
        vv_post func cenv cx (Builtin ann bt [a;b]) es2 sm sb u es2 (Value v) vv s)
      (expr_exit (case exprSimWordArgs$builtin_result cx es2.accounts ann bt
                        [expr_type a;expr_type b] [v1;v2] of
        INL v => INL (Value v) | INR ex => INR ex))) ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel func cenv cx es s)
    (\s. ?v. res = INL v /\
      vv_post func cenv cx (Builtin ann bt [a;b]) es sa sb s0 es' v vv s)
    (expr_exit res)
Proof
  strip_tac >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
  `expr_sim_pre cenv cx env a es` by
    (`expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
     drule expr_sim_pre_builtin_arg >>
     disch_then (qspecl_then [`a`, `es`] mp_tac) >> simp[]) >>
  `expr_ok cenv a /\ expr_ok cenv b` by
    (conj_tac >> irule expr_sim_below_mem >>
     qexists_tac `[a;b]` >> simp[]) >>
  Cases_on `(do r <- eval_expr cx a; read_result cx r od) es` >>
  rename1 `(do r <- eval_expr cx a; read_result cx r od) es = (r1,es1)` >>
  `expr_sim_inv cenv cx env es1 /\ expr_res_ok r1` by
    metis_tac[expr_sim_pre_eval, expr_sim_pre_res_ok] >>
  `expr_sim_pre cenv cx env b es1` by
    (qpat_assum `expr_sim_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any mp_tac expr_sim_pre_builtin_arg) >>
     disch_then (qspecl_then [`b`, `es1`] mp_tac) >> simp[]) >>
  Cases_on `(do r <- eval_expr cx b; read_result cx r od) es1` >>
  rename1 `(do r <- eval_expr cx b; read_result cx r od) es1 = (r2,es2)` >>
  `expr_res_ok r2` by metis_tac[expr_sim_pre_res_ok] >>
  qpat_assum `lower_value _ _ _ a _ = _`
    (mp_then Any mp_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >> strip_tac >>
  qpat_assum `lower_value _ _ _ b _ = _`
    (mp_then Any mp_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >> strip_tac >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!z. p = Var z ==> not_fresh_at s1 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s1 sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all ec_two_args_source >> strip_tac >>
  `expr_sim ctx func cenv cx (expr_type a) a es /\
   expr_sim ctx func cenv cx (expr_type b) b es1` by
    metis_tac[expr_ok_def, expr_sim_ok_def] >>
  `safe_operand s1 p` by metis_tac[ec_point_lower_value_safe_operand] >>
  `!l. p <> Label l` by gvs[safe_operand_def] >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    metis_tac[exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom] >>
  irule ec_point_operands_then >> simp[] >>
  qexistsl_tac [`a`, `b`, `es1`, `es2`, `p`, `q`, `r1`, `r2`,
                `s1`, `sm`, `expr_type a`, `expr_type b`] >> simp[] >>
  rpt conj_tac
  >- (once_rewrite_tac[GSYM (Q.ISPEC `Value` expr_exit_success_map)] >>
      Cases_on `r1` >> gvs[expr_exit_def])
  >- (once_rewrite_tac[GSYM (Q.ISPEC `Value` expr_exit_success_map)] >>
      Cases_on `r2` >> gvs[expr_exit_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `expr_result_typed env a (Value v1) /\ expr_result_typed env b (Value v2)` by
    metis_tac[expr_sim_pre_eval] >>
  `stmt_state_rel func cenv cx es2 u` by gvs[expr_post_def] >>
  `!z. MEM (Var z) [p;q] ==> not_fresh_at sm z` by
    (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var,
                         freshWritesTheory.not_fresh_at_mono]) >>
  gvs[] >>
  qpat_x_assum `!t u. _ ==> frag_exec _ _ _ _ _ _` drule_all >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    metis_tac[exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom] >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by metis_tac[] >>
  `wb_frame cenv es sa s0 u` by
    (drule_all exprSimWordArgsTheory.expr_post_frame >> strip_tac >>
     qpat_assum `expr_post _ _ _ a _ _ _ _ _ _ _ _`
       (mp_then Any strip_assume_tac exprSimWordArgsTheory.expr_post_frame) >>
     irule exprSimWordArgsTheory.wb_frame_trans >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`es1`, `s1`, `t`] >> simp[]) >>
  gvs[] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >> rpt strip_tac >> gvs[] >>
  irule exprSimCalldataSliceTheory.vv_post_prefix_frame >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_ecmul_call_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann ECMul args)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_ok_def] >> rpt strip_tac >>
  drule ecmul_pre_types >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  drule compile_ecmul_operands >> strip_tac >>
  `cs_extends sm sb` by
    (drule ecmul_point_code_shape >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  irule ec_binary_call_then >>
  simp[builtin_args_length_ok_def] >>
  qexists_tac `env` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
   value_has_type (BaseTV (UintT 256)) v2` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def, evaluate_type_def] >>
  `expr_val_rel cx (BaseT (UintT 256)) v2 scalar u` by gvs[expr_post_def] >>
  `frag_exec ctx sm sb (\s. s = u)
     (\s. ?v. evaluate_ecmul [v1;v2] = INL v /\
       vv_post func cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b])
         es2 sm sb u es2 (Value v)
         (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res',sb))) s)
     (expr_exit (case evaluate_ecmul [v1;v2] of
        INL v => INL (Value v) | INR err => INR (Error err)))` by
    (irule (SRULE []
       (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b]`]
          (SPEC_ALL ecmul_point_frag))) >> simp[vyperASTTheory.expr_type_def] >>
     conj_tac >- metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
     qexistsl_tac [`sa`, `p`, `scalar`] >> simp[] >> metis_tac[]) >>
  gvs[exprSimWordArgsTheory.builtin_result_def, evaluate_builtin_def] >>
  Cases_on `evaluate_ecmul [v1;v2]` >> gvs[]
QED

Theorem ec_expr_val_at_start_mono[local]:
  sa.cs_next_id <= s1.cs_next_id /\
  expr_val_at cenv cx ty s1 sm es v p s ==>
  expr_val_at cenv cx ty sa sm es v p s
Proof
  simp[expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem compile_ecadd_call_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann ECAdd args)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_ok_def] >> rpt strip_tac >>
  drule ecadd_pre_types >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  drule compile_ecadd_operands >> strip_tac >>
  `cs_extends sm sb` by
    (drule ecadd_points_code_shape >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  gvs[] >>
  irule ec_binary_call_then >> simp[builtin_args_length_ok_def] >>
  qexists_tac `env` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
   value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2` by
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeExprSoundnessTheory.value_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def, evaluate_type_def] >>
  `expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 q u /\
   expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) s1 sm es2 v2 q u` by
    gvs[expr_post_def] >>
  qpat_assum `lower_value _ _ _ a _ = _`
    (mp_then Any mp_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >> strip_tac >>
  `expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa sm es2 v2 q u` by
    (irule ec_expr_val_at_start_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `frag_exec ctx sm sb (\s. s = u)
     (\s. ?v. evaluate_ecadd [v1;v2] = INL v /\
       vv_post func cenv cx (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b])
         es2 sm sb u es2 (Value v)
         (FST (as_ptr_val (ArrayT (BaseT (UintT 256)) (Fixed 2)) LocMemory (res',sb))) s)
     (expr_exit (case evaluate_ecadd [v1;v2] of
        INL v => INL (Value v) | INR err => INR (Error err)))` by
    (irule (SRULE []
       (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b]`]
          (SPEC_ALL ecadd_points_frag))) >> simp[vyperASTTheory.expr_type_def] >>
     conj_tac >- metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
     qexistsl_tac [`sa`, `p`, `q`] >> simp[] >> metis_tac[]) >>
  gvs[exprSimWordArgsTheory.builtin_result_def, evaluate_builtin_def] >>
  Cases_on `evaluate_ecadd [v1;v2]` >> gvs[]
QED
