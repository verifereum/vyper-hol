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
 *   compile_ecadd_call_case, compile_ecmul_call_case — shared case judgments
 *   for ECAdd and ECMul, including operands with internal calls.
 *
 * Helpers: lower_value_name_safe_operand and generic no-Label support in
 *   exprSafeOperand; ec_point_memory_words, ec_point_operand_kept;
 *   ec_point_word_transfer_run, ec_point_pair_transfer_run,
 *   ec_point_prefix_then_run share point-word movement;
 *   ec_scratch_stores_memory, ec_scratch_stores_capacity and
 *   ec_scratch_stores_frame preserve disjoint regions and immutable bytes;
 *   ec_points_run,
 *   ec_outcome_then composes a value step with a counted continuation;
 *   ec_binary_call_gas composes exprs_case operands under expr_body_pre as
 *   counted gas outcomes;
 *   ec_points_path and compile_ec_call_case share the EC pipeline atop
 *   exprSimPrecompiles' allocated_payload_run and computed-call suffix.
 *)
Theory exprSimECArith
Ancestors
  exprSimSource
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  exprOperandVar exprSafeOperand exprSafeOperandBuiltins
  fragExec exprSimHash exprSimWordBuiltins
  exprLowering exprSimHyps exprSimPrecompiles exprSimOperands
  exprSimAttributeFields
  exprSimLiteralBuffer
  exprSimCalldataSlice entryDecodeStaticProps
  builtinMisc venomInst exprLoweringProps venomExecSemantics
  venomState vyperTypeSystem vyperContext valueEncoding
  vyperTyping valueEncodingProofs vyperTypeBuiltins vyperValueOperation
  vyperValue vyperAssignPreservesType compileEnv extCallOracle byte
  vfmBuffer venomMemDefs vfmTypes vfmExecution bn254 list rich_list
  numposrep gasOutcome gasSummary gasSummaryCompose gasExemptCert
  fragGasPath fragGasMode cv_std[ignore_grammar]

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

Theorem ec_point_lower_value_safe_operand[local]:
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
  post_value_type cenv e1 = expr_type e1 /\
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y u /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_sim_inv cenv cx env es /\
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
  simp[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  strip_tac
  >- (`expr_val_in_alloca cenv cx (expr_type e1) sa s1 es1 v1 x t` by
        (simp[expr_val_in_alloca_def, evaluate_type_def, is_word_type_def,
              type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
         qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
      drule_all expr_post_operand_kept_stable >> strip_tac >>
      drule expr_val_in_alloca_at >> strip_tac >>
      gvs[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
          type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
      metis_tac[]) >>
  conj_tac
  >- (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    expr_post_operand_local_kept >>
  simp[is_word_type_def, evaluate_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  disch_then irule >>
  simp[is_word_type_def, evaluate_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  conj_tac >- gvs[expr_post_def] >>
  qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
  rpt strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `es`, `n`, `w2n w - b`,
               `ArrayTV (BaseTV (UintT 256)) (Fixed 2)`, `k`] mp_tac
    local_path_at_dynarray_apart >>
  simp[dynarray_free_fixed, dynarray_free_base, type_memory_size_def]) >>
  `local_region cenv es'.scopes u n b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`t`, `s1`, `es1.scopes`] >> simp[] >>
     gvs[expr_post_def]) >>
  simp[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  disj2_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem ec_precompile_words[local]:
  (!x1 y1 x2 y2.
  precompile_result 6w
    (word_to_bytes (x1:bytes32) T ++ word_to_bytes (y1:bytes32) T ++
     word_to_bytes (x2:bytes32) T ++ word_to_bytes (y2:bytes32) T) =
  SOME (OPTION_MAP (\(x,y).
    PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
    (vfmExecution$ecadd (w2n x1,w2n y1) (w2n x2,w2n y2)))) /\
  (!x y n.
  precompile_result 7w
    (word_to_bytes (x:bytes32) T ++ word_to_bytes (y:bytes32) T ++
     word_to_bytes (n:bytes32) T) =
  SOME (OPTION_MAP (\(x,y).
    PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
    (vfmExecution$ecmul (w2n x,w2n y) (w2n n))))
Proof
  conj_tac >> rpt gen_tac >>
  rewrite_tac[precompile_result_ecadd, precompile_result_ecmul,
              SRULE [] (Q.INST [`n` |-> `0`] drop_word_prefix),
              SRULE [] (Q.INST [`n` |-> `32`] drop_word_prefix),
              SRULE [] (Q.INST [`n` |-> `64`] drop_word_prefix),
              take_pad_word_prefix] >>
  simp[take_pad_0_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, listTheory.TAKE_APPEND1,
       listTheory.DROP_APPEND, listTheory.TAKE_LENGTH_TOO_LONG,
       listTheory.DROP_LENGTH_TOO_LONG, PAD_RIGHT,
       num_of_be_bytes_word32, word_to_bytes_word_of_bytes_32,
       word_of_bytes_be_def]
QED

(* These bounds adapters use distinct affine results: addAffine_bounded
   directly, versus mulAffine_bounded with the valid input point unpacked. *)
Theorem ecadd_success_bounds:
  vfmExecution$ecadd a b = SOME (x,y) ==>
  x < 2 ** 256 /\ y < 2 ** 256
Proof
  simp[vfmExecutionTheory.ecadd_def, AllCaseEqs()] >> strip_tac >>
  mp_tac (Q.SPECL [`a`, `b`] addAffine_bounded) >> gvs[]
QED

Theorem ecmul_success_bounds:
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

Theorem ec_precompile_success[local]:
  (!x1 y1 x2 y2 x y.
  vfmExecution$ecadd (w2n x1,w2n y1) (w2n x2,w2n y2) = SOME (x,y) ==>
  precompile_result 6w
    (word_to_bytes (x1:bytes32) T ++ word_to_bytes (y1:bytes32) T ++
     word_to_bytes (x2:bytes32) T ++ word_to_bytes (y2:bytes32) T) =
  SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T))) /\
  (!px py scalar x y.
  vfmExecution$ecmul (w2n px,w2n py) (w2n scalar) = SOME (x,y) ==>
  precompile_result 7w
    (word_to_bytes (px:bytes32) T ++ word_to_bytes (py:bytes32) T ++
     word_to_bytes (scalar:bytes32) T) =
  SOME (SOME (word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T)))
Proof
  conj_tac >> rpt gen_tac >> strip_tac >>
  `x < 2 ** 256 /\ y < 2 ** 256` by
    metis_tac[ecadd_success_bounds, ecmul_success_bounds] >>
  simp[ec_precompile_words, padded_num_to_be_bytes_word32]
QED

Theorem ec_points_code_shape[local]:
  (!p1 p2 sa op sb.
  compile_ecadd_points p1 p2 sa = (op,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)) /\
  (!p scalar sa op sb.
  compile_ecmul_point p scalar sa = (op,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb))
Proof
  conj_tac >> rpt gen_tac >>
  simp[compile_ecadd_points_def, compile_ecmul_point_def,
       contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       same_blocks_def, mk_inst_def, is_terminator_def]
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
  simp[Once run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
       bind_outputs_def, eval_operand_def,
       emitHelperPropsTheory.lookup_var_update_var,
       valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  simp[Once run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
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
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  stmt_state_rel ctx func cenv cx es' t /\ wb_frame cenv es sa s0 t /\
  eval_operand pop t = SOME w /\
  mem_bytes_at (w2n w) 64 t.vs_memory =
    word_to_bytes (n2w x:bytes32) T ++ word_to_bytes (n2w y:bytes32) T /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,64) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b sz. local_region cenv es'.scopes t name b sz ==>
     regions_disjoint (w2n w) 64 b sz) ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value (mk_ec_result (x,y)))
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
  gvs[loweringPostsTheory.wb_frame_def] >> metis_tac[]
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
      irule exprSimPropsTheory.local_region_frame_fwd >>
      qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]) >>
  metis_tac[]
QED

Theorem ec_input_stores_shape[local]:
  (!p1 p2 ib sa sb. (do xp <- emit_op ADD [p1; Lit 0w];
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
  sb.cs_next_id = sa.cs_next_id + 16) /\
  (!p ib scalar sa sb. (do xp <- emit_op ADD [p; Lit 0w];
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
  sb.cs_next_id = sa.cs_next_id + 10)
Proof
  conj_tac >> rpt gen_tac >>
  simp[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

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

(* First-point prefix shared by both payloads.  The tail's operands are
   preserved even when they are labels, since the prefix preserves labels. *)
Theorem ec_point_prefix_then_run[local]:
  (do xp <- emit_op ADD [p; Lit 0w];
      x <- emit_op MLOAD [xp];
      dst0 <- emit_op ADD [ib; Lit 0w];
      emit_void MSTORE [dst0; x];
      yp <- emit_op ADD [p; Lit 32w];
      y <- emit_op MLOAD [yp];
      dst1 <- emit_op ADD [ib; Lit 32w];
      emit_void MSTORE [dst1; y]; tail od) sa = ((),sb) /\
  eval_operand p s = SOME point /\ eval_operand ib s = SOME bw /\
  (!x. MEM (Var x) (p::ib::ops) ==> not_fresh_at sa x) /\
  w2n point + 64 < dimword (:256) /\
  w2n bw + len < dimword (:256) /\ 64 <= len /\
  regions_disjoint (w2n bw) len (w2n point) 64 ==>
  ?sc t.
    (do xp <- emit_op ADD [p; Lit 0w];
        x <- emit_op MLOAD [xp];
        dst0 <- emit_op ADD [ib; Lit 0w];
        emit_void MSTORE [dst0; x];
        yp <- emit_op ADD [p; Lit 32w];
        y <- emit_op MLOAD [yp];
        dst1 <- emit_op ADD [ib; Lit 32w];
        emit_void MSTORE [dst1; y] od) sa = ((),sc) /\
    tail sc = ((),sb) /\
    run_inst_seq (emitted_insts sa sc) s = OK t /\
    t.vs_memory =
      (mstore (w2n bw+32) (mem_word_at (w2n point+32) s.vs_memory)
        (mstore (w2n bw) (mem_word_at (w2n point) s.vs_memory) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    sc.cs_next_var = sa.cs_next_var + 6 /\
    sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
    (!op. MEM op (ib::ops) ==> eval_operand op t = eval_operand op s) /\
    (!x. MEM (Var x) (ib::ops) ==> not_fresh_at sc x)
Proof
  rpt strip_tac >>
  `(do (do xp <- emit_op ADD [p; Lit 0w];
           x <- emit_op MLOAD [xp];
           dst0 <- emit_op ADD [ib; Lit 0w];
           emit_void MSTORE [dst0; x];
           yp <- emit_op ADD [p; Lit 32w];
           y <- emit_op MLOAD [yp];
           dst1 <- emit_op ADD [ib; Lit 32w];
           emit_void MSTORE [dst1; y] od); tail od) sa = ((),sb)` by
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
  `sc.cs_next_var = sa.cs_next_var + 6 /\
   sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    (qpat_assum `_ sa = ((),sc)` mp_tac >>
     simp[NoAsms, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `_ with <|vs_memory := _; vs_vars := _|> = _`
      (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_x_assum irule >> simp[] >> decide_tac
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
  drule (Q.INST [`ops` |-> `[scalar]`, `len` |-> `96`]
    (SPEC_ALL ec_point_prefix_then_run)) >>
  disch_then (qspecl_then [`scalar`, `s`, `point`, `bw`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK s1` >>
  `eval_operand ib s1 = SOME bw /\ eval_operand scalar s1 = SOME wscalar` by
    (gvs[] >> metis_tac[]) >>
  `!x. MEM (Var x) [ib;scalar] ==> not_fresh_at sc x` by
    (gvs[] >> metis_tac[]) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
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
  simp[Once run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, bind_outputs_def, eval_operand_def] >>
  simp[Once run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
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
  drule (Q.INST [`ops` |-> `[q]`, `len` |-> `128`]
    (SPEC_ALL ec_point_prefix_then_run)) >>
  disch_then (qspecl_then [`s`, `q`, `point`, `bw`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK s1` >>
  qpat_x_assum `_ sa = ((),sb)` kall_tac >>
  `eval_operand q s1 = SOME point2 /\ eval_operand ib s1 = SOME bw` by
    (gvs[] >> metis_tac[]) >>
  `!x. MEM (Var x) [q;ib] ==> not_fresh_at sc x` by
    (gvs[] >> metis_tac[]) >>
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
  drule_all run_inst_seq_chain >> strip_tac >>
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
  >- simp[] >>
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
    (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[]
QED

(* Any finite collection of word stores confined to scratch preserves all
   disjoint observations.  Payload clients only supply offsets and words. *)
Theorem ec_scratch_stores_memory[local]:
  !stores s.
  (!off w. MEM (off,w) stores ==> off + 32 <= len) /\
  regions_disjoint a len b sz ==>
  mem_bytes_at b sz
    (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory =
  mem_bytes_at b sz s.vs_memory
Proof
  Induct_on `stores` >> simp[] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt strip_tac >>
  `mem_bytes_at b sz
     (FOLDL (\u (off,w). mstore (a+off) w u)
       (mstore (a+h0) h1 s) stores).vs_memory =
   mem_bytes_at b sz (mstore (a+h0) h1 s).vs_memory` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[] >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
  gvs[compileEnvTheory.regions_disjoint_def] >>
  qpat_x_assum `!off w. _` (qspecl_then [`h0`, `h1`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem ec_scratch_stores_capacity[local]:
  !stores s. LENGTH s.vs_memory <=
    LENGTH (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory
Proof
  Induct_on `stores` >> simp[] >>
  qx_gen_tac `h` >> PairCases_on `h` >> gen_tac >>
  first_x_assum (qspec_then `mstore (a+h0) h1 s` mp_tac) >>
  simp[immutableMemoryFrameTheory.immutable_mstore_capacity] >> decide_tac
QED

Theorem ec_scratch_stores_frame[local]:
  t.vs_memory =
    (FOLDL (\u (off,w). mstore (a+off) w u) s stores).vs_memory /\
  (!off w. MEM (off,w) stores ==> off + 32 <= len) /\
  stmt_state_rel ctx func cenv cx es s /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint a len b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint a len b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint a len off (type_memory_size tv)) ==>
  stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t
Proof
  strip_tac >>
  `!b sz. regions_disjoint a len b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule ec_scratch_stores_memory >>
     qexists_tac `len` >> metis_tac[]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (simp[] >> irule ec_scratch_stores_capacity) >>
  drule_all scratch_memory_frame >> simp[]
QED

Theorem ec_input_stores_sim[local]:
  (!p ib scalar sa sb s point bw wscalar func cenv cx es sc.
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
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 96 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n bw) 96 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n bw) 96 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes wscalar T) /\
  (!p q ib sa sb s point point2 bw func cenv cx es sc.
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
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sc.cs_next_var <= sa.cs_next_var /\ sc.cs_next_id <= sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (!aid b sz. aid < sc.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n bw) 128 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n bw) 128 off (type_memory_size tv)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sc s t /\
    mem_bytes_at (w2n bw) 128 t.vs_memory =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point2+32) s.vs_memory) T)
Proof
  conj_tac >> rpt gen_tac >> strip_tac
  >- (
    drule_all ecmul_input_stores_run >> strip_tac >>
    `?stores. t.vs_memory =
       (FOLDL (\u (off,w). mstore (w2n bw+off) w u) s stores).vs_memory /\
       (!off w. MEM (off,w) stores ==> off+32 <= 96)` by
      (qexists_tac `[(0,mem_word_at (w2n point) s.vs_memory);
                    (32,mem_word_at (w2n point+32) s.vs_memory);
                    (64,wscalar)]` >>
       simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
    qexists_tac `t` >>
    simp[IgnAsm `t.vs_memory = (FOLDL _ _ _).vs_memory`,
         scratch_three_word_stores] >> suspend "frame") >>
    drule_all ecadd_input_stores_run >> strip_tac >>
    `?stores. t.vs_memory =
       (FOLDL (\u (off,w). mstore (w2n bw+off) w u) s stores).vs_memory /\
       (!off w. MEM (off,w) stores ==> off+32 <= 128)` by
      (qexists_tac `[(0,mem_word_at (w2n point) s.vs_memory);
                    (32,mem_word_at (w2n point+32) s.vs_memory);
                    (64,mem_word_at (w2n point2) s.vs_memory);
                    (96,mem_word_at (w2n point2+32) s.vs_memory)]` >>
       simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
    qexists_tac `t` >>
    simp[IgnAsm `t.vs_memory = (FOLDL _ _ _).vs_memory`,
         scratch_four_word_stores] >> suspend "frame"
QED

Resume ec_input_stores_sim[frame]:
  markerLib.RESUME_TAC >> drule_all ec_scratch_stores_frame >> simp[]
QED

Finalise ec_input_stores_sim

Theorem comp_return_bind[local]:
  !x f. comp_bind (comp_return x) f = f x
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

(* Direct compiler boundary. The legacy buffer-prefix interface below is
   retained only until the allocation-runtime consumers are migrated. *)
Theorem ec_points_prefix[local]:
  (!p scalar sf res sb cenv func.
  compile_ecmul_point p scalar sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sp sm.
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
        emit_void MSTORE [dst2; scalar] od) sa = ((),sp) /\
    context$compile_alloc_buffer 64 sp = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 7w; ib.buf_operand; Lit 96w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sp ++
      emitted_insts sp sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 96w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sp.cs_next_var /\
    sp.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id <= sp.cs_next_id /\
    sp.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sa x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x)) /\
  (!p1 p2 sf res sb cenv func.
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) ==>
  ?ib ob sa sp sm.
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
        emit_void MSTORE [dst3; y2] od) sa = ((),sp) /\
    context$compile_alloc_buffer 64 sp = (ob,sm) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit 6w; ib.buf_operand; Lit 128w; ob.buf_operand; Lit 64w];
        emit_void ASSERT [success]; return ob.buf_operand od) sm = (res,sb) /\
    emitted_insts sf sm = emitted_insts sf sa ++ emitted_insts sa sp ++
      emitted_insts sp sm /\
    emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb /\
    MEM (mk_inst sf.cs_next_id ALLOCA [Lit 128w]
      [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
    MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sp /\
    local_ptrs_reserved cenv sm /\
    sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sp.cs_next_var /\
    sp.cs_next_var <= sm.cs_next_var /\
    sf.cs_next_id < sa.cs_next_id /\ sa.cs_next_id <= sp.cs_next_id /\
    sp.cs_next_id < sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sa x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x))
Proof
  conj_tac >> (rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ sf = (res,sb)` mp_tac >>
  simp[compile_ecmul_point_def, compile_ecadd_points_def, comp_return_bind] >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `context$compile_alloc_buffer _ sf = (ib,sa)` >>
  qpat_abbrev_tac `payload = comp_bind (emit_op ADD _) _` >>
  qmatch_asmsub_abbrev_tac `comp_bind (context$compile_alloc_buffer 64) suffix` >>
  qabbrev_tac `tail = comp_bind (context$compile_alloc_buffer 64) suffix` >>
  `comp_ignore_bind payload tail sa = (res,sb)` by
    (fs[Abbr `payload`, Abbr `tail`, comp_ignore_bind_def, comp_bind_assoc]) >>
  qpat_x_assum `comp_ignore_bind payload tail sa = _` mp_tac >>
  simp[comp_ignore_bind_def, Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `payload sa = (u,sp)` >> Cases_on `u` >>
  qpat_x_assum `tail sp = _` mp_tac >>
  simp[Abbr `tail`, Once comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rename1 `context$compile_alloc_buffer 64 sp = (ob,sm)` >>
  qpat_x_assum `_ sa = (res,sb)` kall_tac >>
  qunabbrev_tac `payload` >> imp_res_tac ec_input_stores_shape >>
  qunabbrev_tac `suffix` >> fs[] >> drule computed_suffix_shape >> strip_tac >>
  qpat_assum `context$compile_alloc_buffer _ sf = _`
    (strip_assume_tac o MATCH_MP loweringHaltTheory.compile_alloc_buffer_insts) >>
  qpat_assum `context$compile_alloc_buffer 64 sp = _`
    (strip_assume_tac o MATCH_MP loweringHaltTheory.compile_alloc_buffer_insts) >>
  `emitted_insts sf sm = emitted_insts sf sa ++
     emitted_insts sa sp ++ emitted_insts sp sm` by
    (CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     simp[rich_listTheory.DROP_APPEND1] >>
     simp[emitted_insts_def, NoAsms] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  qpat_x_assum `emitted_insts sm sb = _` kall_tac >>
  `sm.cs_current_insts = sf.cs_current_insts ++ emitted_insts sf sm` by
    (CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV emitted_insts_def))) >>
     simp[rich_listTheory.DROP_APPEND1, listTheory.APPEND_ASSOC]) >>
  `emitted_insts sf sb = emitted_insts sf sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  qpat_x_assum `sm.cs_current_insts = sf.cs_current_insts ++ _` kall_tac >>
  qpat_assum `context$compile_alloc_buffer _ sf = _`
    (strip_assume_tac o MATCH_MP loweringHaltTheory.compile_alloc_buffer_parts) >>
  qpat_assum `context$compile_alloc_buffer 64 sp = _`
    (strip_assume_tac o MATCH_MP loweringHaltTheory.compile_alloc_buffer_parts) >>
  simp[] >>
  conj_tac
  >- (qpat_x_assum `!i. MEM i (emitted_insts sf sb) ==> _` irule >>
      simp[] >> disj1_tac >> disj1_tac >>
      once_rewrite_tac[emitted_insts_def] >> simp[rich_listTheory.DROP_APPEND1]) >>
  conj_tac
  >- (qpat_x_assum `!i. MEM i (emitted_insts sf sb) ==> _` irule >>
      simp[] >> disj1_tac >> disj2_tac >>
      once_rewrite_tac[emitted_insts_def] >> simp[rich_listTheory.DROP_APPEND1]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sf` >> simp[]) >>
  simp[not_fresh_at_def])
QED

Definition ec_source_tail_def:
  ec_source_tail cx ann bt tys vs es =
    case exprSimWordArgs$builtin_result cx es.accounts ann bt tys vs of
      INR ex => (INR ex,es)
    | INL v => (do precompile_call_success bt;
                   vyperState$return (Value v) od) es
End

Theorem ec_source_outcome_step[local]:
  (bt = ECAdd \/ bt = ECMul) ==>
  precompile_call_success bt es =
    case es.outcomes of
      NONE => (INL (),es)
    | SOME [] => (INR (Error (RuntimeError "precompile failed")),es)
    | SOME (outcome::rest) =>
        (if call_outcome_success outcome then INL ()
         else INR (Error (RuntimeError "precompile failed")),
         es with outcomes := SOME rest)
Proof
  strip_tac >> gvs[] >>
  Cases_on `es.outcomes` >>
  simp[vyperInterpreterTheory.precompile_call_success_def, vyperStateTheory.return_def] >>
  rename1 `SOME os` >> Cases_on `os` >>
  simp[vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  Cases_on `call_outcome_success h` >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem eval_expr_ec_cases[local]:
  (bt = ECAdd \/ bt = ECMul) /\ LENGTH args = 2 /\
  eval_expr cx (Builtin ann bt args) es = (res,es') ==>
  (?exc. eval_exprs cx args es = (INR exc,es') /\ res = INR exc) \/
  ?vs es1. eval_exprs cx args es = (INL vs,es1) /\
    ec_source_tail cx ann bt (MAP expr_type args) vs es1 = (res,es')
Proof
  strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, builtin_args_length_ok_def] >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (rr, es1)` >>
  Cases_on `rr` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.lift_sum_def,
       exprSimWordArgsTheory.builtin_result_def, ec_source_tail_def,
       AllCaseEqs(), vyperStateTheory.ignore_bind_def] >>
  Cases_on `evaluate_builtin cx es1.accounts ann bt (MAP expr_type args) x` >>
  Cases_on `precompile_call_success bt es1` >>
  rename1 `precompile_call_success bt es1 = (out,es2)` >>
  Cases_on `out` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
      AllCaseEqs()] >> metis_tac[]
QED

Theorem ec_source_tail_cases[local]:
  (bt = ECAdd \/ bt = ECMul) ==>
  ec_source_tail cx ann bt tys vs es =
    case exprSimWordArgs$builtin_result cx es.accounts ann bt tys vs of
      INR ex => (INR ex,es)
    | INL v =>
        case es.outcomes of
          NONE => (INL (Value v),es)
        | SOME [] => (INR (Error (RuntimeError "precompile failed")),es)
        | SOME (co::rest) =>
            (if call_outcome_success co then INL (Value v)
             else INR (Error (RuntimeError "precompile failed")),
             es with outcomes := SOME rest)
Proof
  disch_tac >> simp[ec_source_tail_def] >>
  Cases_on `exprSimWordArgs$builtin_result cx es.accounts ann bt tys vs` >> simp[] >>
  drule ec_source_outcome_step >> disch_then (qspec_then `es` assume_tac) >>
  Cases_on `es.outcomes` >>
  gvs[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def] >>
  rename1 `SOME os` >> Cases_on `os` >>
  gvs[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def] >>
  Cases_on `call_outcome_success h` >> simp[]
QED

Theorem ec_two_args_source[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  eval_expr cx (Builtin ann bt [a;b]) es = (res,es') /\
  (do r <- eval_expr cx a; read_result cx r od) es = (r1,es1) /\
  (do r <- eval_expr cx b; read_result cx r od) es1 = (r2,es2) ==>
  (!ex. r1 = INR ex ==> res = INR ex) /\
  (!v ex. r1 = INL v /\ r2 = INR ex ==> res = INR ex) /\
  (!v1 v2. r1 = INL v1 /\ r2 = INL v2 ==>
    ec_source_tail cx ann bt [expr_type a;expr_type b] [v1;v2] es2 = (res,es'))
Proof
  strip_tac >> drule_at Any eval_expr_ec_cases >> simp[] >> strip_tac >>
  drule exprSimWordArgsTheory.eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  drule exprSimWordArgsTheory.eval_exprs_cons_cases >> strip_tac >>
  gvs[exprSimWordArgsTheory.eval_exprs_nil]
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

Theorem ec_suffix_oracle_failure[local]:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit 64w];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!z. ip = Var z ==> not_fresh_at sm z) /\
  (!z. op = Var z ==> not_fresh_at sm z) /\
  (target = 6w \/ target = 7w) /\
  (s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
  ?u. run_inst_seq (emitted_insts sm sb) s = Abort Revert_abort u
Proof
  strip_tac >> irule computed_suffix_oracle_failure >>
  simp[] >>
  goal_assum (drule_at (Pat `(_ : operand # compile_state) = _`)) >> simp[] >>
  simp[computed_precompile_def, venomCallOracleDefsTheory.venom_call_request_def,
       precompile_result_domain, wordsTheory.w2w_n2w,
       fcpLib.INDEX_CONV ``dimindex(:160)``]
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
  st.vs_outcomes = co::rest /\ co.co_success /\
  stmt_state_rel ctx func cenv cx es st /\ local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sf /\
  wb_frame cenv es sf s0 st /\ w2n wo + 64 < dimword (:256) /\
  FLOOKUP st.vs_allocas aid = SOME (w2n wo,64) /\
  sf.cs_next_id <= aid /\ aid < sm.cs_next_id /\
  (!name b sz. local_region cenv es.scopes st name b sz ==>
     regions_disjoint (w2n wo) 64 b sz) /\
  (!old b sz. old < sf.cs_next_id /\ FLOOKUP st.vs_allocas old = SOME (b,sz) ==>
     regions_disjoint (w2n wo) 64 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wo) 64 off (type_memory_size tv)) /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  ?t. run_inst_seq (emitted_insts sm sb) st = OK t /\
      vv_post ctx func cenv cx e es sf sb s0 (es with outcomes := SOME rest)
        (Value (mk_ec_result (x,y)))
        (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
Proof
  strip_tac >>
  drule_at (Pat `precompile_result _ _ = _`) computed_suffix_success >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ st = OK t` >>
  qexists `t` >> conj_tac >- simp[] >>
  qpat_x_assum `Abbrev _` kall_tac >>
  drule_all computed_suffix_output >> strip_tac >>
  `stmt_state_rel ctx func cenv cx
     (es with outcomes := SOME (DROP 1 st.vs_outcomes)) t /\
   wb_frame cenv es sf st t` by
    (irule computed_suffix_preserves >>
     simp[] >>
     goal_assum (drule_at (Pat `(_ : operand # compile_state) = _`)) >> simp[] >>
     metis_tac[]) >>
  `wb_frame cenv es sf s0 t` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`es`,`sf`,`st`] >> simp[]) >>
     qexistsl [`ctx`,`cx`,`func`] >> simp[]) >>
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
     qexists `name` >> irule exprSimPropsTheory.local_region_frame >>
     simp[] >> conj_tac
     >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sm`,`es.scopes`,`t`] >> simp[]) >>
  qpat_assum `expr_type e = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  irule ec_result_pointer_post >> simp[] >>
  conj_tac >- (qexists `aid` >> gvs[] >> metis_tac[]) >> gvs[]
QED

Theorem ec_points_run[local]:
  (!p scalar sf res sb func cenv cx es s point wscalar lo v e.
  compile_ecmul_point p scalar sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand p s = SOME point /\ eval_operand scalar s = SOME wscalar /\
  (!z. MEM (Var z) [p;scalar] ==> not_fresh_at sf z) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  w2n point + 64 < dimword (:256) /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  case vfmExecution$ecmul
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n wscalar) of
    NONE => ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t
  | SOME (x,y) =>
      if (?co rest. s.vs_outcomes = co::rest /\ co.co_success) then
        ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
          vv_post ctx func cenv cx e es sf sb s
            (es with outcomes := SOME (DROP 1 s.vs_outcomes))
            (Value (mk_ec_result (x,y)))
            (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
      else ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t) /\
  (!p1 p2 sf res sb func cenv cx es s point point2 lo v1 v2 e.
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME point2 /\
  (!z. MEM (Var z) [p1;p2] ==> not_fresh_at sf z) /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v1 p1 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v2 p2 s /\
  w2n point + 64 < dimword (:256) /\ w2n point2 + 64 < dimword (:256) /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  case vfmExecution$ecadd
    (w2n (mem_word_at (w2n point) s.vs_memory),
     w2n (mem_word_at (w2n point+32) s.vs_memory))
    (w2n (mem_word_at (w2n point2) s.vs_memory),
     w2n (mem_word_at (w2n point2+32) s.vs_memory)) of
    NONE => ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t
  | SOME (x,y) =>
      if (?co rest. s.vs_outcomes = co::rest /\ co.co_success) then
        ?t. run_inst_seq (emitted_insts sf sb) s = OK t /\
          vv_post ctx func cenv cx e es sf sb s
            (es with outcomes := SOME (DROP 1 s.vs_outcomes))
            (Value (mk_ec_result (x,y)))
            (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t
      else ?t. run_inst_seq (emitted_insts sf sb) s = Abort Revert_abort t)
Proof
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
    drule_all (CONJUNCT1 ec_points_prefix) >> strip_tac >>
    rename1 `compile_ecmul_point p1 p2 sf = _` >>
    rename1 `eval_operand p2 s = SOME second_word` >>
    qabbrev_tac `bytes =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes second_word T` >>
    qpat_x_assum `compile_ecmul_point _ _ _ = _` kall_tac >>
    suspend "allocation") >>
  rpt gen_tac >> strip_tac >>
    drule_all (CONJUNCT2 ec_points_prefix) >> strip_tac >>
    rename1 `eval_operand p2 s = SOME second_word` >>
    qabbrev_tac `bytes =
      word_to_bytes (mem_word_at (w2n point) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n point+32) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n second_word) s.vs_memory) T ++
      word_to_bytes (mem_word_at (w2n second_word+32) s.vs_memory) T` >>
    qpat_x_assum `compile_ecadd_points _ _ _ = _` kall_tac >>
    suspend "allocation"
QED

Resume ec_points_run[allocation]:
  markerLib.RESUME_TAC >> (
  qmatch_asmsub_abbrev_tac `context$compile_alloc_buffer insz sf = (ib,sa)` >>
  `insz < dimword (:256) /\ 64 < dimword (:256)` by
    simp[Abbr `insz`, wordsTheory.dimword_def] >>
  mp_tac (Q.INST [`insz` |-> `insz`, `outsz` |-> `64`,
    `sb` |-> `sp`, `code` |-> `emitted_insts sa sp`, `bytes` |-> `bytes`]
    (SPEC_ALL allocated_payload_run)) >>
  (impl_tac >- (
    simp[] >> rpt strip_tac >>
    `eval_operand p1 s1 = SOME point /\ eval_operand p2 s1 = SOME second_word` by
      (qpat_x_assum `eval_operand p1 s = SOME point` mp_tac >>
       qpat_x_assum `eval_operand p2 s = SOME second_word` mp_tac >>
       qpat_x_assum `!x. MEM (Var x) [p1;p2] ==> _` mp_tac >>
       qpat_x_assum `!x. not_fresh_at sf x ==> lookup_var x s1 = lookup_var x s` mp_tac >>
       qpat_x_assum `s1.vs_labels = s.vs_labels` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
       Cases_on `p1` >> Cases_on `p2` >>
       gvs[eval_operand_def] >> metis_tac[]) >>
    `!x. MEM (Var x) [p1;p2;ib.buf_operand] ==> not_fresh_at sa x` by
      (qpat_x_assum `!x. MEM (Var x) [p1;p2] ==> _` mp_tac >>
       qpat_x_assum `ib.buf_operand = Var _` mp_tac >>
       qpat_x_assum `not_fresh_at sa _` mp_tac >>
       qpat_x_assum `sf.cs_next_var <= sa.cs_next_var` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[listTheory.MEM] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
    `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
    `regions_disjoint (w2n wi) insz (w2n point) 64` by
      (rpt (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ p2 _` kall_tac) >>
       drule_all ec_point_fresh_scratch_disjoint >> simp[]) >>
    `cenv.ce_is_ctor ==> !name tv iv off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
      regions_disjoint (w2n wi) insz off (type_memory_size tv)` by
      (match_mp_tac (Q.INST
        [`s` |-> `s1`, `inst` |-> `mk_inst sf.cs_next_id ALLOCA [Lit (n2w insz)]
          [STRING #"%" (toString sf.cs_next_var)]`]
        precompile_alloca_immutable_disjoint) >>
       simp[mk_inst_def, Abbr `insz`]) >>
    Cases_on `insz = 96`
    >- (gvs[Abbr `insz`] >>
        `!z. MEM (Var z) [p1;Var x;p2] ==> not_fresh_at sa z` by
          (simp[MEM] >> metis_tac[]) >>
        `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
        drule_all (Q.INST [`s` |-> `s1`, `sc` |-> `sf`]
          (SPEC_ALL (CONJUNCT1 ec_input_stores_sim))) >> strip_tac >>
        suspend "payload_finish") >>
    gvs[Abbr `insz`] >>
    `regions_disjoint (w2n wi) 128 (w2n second_word) 64` by
      (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ p1 _` kall_tac >>
       drule_all ec_point_fresh_scratch_disjoint >> simp[]) >>
    `!z. MEM (Var z) [p1;p2;Var x] ==> not_fresh_at sa z` by
      (simp[MEM] >> metis_tac[]) >>
    `sf.cs_next_id <= sa.cs_next_id` by decide_tac >>
    drule_all (Q.INST [`s` |-> `s1`, `sc` |-> `sf`]
      (SPEC_ALL (CONJUNCT2 ec_input_stores_sim))) >> strip_tac >>
    suspend "payload_finish")) >>
  strip_tac >> suspend "suffix")
QED

Resume ec_points_run[payload_finish]:
  markerLib.RESUME_TAC >> (
  `t.vs_allocas = s1.vs_allocas` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _|> = _`
      (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  `eval_operand ib.buf_operand t = SOME wi` by
    (Cases_on `ib.buf_operand` >> gvs[eval_operand_def] >> metis_tac[]) >>
  qexists_tac `t` >> gvs[Abbr `bytes`])
QED

Resume ec_points_run[suffix]:
  markerLib.RESUME_TAC >> (
  rename1 `stmt_state_rel ctx func cenv cx es st` >>
  qpat_x_assum `ib.buf_operand = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `ob.buf_operand = _` (SUBST_ALL_TAC o SYM) >>
  qabbrev_tac `ip = ib.buf_operand` >>
  qabbrev_tac `op = ob.buf_operand` >>
  qabbrev_tac `aid = sp.cs_next_id` >>
  fs[Abbr `insz`, Abbr `bytes`] >>
  rpt (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` kall_tac) >>
  `local_ptrs_reserved cenv sm` by metis_tac[] >>
  qmatch_asmsub_rename_tac `eval_operand op st = SOME wo` >>
  `cenv.ce_is_ctor ==> !name tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
    regions_disjoint (w2n wo) 64 off (type_memory_size tv)` by
    (match_mp_tac (Q.INST
      [`s` |-> `st`, `inst` |-> `mk_inst sp.cs_next_id ALLOCA [Lit 64w]
        [STRING #"%" (toString sp.cs_next_var)]`]
      precompile_alloca_immutable_disjoint) >>
     simp[mk_inst_def, Abbr `aid`]) >>
  `(!z. ip = Var z ==> not_fresh_at sm z) /\
   (!z. op = Var z ==> not_fresh_at sm z)` by
    (conj_tac >> rpt strip_tac >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `option_CASE result` >>
  Cases_on `result`
  >- (qmatch_asmsub_rename_tac `eval_operand ip st = SOME wi` >>
      qmatch_asmsub_rename_tac `eval_operand op st = SOME po` >>
      `?u. run_inst_seq (emitted_insts sm sb) st = Abort Revert_abort u` by
        (irule ec_suffix_failure >>
         goal_assum (drule_at (Pat `(_ : operand # compile_state) = _`)) >> simp[] >>
         gvs[venomCallOracleDefsTheory.venom_call_request_def,
             venomStateTheory.read_memory_def, GSYM mem_bytes_at_def,
             wordsTheory.dimword_def, wordsTheory.w2w_n2w,
             fcpLib.INDEX_CONV ``dimindex(:160)``,
             ec_precompile_words, markerTheory.Abbrev_def]) >>
      pop_assum strip_assume_tac >>
      drule run_inst_seq_append >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  qmatch_goalsub_rename_tac `option_CASE (SOME r)` >>
  PairCases_on `r` >> simp[] >>
  `st.vs_outcomes = s.vs_outcomes` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  reverse (Cases_on `?co rest. s.vs_outcomes = co::rest /\ co.co_success`)
  >- (simp[] >>
      `st.vs_outcomes = [] \/
       ?co rest. st.vs_outcomes = co::rest /\ ~co.co_success` by
        (Cases_on `s.vs_outcomes` >> gvs[] >> metis_tac[]) >>
      `?u. run_inst_seq (emitted_insts sm sb) st = Abort Revert_abort u` by
        (irule ec_suffix_oracle_failure >>
         simp[] >>
         goal_assum (drule_at (Pat `(_ : operand # compile_state) = _`)) >>
         simp[] >> metis_tac[]) >>
      pop_assum strip_assume_tac >>
      drule run_inst_seq_append >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  simp[] >> pop_assum strip_assume_tac >>
  `?t. run_inst_seq (emitted_insts sm sb) st = OK t /\
       vv_post ctx func cenv cx e es sf sb s
         (es with outcomes := SOME (DROP 1 s.vs_outcomes))
         (Value (mk_ec_result (r0,r1)))
         (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) t` by
    (irule ec_suffix_pointer_post >> simp[] >>
     goal_assum (drule_at (Pat `(_ : operand # compile_state) = _`)) >> simp[] >>
     qexists_tac `aid` >> simp[] >>
     gvs[venomCallOracleDefsTheory.venom_call_request_def,
         venomStateTheory.read_memory_def, GSYM mem_bytes_at_def,
         wordsTheory.dimword_def, wordsTheory.w2w_n2w,
         fcpLib.INDEX_CONV ``dimindex(:160)``, markerTheory.Abbrev_def] >>
     metis_tac[ec_precompile_success]) >>
  pop_assum strip_assume_tac >>
  qpat_assum `run_inst_seq (emitted_insts sf sm) s = OK st`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> gvs[])
QED

Finalise ec_points_run

Theorem ec_pre_types[local]:
  (!cenv cx env ann args es.
  expr_body_pre cenv cx env (Builtin ann ECAdd args) es ==>
  ann = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?a b. args = [a;b] /\
    expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type b = ArrayT (BaseT (UintT 256)) (Fixed 2)) /\
  (!cenv cx env ann args es.
  expr_body_pre cenv cx env (Builtin ann ECMul args) es ==>
  ann = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ?a b. args = [a;b] /\
    expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type b = BaseT (UintT 256))
Proof
  conj_tac >> rpt gen_tac >>
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  imp_res_tac ecadd_types >> imp_res_tac ecmul_types >>
  gvs[MAP_EQ_CONS] >> metis_tac[]
QED

Theorem compile_ec_operands[local]:
  (!cenv ty ann a b sa vv sb.
  compile_expr cenv ty (Builtin ann ECMul [a;b]) sa = (vv,sb) ==>
  ?p scalar s1 sm res.
    lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
    lower_value compile_expr cenv (BaseT (UintT 256)) b s1 = (scalar,sm) /\
    compile_ecmul_point p scalar sm = (res,sb) /\
    vv = FST (as_ptr_val ann LocMemory (res,sb))) /\
  (!cenv ty ann a b sa vv sb.
  compile_expr cenv ty (Builtin ann ECAdd [a;b]) sa = (vv,sb) ==>
  ?p q s1 sm res.
    lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
    lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
    compile_ecadd_points p q sm = (res,sb) /\
    vv = FST (as_ptr_val ann LocMemory (res,sb)))
Proof
  conj_tac >> rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `compile_expr cenv ty (Builtin ann builtin [a;b]) sa` >>
  `compile_expr cenv ty (Builtin ann builtin [a;b]) sa =
    compile_builtin_dispatch cenv ann ty builtin [a;b] sa` by
    (irule compile_expr_builtin_dispatch >>
     Cases_on `a` >> simp[names_builtin_def, Abbr `builtin`] >>
     Cases_on `b` >> simp[names_builtin_def]) >>
  simp[] >>
  simp[Abbr `builtin`, Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `as_ptr_val ann LocMemory result` >>
  Cases_on `result` >> gvs[as_ptr_val_def]
QED

Theorem ec_point_pointer_bound[local]:
  stmt_state_rel ctx func cenv cx es s /\
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

Theorem ec_memory_semantics[local]:
  (!v1 v2 cx p1 p2 s.
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (BaseTV (UintT 256)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (BaseT (UintT 256)) v2 p2 s ==>
  ?point sw.
    eval_operand p1 s = SOME point /\ eval_operand p2 s = SOME sw /\
    evaluate_ecmul [v1;v2] =
      (case vfmExecution$ecmul
        (w2n (mem_word_at (w2n point) s.vs_memory),
         w2n (mem_word_at (w2n point+32) s.vs_memory)) (w2n sw) of
         NONE => INR (RuntimeError "ECMul invalid point")
       | SOME r => INL (mk_ec_result r))) /\
  (!v1 v2 cx p1 p2 s.
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
       | SOME r => INL (mk_ec_result r)))
Proof
  conj_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `value_has_type _ v1` (mp_then Any mp_tac ec_point_memory_words) >>
  disch_then drule >> strip_tac >>
  rename1 `eval_operand p1 s = SOME first_point` >>
  qexists_tac `first_point` >> simp[]
  >- (drule ec_uint256_encoding >> strip_tac >> gvs[] >>
      qpat_x_assum `expr_val_rel cx (BaseT (UintT 256)) _ _ _` mp_tac >>
      simp[expr_val_rel_def, evaluate_type_def, is_word_type_def] >>
      strip_tac >> gvs[] >>
      simp[evaluate_ecmul_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def]) >>
  qpat_assum `value_has_type _ v2` (mp_then Any mp_tac ec_point_memory_words) >>
  disch_then drule >> strip_tac >>
  rename1 `eval_operand p2 s = SOME second_point` >>
  qexists_tac `second_point` >>
  gvs[evaluate_ecadd_def, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem ec_points_path[local]:
  (!p scalar sf res sb func cenv cx es s lo v k e ctx ann tys r es'.
  compile_ecmul_point p scalar sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  (!z. MEM (Var z) [p;scalar] ==> not_fresh_at sf z) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  value_has_type (BaseTV (UintT 256)) k /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p s /\
  expr_val_rel cx (BaseT (UintT 256)) k scalar s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v p s /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ec_source_tail cx ann ECMul tys [v;k] es = (r,es') /\
  fn_has_code sf sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  ?n r'. gas_marked_path F ctx func s n r' /\
    ((?w. r' = OK w /\
        (?a. r = INL a /\
           vv_post ctx func cenv cx e es sf sb s es' a
             (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) w) /\
        w.vs_current_bb = sb.cs_current_bb /\
        w.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r' /\ expr_exit r r'))) /\
  (!p1 p2 sf res sb func cenv cx es s lo v1 v2 e ctx ann tys r es'.
  compile_ecadd_points p1 p2 sf = (res,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\
  (!i. MEM i (emitted_insts sf sb) ==> MEM i (fn_insts func)) /\
  (!z. MEM (Var z) [p1;p2] ==> not_fresh_at sf z) /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v2 /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 p1 s /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 p2 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v1 p1 s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v2 p2 s /\
  post_value_type cenv e = expr_type e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ec_source_tail cx ann ECAdd tys [v1;v2] es = (r,es') /\
  fn_has_code sf sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sf.cs_current_bb /\
  s.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  ?n r'. gas_marked_path F ctx func s n r' /\
    ((?w. r' = OK w /\
        (?a. r = INL a /\
           vv_post ctx func cenv cx e es sf sb s es' a
             (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) w) /\
        w.vs_current_bb = sb.cs_current_bb /\
        w.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r' /\ expr_exit r r')))
Proof
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule (CONJUNCT2 ec_points_code_shape) >> strip_tac >>
      qspecl_then [`ctx`, `func`, `sf`, `sb`, `s`,
        `\w. ?a. r = INL a /\
           vv_post ctx func cenv cx e es sf sb s es' a
             (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) w`,
        `expr_exit r`] mp_tac run_inst_seq_gas_path >>
      BETA_TAC >> reverse impl_tac >- (disch_then ACCEPT_TAC) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (fs[same_blocks_def] >> NO_TAC) >>
      TRY (simp[rich_listTheory.IS_PREFIX_APPEND] >> NO_TAC) >>
      drule_all (CONJUNCT1 ec_memory_semantics) >> strip_tac >>
      `w2n point + 64 < dimword (:256)` by
        (irule ec_point_pointer_bound >> goal_assum (drule_at Any) >>
         goal_assum (drule_at Any) >> qexistsl_tac [`ctx`,`func`] >> simp[]) >>
      drule_all (CONJUNCT1 ec_points_run) >> suspend "result") >>
  rpt gen_tac >> strip_tac >>
  drule (CONJUNCT1 ec_points_code_shape) >> strip_tac >>
  qspecl_then [`ctx`, `func`, `sf`, `sb`, `s`,
    `\w. ?a. r = INL a /\
       vv_post ctx func cenv cx e es sf sb s es' a
         (FST (as_ptr_val (expr_type e) LocMemory (res,sb))) w`,
    `expr_exit r`] mp_tac run_inst_seq_gas_path >>
  BETA_TAC >> reverse impl_tac >- (disch_then ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (fs[same_blocks_def] >> NO_TAC) >>
  TRY (simp[rich_listTheory.IS_PREFIX_APPEND] >> NO_TAC) >>
  qpat_assum `value_has_type _ v1`
    (mp_then Any mp_tac (CONJUNCT2 ec_memory_semantics)) >>
  disch_then (qspecl_then [`v2`, `cx`, `p1`, `p2`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  `w2n point + 64 < dimword (:256)` by
    (irule ec_point_pointer_bound >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> qexistsl_tac [`ctx`,`func`] >> simp[]) >>
  `w2n point2 + 64 < dimword (:256)` by
    (irule ec_point_pointer_bound >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> qexistsl_tac [`ctx`,`func`] >> simp[]) >>
  drule_all (CONJUNCT2 ec_points_run) >> suspend "result"
QED

Resume ec_points_path[result]:
  markerLib.RESUME_TAC >> (
  qmatch_goalsub_abbrev_tac `option_CASE result` >> Cases_on `result`
  >- (gvs[markerTheory.Abbrev_def] >> strip_tac >>
      gvs[ec_source_tail_cases, exprSimWordArgsTheory.builtin_result_def,
          evaluate_builtin_def, expr_exit_def] >>
      TRY (goal_assum (drule_at Any) >> simp[])) >>
  qmatch_goalsub_rename_tac `option_CASE (SOME pair)` >>
  PairCases_on `pair` >> gvs[markerTheory.Abbrev_def] >> strip_tac >>
  `es.outcomes = SOME s.vs_outcomes` by gvs[stmt_state_rel_def, state_rel_def] >>
  Cases_on `s.vs_outcomes`
  >- (gvs[ec_source_tail_cases, exprSimWordArgsTheory.builtin_result_def,
          evaluate_builtin_def, expr_exit_def] >>
      TRY (goal_assum (drule_at Any) >> simp[])) >>
  rename1 `s.vs_outcomes = co::rest` >>
  Cases_on `co.co_success` >>
  gvs[ec_source_tail_cases, exprSimWordArgsTheory.builtin_result_def,
      evaluate_builtin_def, expr_exit_def] >>
  TRY (goal_assum (drule_at Any) >> simp[]))
QED

Finalise ec_points_path

Theorem ec_expr_exit_INR_cast[local]:
  expr_exit (INR exc : value + exception) r ==>
  expr_exit (INR exc : eval_result + exception) r
Proof
  Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

(* A value step followed by a continuation whose outcome is counted from
   every normal endpoint of the step. *)
Theorem ec_outcome_then[local]:
  gas_outcome F tops (ctx,func)
    (m : evaluation_state -> value evaluation_result) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t) (\res ee r. expr_exit res r) /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==>
     R (INR exc) ee r) /\
  (!gs v ee t. m (es with gas_obs := gs) = (INL v, ee) /\ ee.gas_obs = [] /\
     P v ee t /\ ~t.vs_halted ==>
     gas_outcome F tops (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome F tops (ctx,func) (bind m k) (es,s0) Q R
Proof
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
      gvs[]
      >- (`m (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL v, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
               (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          qpat_x_assum `!gs v ee t. _`
            (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `v`,
                          `es_end with gas_obs := []`, `t`] mp_tac) >>
          (impl_tac >- simp[]) >>
          disch_then (qx_choose_then `right` strip_assume_tac)
          >- (qexists_tac `marks ++ right` >> disj1_tac >>
              qpat_x_assum `gas_summary_at F _ right _ _ _ _`
                (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
              disch_then (qx_choosel_then [`fres`, `fin`, `fr`]
                (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
              drule_all gas_marked_exec_bind_normal >> strip_tac >>
              rewrite_tac[gas_summary_at_def] >>
              qexistsl_tac [`fres`, `fin`, `fr`] >> asm_rewrite_tac[]) >>
          qexists_tac `marks ++ right` >> disj2_tac >>
          `ignore_bind (bind m k) (return ()) =
           bind m (\v. ignore_bind (k v) (return ()))` by
            simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
          pop_assum SUBST1_TAC >>
          irule_at Any gas_exempt_cert_bind_value >>
          first_assum (irule_at Any) >> BETA_TAC >>
          first_assum (irule_at Any)) >>
      Cases_on `res` >> gvs[] >>
      rename1 `expr_exit (INR exc) r` >>
      qexists_tac `marks` >> disj1_tac >> rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  `ignore_bind (bind m k) (return ()) =
   bind m (\v. ignore_bind (k v) (return ()))` by
    simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >>
  metis_tac[gas_exempt_cert_error_value]
QED

Theorem ec_eval_bind[local]:
  (bt = ECAdd \/ bt = ECMul) ==>
  eval_expr cx (Builtin ann bt [a;b]) =
  bind (bind (eval_expr cx a) (read_result cx))
    (\v1. bind (bind (eval_expr cx b) (read_result cx))
      (\v2. ec_source_tail cx ann bt [expr_type a; expr_type b] [v1;v2]))
Proof
  disch_tac >>
  `eval_expr cx (Builtin ann bt [a;b]) =
   bind (eval_exprs cx [a;b])
     (\vs. ec_source_tail cx ann bt (MAP expr_type [a;b]) vs)` by
    (qpat_x_assum `_ \/ _` mp_tac >> simp[FUN_EQ_THM] >> rpt strip_tac >>
     Cases_on `eval_expr cx (Builtin ann bt [a;b]) x` >>
     drule_at (Pat `eval_expr _ _ _ = _`) eval_expr_ec_cases >>
     impl_tac >- simp[] >> strip_tac >>
     gvs[vyperStateTheory.bind_def]) >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, exprSimWordArgsTheory.eval_exprs_nil,
         vyperStateTheory.return_def] >>
  asm_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[vyperStateTheory.bind_assoc, vyperStateTheory.bind_return]
QED

Theorem ec_source_tail_gas_obs[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  ec_source_tail cx ann bt tys vs es = (r,es') ==>
  ec_source_tail cx ann bt tys vs (es with gas_obs := g) =
    (r, es' with gas_obs := g)
Proof
  rpt strip_tac >> gvs[ec_source_tail_cases, AllCaseEqs()] >>
  simp[vyperStateTheory.evaluation_state_component_equality]
QED

Theorem ec_source_tail_scopes[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  ec_source_tail cx ann bt tys vs es = (r,es') ==>
  es'.scopes = es.scopes
Proof
  rpt strip_tac >> gvs[ec_source_tail_cases, AllCaseEqs()]
QED

(* Both operands as counted outcomes, then the point suffix as an actual
   counted target path from every pair of operand endpoints. *)
Theorem ec_binary_call_gas[local]:
  exprs_case nocalls ctx func cenv cx [a;b] /\
  expr_body_pre cenv cx env (Builtin ann bt [a;b]) es /\
  (nocalls ==> int_calls_expr (Builtin ann bt [a;b]) = []) /\
  (bt = ECAdd \/ bt = ECMul) /\
  expr_type a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  lower_value compile_expr cenv (expr_type a) a sa = (p,s1) /\
  lower_value compile_expr cenv (expr_type b) b s1 = (q,sm) /\
  cs_extends sm sb /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!es1 es2 v1 v2 t u res es'.
    expr_post ctx func cenv cx a es sa s1 s0 es1 v1 p t /\
    expr_post ctx func cenv cx b es1 s1 sm t es2 v2 q u /\
    expr_val_rel cx (expr_type a) v1 p u /\
    expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u /\
    expr_result_typed env a (Value v1) /\ expr_result_typed env b (Value v2) /\
    stmt_state_rel ctx func cenv cx es2 u /\ local_ptrs_reserved cenv sm /\
    fn_has_code sm sb func /\ ~u.vs_halted /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!z. MEM (Var z) [p;q] ==> not_fresh_at sm z) /\
    ec_source_tail cx ann bt [expr_type a;expr_type b] [v1;v2] es2 = (res,es') ==>
    ?n r. gas_marked_path F ctx func u n r /\
      ((?w. r = OK w /\
          (?tv. res = INL tv /\
             vv_post ctx func cenv cx (Builtin ann bt [a;b]) es2 sm sb u es'
               tv vv w) /\
          w.vs_current_bb = sb.cs_current_bb /\
          w.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\ expr_exit res r))) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx (Builtin ann bt [a;b]))
    (es,s0)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx (Builtin ann bt [a;b]) es sa sb s0 ee tv vv t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!n. bt <> Slice n` by (rpt strip_tac >> gvs[]) >>
  `expr_body_pre cenv cx env a es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`a`, `es`] mp_tac) >> simp[]) >>
  `nocalls ==> int_calls_expr a = []` by
    metis_tac[int_calls_builtin_arg, listTheory.MEM] >>
  `nocalls ==> int_calls_expr b = []` by
    metis_tac[int_calls_builtin_arg, listTheory.MEM] >>
  `post_value_type cenv a = expr_type a` by
    (irule post_value_type_ec_point >> simp[] >>
     qexistsl_tac [`cx`,`env`,`es`] >> fs[expr_body_pre_def]) >>
  `expr_sim ctx func cenv cx (expr_type a) a es` by
    (gvs[exprs_case_def, expr_sim_case_def] >> metis_tac[]) >>
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
  `safe_operand s1 p` by
    metis_tac[ec_point_lower_value_safe_operand] >>
  `!l. p <> Label l` by gvs[safe_operand_def] >>
  qpat_assum `bt = ECAdd \/ bt = ECMul`
    (fn th => rewrite_tac[MATCH_MP ec_eval_bind th]) >>
  irule ec_outcome_then >>
  conj_tac >- (BETA_TAC >> metis_tac[ec_expr_exit_INR_cast]) >>
  qexists_tac `\v1 ee t. expr_post ctx func cenv cx a es sa s1 s0 ee v1 p t /\
     t.vs_current_bb = s1.cs_current_bb /\
     t.vs_inst_idx = LENGTH s1.cs_current_insts` >>
  BETA_TAC >> reverse conj_tac
  >- (irule exprSimWordArgsTheory.expr_sim_apply >>
      simp[] >> conj_tac >- metis_tac[expr_body_pre_gas_admissible] >>
      qexists_tac `expr_type a` >> simp[]) >>
  qx_genl_tac [`gs1`, `v1`, `es1`, `t`] >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `a`, `es with gas_obs := gs1`, `INL v1`, `es1`]
    mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `expr_result_typed env a (Value v1)` by simp[] >>
  `expr_body_pre cenv cx env b es1` by
    (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_builtin_arg) >>
     disch_then (qspecl_then [`b`, `es1`] mp_tac) >> simp[]) >>
  `expr_sim ctx func cenv cx (expr_type b) b es1` by
    (qpat_x_assum `exprs_case _ _ _ _ _ _` mp_tac >>
     simp[exprs_case_def] >> strip_tac >>
     `?s tv t s1 v t1. eval_expr cx a s = (INL tv,t) /\
                       read_result cx tv s1 = (INL v,t1)` by
       (qpat_x_assum `bind (eval_expr cx a) _ _ = _` mp_tac >>
        simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
     gvs[expr_sim_case_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es1 t` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (qpat_assum `bind (eval_expr cx a) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
            exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >>
     simp[]) >>
  irule ec_outcome_then >>
  conj_tac >- (BETA_TAC >> metis_tac[ec_expr_exit_INR_cast]) >>
  qexists_tac `\v2 ee u. expr_post ctx func cenv cx b es1 s1 sm t ee v2 q u /\
     u.vs_current_bb = sm.cs_current_bb /\
     u.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  BETA_TAC >> reverse conj_tac
  >- (irule exprSimWordArgsTheory.expr_sim_apply >>
      simp[] >> conj_tac >- metis_tac[expr_body_pre_gas_admissible] >>
      qexists_tac `expr_type b` >> simp[]) >>
  qx_genl_tac [`gs2`, `v2`, `es2`, `u`] >> strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `b`, `es1 with gas_obs := gs2`, `INL v2`, `es2`]
    mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_eval) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `expr_result_typed env b (Value v2)` by simp[] >>
  `stmt_state_rel ctx func cenv cx es2 u` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    (qpat_assum `bind (eval_expr cx b) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
            exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >>
     simp[]) >>
  `?w. eval_operand p t = SOME w /\ eval_operand p u = SOME w` by
    metis_tac[expr_post_operand_word] >>
  `!w. eval_operand p t = SOME w ==> eval_operand p u = SOME w` by
    metis_tac[optionTheory.SOME_11] >>
  `expr_val_rel cx (expr_type a) v1 p u /\
   expr_val_at cenv cx (expr_type a) sa sm es2 v1 p u` by
    metis_tac[ec_point_operand_kept] >>
  `!z. MEM (Var z) [p;q] ==> not_fresh_at sm z` by
    (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var,
                         freshWritesTheory.not_fresh_at_mono]) >>
  Cases_on `ec_source_tail cx ann bt [expr_type a; expr_type b] [v1; v2] es2` >>
  rename1 `_ = (res, es')` >>
  qpat_x_assum `!es1 es2 v1 v2 t u res es'. _`
    (qspecl_then [`es1`, `es2`, `v1`, `v2`, `t`, `u`, `res`, `es'`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `es2 with gas_obs := [] = es2` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `!g. ec_source_tail cx ann bt [expr_type a; expr_type b] [v1; v2]
         (es2 with gas_obs := g) = (res, es' with gas_obs := g)` by
    metis_tac[ec_source_tail_gas_obs] >>
  `es' with gas_obs := [] = es'` by
    (qpat_x_assum `!g. _` (qspec_then `[]` mp_tac) >>
     qpat_x_assum `es2 with gas_obs := [] = es2` (fn th => rewrite_tac[th]) >>
     qpat_assum `ec_source_tail _ _ _ _ _ es2 = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[pairTheory.PAIR_EQ] >> metis_tac[]) >>
  `wb_frame cenv es sa s0 u` by
    (match_mp_tac (Q.SPECL [`func`, `cenv`, `cx`, `es`, `s0`, `sa`, `es1`, `s1`,
                            `t`, `u`, `ctx`] exprSimWordArgsTheory.wb_frame_trans) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     metis_tac[exprSimWordArgsTheory.expr_post_frame]) >>
  `gas_marked_exec F (ctx,func)
     (ec_source_tail cx ann bt [expr_type a; expr_type b] [v1; v2])
     (es2,u) (REPLICATE n F) res es' r` by
    (irule gas_marked_exec_no_source_read >> conj_tac >>
     first_assum ACCEPT_TAC) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `REPLICATE n F` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `es'`, `r`] >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (fn th => rewrite_tac[th]) >>
  BETA_TAC >>
  qpat_x_assum `es' with gas_obs := [] = es'` SUBST1_TAC >>
  FIRST [disj2_tac >> simp[] >> NO_TAC,
         disj1_tac >> simp[] >>
         irule exprSimCalldataSliceTheory.vv_post_prefix_frame >>
         first_assum (irule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
         simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]]
QED

Theorem compile_ec_call_case[local]:
  (!nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECMul args)) /\
  (!nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECAdd args))
Proof
  conj_tac >> rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_vv_case_def] >> rpt strip_tac >>
  imp_res_tac ec_pre_types >> gvs[] >>
  rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  imp_res_tac compile_ec_operands >>
  rename1 `vv = FST (as_ptr_val _ LocMemory (result_ptr,sb))` >>
  `cs_extends sm sb` by
    (imp_res_tac ec_points_code_shape >>
     simp[cs_extends_def] >> qexists_tac `[]` >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  gvs[] >> irule ec_binary_call_gas >> simp[] >>
  (reverse conj_tac
  >- (qexists_tac `nocalls` >> simp[]) >>
  qexists_tac `env` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `expr_result_typed env a (Value v1)` mp_tac >>
  qpat_assum `expr_result_typed env b (Value v2)` mp_tac >>
  simp[IgnAsm `expr_result_typed _ _ _`,
       vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def, evaluate_type_def] >>
  strip_tac >> strip_tac >>
  suspend "point_payload")
QED

Resume compile_ec_call_case[point_payload]:
  markerLib.RESUME_TAC >~ [`compile_ecmul_point _ _ _ = _`]
  >- (`post_value_type cenv b = expr_type b` by
        simp[post_value_type_word, is_word_type_def] >>
      `expr_val_rel cx (BaseT (UintT 256)) v2 scalar u` by gvs[expr_post_def] >>
      irule (SRULE []
        (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul [a;b]`]
          (SPEC_ALL (CONJUNCT1 ec_points_path)))) >>
      simp[vyperASTTheory.expr_type_def] >>
      conj_tac >- metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
      goal_assum (drule_at (Pat `ec_source_tail _ _ _ _ _ _ = _`)) >>
      qexistsl_tac [`sa`, `p`, `scalar`] >> simp[] >> metis_tac[]) >>
  `post_value_type cenv b = expr_type b` by
    (irule post_value_type_ec_point >> simp[] >>
     qexistsl_tac [`cx`,`env`,`es`] >>
     qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, well_typed_expr_def]) >>
  `expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v2 q u /\
   expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) s1 sm es2 v2 q u` by
    gvs[expr_post_def] >>
  qpat_assum `lower_value _ _ _ a _ = _`
    (mp_then Any mp_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >> strip_tac >>
  `expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa sm es2 v2 q u` by
    (irule expr_val_at_start_mono >> goal_assum (drule_at Any) >> simp[]) >>
  irule (SRULE []
    (Q.INST [`e` |-> `Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd [a;b]`]
      (SPEC_ALL (CONJUNCT2 ec_points_path)))) >>
  simp[vyperASTTheory.expr_type_def] >>
  conj_tac >- metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  goal_assum (drule_at (Pat `ec_source_tail _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`sa`, `p`, `q`] >> simp[] >> metis_tac[]
QED

Finalise compile_ec_call_case

Theorem compile_ecadd_call_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECAdd args)
Proof
  metis_tac[CONJUNCT2 compile_ec_call_case]
QED

Theorem compile_ecmul_call_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann ECMul args)
Proof
  metis_tac[CONJUNCT1 compile_ec_call_case]
QED
