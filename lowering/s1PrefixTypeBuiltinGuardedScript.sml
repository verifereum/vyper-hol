(* Arity-guarded TypeBuiltin prefix introduction. *)
Theory s1PrefixTypeBuiltinGuarded
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixOfVV bodyFullPreds vyperInterpreter
  vyperAST vyperContext vyperState stmtLowering list
  s1PrefixAnnAssignEmptyRhs s1PrefixBuiltinLeaves
  s1PrefixTypeBuiltinExtract32 s1PrefixAbiDecodeExprConditional
  s1PrefixAbiEncodeTupleFull s1PrefixAbiEncodeNonwordFull s1PrefixAbiEncodeWordFull
  s1PrefixConvertBytesJoint s1PrefixConvertDynamicJoint s1PrefixConvertScalarJoint
  exprSimConvert exprSimAbiEncodeRuntimeInputs bodyFullSimProjection bodyFullExprsSingleton

Theorem body_type_builtin_case_prefix:
  !cx v11 tb typ es.
  (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt gen_tac >> Cases_on `tb`
  >- (simp[Once body_expr_prefix_ok_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
      conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
      rw[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
      once_rewrite_tac[GSYM gas_prefix_full_bind_read_result] >>
      irule annassign_empty_rhs_prefix >> simp[is_empty_value_expr_def])
  >- (simp[Once body_expr_prefix_ok_def] >> rpt strip_tac >>
      metis_tac[bound_builtin_sim_prefix, MEM])
  >- (simp[Once body_expr_prefix_ok_def] >> rpt strip_tac >>
      metis_tac[bound_builtin_sim_prefix, MEM])
  >- (simp[Once body_expr_prefix_ok_def] >> rpt strip_tac >>
      metis_tac[bound_builtin_sim_prefix, MEM])
  >- suspend "convert"
  >- MATCH_ACCEPT_TAC extract32_expr_prefix_ok
  >- MATCH_ACCEPT_TAC abi_decode_expr_prefix >>
  suspend "encode"
QED

Resume body_type_builtin_case_prefix[convert]:
  strip_tac >> simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `type_check (type_builtin_args_length_ok Convert 1)
       "TypeBuiltin args" es' = (INL (),es')` by
    simp[type_check_def,type_builtin_args_length_ok_def,assert_def,return_def] >>
  `body_exprs_full_ok cx [e1] /\ body_exprs_prefix_ok cx [e1]` by metis_tac[] >>
  gvs[bodyFullExprsSingletonTheory.body_exprs_full_ok_singleton,
      body_exprs_prefix_ok_def] >>
  conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
  Cases_on `is_bytestring_type typ`
  >- (irule convert_bytes_vv_sim_prefix >> simp[] >> metis_tac[]) >>
  Cases_on `is_bytestring_type (expr_type e1)`
  >- (irule convert_dynamic_vv_sim_prefix >> simp[] >> metis_tac[]) >>
  irule convert_scalar_vv_sim_prefix >> simp[] >> metis_tac[]
QED

Resume body_type_builtin_case_prefix[encode]:
  strip_tac >> simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
  Cases_on `LENGTH es = 1 /\ ~b`
  >- suspend "encode_singleton" >>
  irule abi_encode_tuple_vv_prefix_from_packaging >> simp[] >> metis_tac[]
QED

Resume body_type_builtin_case_prefix[encode_singleton]:
  gvs[] >> Cases_on `es` >> gvs[] >>
  rename1 `TypeBuiltin _ (AbiEncode F m) _ [e]` >>
  `type_check (type_builtin_args_length_ok (AbiEncode F m) 1)
       "TypeBuiltin args" es' = (INL (),es')` by
    simp[type_check_def,type_builtin_args_length_ok_def,assert_def,return_def] >>
  `body_exprs_full_ok cx [e] /\ body_exprs_prefix_ok cx [e]` by metis_tac[] >>
  gvs[bodyFullExprsSingletonTheory.body_exprs_full_ok_singleton,
      body_exprs_prefix_ok_def] >>
  Cases_on `is_word_type (expr_type e)`
  >- suspend "encode_word" >>
  irule abi_encode_nonword_vv_prefix_from_packaging >> simp[] >> metis_tac[]
QED

Resume body_type_builtin_case_prefix[encode_word]:
  `expr_body_pre cenv cx env e es'` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  irule abi_encode_word_vv_prefix_from_packaging >> simp[] >>
  qpat_assum `body_expr_prefix_ok cx e`
    (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  metis_tac[bodyFullSimProjectionTheory.body_expr_full_ok_simulations]
QED

Finalise body_type_builtin_case_prefix
