(* Layout classification at valued-return expression boundaries. *)
Theory incompatibleReturnLayout
Ancestors
  internalReturnMetadata intCallStep externalNormalizePremises compileEnv
  valueEncoding exprLowering vyperTypeSystem vyperTypeArgFits vyperValue
  abiTypeBoundProps vyperABI exprSimSource exprSafeOperand
  exprSimHypsDefs vyperTypeInvariants vyperAST

Theorem nonzero_internal_call_located:
  !cfn ce ret ty fid args dret sa vv sb ret_count rbs pvs.
  compile_call cfn ce ret ty (IntCall fid) args dret sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (ret_count,rbs,pvs) /\
  (0 < ret_count \/ 0 < rbs) ==>
  ?p. vv = LocatedValue (ce.ce_func_return_type (nsid_to_string fid)) p
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_call_intcall_shape >> strip_tac >>
  Cases_on `ret_count = 0` >> gvs[] >> metis_tac[]
QED

Theorem literal_string_layout:
  well_typed_expr env (Literal (BaseT (StringT n)) (StringL s)) ==>
  is_bytestring_type (lowered_value_type ce (Literal (BaseT (StringT n)) (StringL s))) /\
  arg_type_fits (lowered_value_type ce (Literal (BaseT (StringT n)) (StringL s)))
    (BaseT (StringT n))
Proof
  simp[well_typed_expr_def, well_typed_literal_def, lowered_value_type_def,
       is_bytestring_type_def, arg_type_fits_def, compatible_bound_def]
QED

Theorem literal_bytes_layout:
  well_typed_expr env (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)) ==>
  is_bytestring_type (lowered_value_type ce (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs))) /\
  arg_type_fits (lowered_value_type ce (Literal (BaseT (BytesT (Dynamic n))) (BytesL bs)))
    (BaseT (BytesT (Dynamic n)))
Proof
  simp[well_typed_expr_def, well_typed_literal_def, lowered_value_type_def,
       is_bytestring_type_def, arg_type_fits_def, compatible_bound_def]
QED

Theorem abi_encode_layout:
  well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) target args) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  EVERY (\t. IS_SOME (evaluate_type env.type_defs t)) (MAP expr_type args) ==>
  is_bytestring_type ann /\
  is_bytestring_type (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) /\
  arg_type_fits (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) ann
Proof
  strip_tac >> drule_all abi_size_bound_tuple_typed >> strip_tac >>
  gvs[well_typed_expr_def, type_builtin_result_ok_def,
      abi_encode_size_ok_def, lowered_value_type_def,
      is_bytestring_type_def, arg_type_fits_def] >>
  Cases_on `args`
  >- gvs[well_typed_type_builtin_args_def] >>
  Cases_on `t` >> gvs[]
  >- (Cases_on `ensure` >> gvs[]
      >- (Cases_on `mid` >>
          gvs[well_typed_type_builtin_args_def, abi_encode_method_id_size_def,
              vyperASTTheory.abi_encode_method_id_bytes_def]) >>
      gvs[optionTheory.IS_SOME_EXISTS] >> drule_all abi_props_vyper_typed >>
      strip_tac >> Cases_on `mid` >>
      gvs[well_typed_type_builtin_args_def, abi_encode_method_id_size_def,
          vyperASTTheory.abi_encode_method_id_bytes_def]) >>
  Cases_on `mid` >>
  gvs[well_typed_type_builtin_args_def, abi_encode_method_id_size_def,
      vyperASTTheory.abi_encode_method_id_bytes_def]
QED

Theorem expr_sim_inv_args_evaluate:
  expr_sim_inv ce cx env es /\ well_typed_exprs env args ==>
  EVERY (\ty. IS_SOME (evaluate_type env.type_defs ty)) (MAP expr_type args)
Proof
  strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
           well_formed_type env.type_defs ty` by
    (rpt strip_tac >> simp[well_formed_type_def] >>
     metis_tac[env_consistent_var_type_evaluates]) >>
  simp[listTheory.EVERY_MEM, listTheory.MEM_MAP] >> rpt strip_tac >>
  rename1 `MEM a args` >>
  `well_typed_expr env a` by metis_tac[well_typed_exprs_member] >>
  drule_all well_typed_expr_type_well_formed >>
  simp[well_formed_type_def]
QED

Theorem incompatible_return_layout_located:
  !tops am tx ce env es ret e ty sa vv sm.
  supported_program tops /\ source_typing_ok tops am tx /\
  expr_sim_inv ce
    (initial_evaluation_context am.sources am.layouts tx NONE) env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  ce.ce_func_info = build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
  ce.ce_func_return_type = build_func_return_type tops /\
  ce.ce_struct_fields = make_struct_fields_map tops /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  compile_expr ce ty e sa = (vv,sm) ==>
  ?declared p. vv = LocatedValue declared p /\ declared <> expr_type e
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
  Cases_on `e` >> gvs[lowered_value_type_def, expr_type_def]
  >>~- ([`Literal ann lit`],
      Cases_on `lit` >> Cases_on `ann` >>
      gvs[lowered_value_type_def, well_typed_expr_def, well_typed_literal_def] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[lowered_value_type_def, expr_type_def, is_bytestring_type_def,
          well_typed_literal_def, arg_type_fits_def, compatible_bound_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[lowered_value_type_def, expr_type_def, is_bytestring_type_def,
          well_typed_literal_def, arg_type_fits_def, compatible_bound_def])
  >>~- ([`TypeBuiltin ann tb target xs`],
      Cases_on `tb` >> gvs[lowered_value_type_def, expr_type_def] >>
      `well_typed_exprs env xs` by
        fs[well_typed_expr_def, well_typed_type_builtin_args_def] >>
      drule_all expr_sim_inv_args_evaluate >> strip_tac >>
      `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
        fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
      drule_all abi_encode_layout >>
      gvs[lowered_value_type_def, expr_type_def]) >>
  rename1 `Call ann target xs drv` >>
  Cases_on `target` >> gvs[lowered_value_type_def, expr_type_def] >>
  rename1 `IntCall fid` >>
  namedCases_on `ce.ce_func_info (nsid_to_string fid)` ["ret_count rbs pvs"] >>
  `ce.ce_func_return_type (nsid_to_string fid) <> ann` by metis_tac[] >>
  drule_all typed_widened_internal_convention >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_def] >> strip_tac >>
  drule nonzero_internal_call_located >>
  disch_then drule >> simp[] >> metis_tac[]
QED
