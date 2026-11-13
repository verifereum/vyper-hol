(* Supported assignment StackValue classification boundaries. *)
Theory assignPlaceStackShape
Ancestors
  bodyAssignPlace exprLowering exprSafeOperand exprSimConvertBytes
  typedMemoryCopy vyperTypeSystem compileEnv vyperContext vyperValue vyperAST
  internalReturnMetadata externalNormalizePremises valueEncodingProps valueEncoding
  supportedExprForms supportedTypes

Theorem assign_place_rhs_not_none:
  type_stmt env ret (Assign (BaseTarget bt) e) = SOME env' ==>
  expr_type e <> NoneT
Proof
  strip_tac >> drule assign_place_typing >> strip_tac >>
  metis_tac[assignable_type_not_NoneT]
QED

Theorem conversion_result_word_or_bytestring[local]:
  well_formed_type tenv dst /\ valid_conversion src dst ==>
  is_word_type dst \/ is_bytestring_type dst
Proof
  Cases_on `src` >> Cases_on `dst` >>
  simp[valid_conversion_def, is_word_type_def, is_bytestring_type_def] >>
  rpt strip_tac >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[valid_conversion_def, is_word_type_def, is_bytestring_type_def,
      well_formed_type_def, evaluate_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[valid_conversion_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem assign_place_convert_result_shape:
  type_stmt env ret
    (Assign (BaseTarget bt) (TypeBuiltin ty Convert target args)) = SOME env' /\
  type_place_target env bt = SOME (Type dty) ==>
  is_word_type ty \/
  (is_bytestring_type ty /\
   is_bytestring_type (lowered_value_type cenv (TypeBuiltin ty Convert target args)) /\
   is_bytestring_type dty)
Proof
  strip_tac >> drule assign_place_typing >> strip_tac >>
  gvs[well_typed_expr_def, type_builtin_result_ok_def,
      well_typed_type_builtin_args_def, expr_type_def] >>
  drule_all conversion_result_word_or_bytestring >> strip_tac >> simp[] >>
  simp[lowered_value_type_def, expr_type_def] >>
  metis_tac[type_widens_from_bytestring]
QED

Theorem compile_internal_stack_no_buffer:
  cenv.ce_func_info (nsid_to_string id) = (ret_count,rbs,pvs) /\
  compile_call f cenv rt ty (IntCall id) args drv sa = (StackValue vt op,sb) ==>
  ret_count = 0 /\ rbs = 0
Proof
  simp[compile_call_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt IF_CASES_TAC >>
  gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem assign_internal_stack_typed_impossible:
  cenv.ce_func_return_type (nsid_to_string id) = declared /\
  cenv.ce_func_info (nsid_to_string id) =
    compute_func_info sft declared (type_memory_bytes cenv declared) ats /\
  type_widens_to tenv declared ann /\ assignable_type tenv ann /\
  evaluate_type tenv declared = SOME tv /\
  type_memory_bytes cenv declared = type_memory_size tv /\
  compile_call f cenv ann ty (IntCall id) args drv sa = (StackValue vt op,sb) ==>
  F
Proof
  strip_tac >>
  `0 < type_memory_size tv` by
    (Cases_on `declared = ann` >> gvs[]
     >- metis_tac[assignable_type_slot_size_pos, type_memory_size_pos] >>
     metis_tac[normalize_return_source_positive]) >>
  `declared <> NoneT` by
    (strip_tac >> gvs[evaluate_type_def, type_memory_size_def]) >>
  Cases_on `compute_func_info sft declared (type_memory_bytes cenv declared) ats` >>
  PairCases_on `r` >>
  drule_all compile_internal_stack_no_buffer >> strip_tac >> gvs[] >>
  drule_all positive_compute_func_info >> simp[]
QED

Theorem compile_ifexp_stack_is_word:
  compile_expr_body f g h ce ty (IfExp ann c a b) sa = (StackValue vt op,sb) ==>
  is_word_type ann
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> gvs[]
QED

Theorem compile_structlit_not_stack:
  compile_expr_body f g h ce ty (StructLit ann name fields) sa =
    (StackValue vt op,sb) ==> F
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_pop_not_stack:
  compile_expr_body f g h ce ty (Pop ann target) sa = (StackValue vt op,sb) ==> F
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_attribute_not_stack:
  compile_attribute f ce rt ty obj fld sa = (StackValue vt op,sb) ==> F
Proof
  simp[compile_attribute_def, LET_THM, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_subscript_not_stack:
  compile_subscript f ce rt ty obj idx sa = (StackValue vt op,sb) ==> F
Proof
  simp[compile_subscript_def, LET_THM, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `place_type ce obj`
  >- (simp[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[])) >>
  rename1 `ValPT bt` >> Cases_on `bt` >>
  simp[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_typed_literal_stack_is_word:
  well_formed_type tenv ann /\ well_typed_literal ann lit /\
  compile_literal_vv ann lit sa = (StackValue vt op,sb) ==>
  is_word_type ann
Proof
  Cases_on `lit` >> Cases_on `ann` >>
  simp[well_typed_literal_def, well_formed_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[well_typed_literal_def, well_formed_type_def, is_word_type_def, compile_literal_vv_def,
       comp_bind_def, comp_return_def, LET_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[is_word_type_def, compile_literal_vv_def, comp_bind_def,
      comp_return_def, LET_THM, evaluate_type_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem as_ptr_val_not_stack[local]:
  as_ptr_val ann loc result <> (StackValue vt op,sb)
Proof
  Cases_on `result` >> simp[as_ptr_val_def]
QED

Theorem compile_type_abi_encode_not_stack[local]:
  compile_type_builtin_dispatch_body f ce ann ty (AbiEncode ensure mid) dst args sa =
    (StackValue vt op,sb) ==> F
Proof
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  simp[as_ptr_val_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[as_ptr_val_not_stack]
QED

Theorem compile_type_abi_decode_not_stack[local]:
  compile_type_builtin_dispatch_body f ce ann ty (AbiDecode unwrap) dst args sa =
    (StackValue vt op,sb) ==> F
Proof
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> simp[as_ptr_val_not_stack]
QED

Theorem compile_empty_stack_is_word[local]:
  compile_type_builtin_dispatch_body f ce ann ty Empty dst args sa =
    (StackValue vt op,sb) ==> is_word_type dst
Proof
  simp[compile_type_builtin_dispatch_body_def] >>
  IF_CASES_TAC >> simp[LET_THM] >> pairarg_tac >> simp[]
QED

Theorem supported_numeric_is_word[local]:
  supported_numeric_type ann ==> is_word_type ann
Proof
  Cases_on `ann` >> simp[supported_numeric_type_def, supported_integer_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_numeric_type_def, supported_integer_type_def, is_word_type_def]
QED

Theorem supported_type_builtin_stack_word:
  supported_type_builtin_form tops ann tb dst args /\ tb <> Convert /\
  compile_type_builtin_dispatch_body f ce ann ty tb dst args sa =
    (StackValue vt op,sb) ==> is_word_type ann
Proof
  Cases_on `tb` >>
  simp[supported_type_builtin_form_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >~ [`Empty`] >-
    (Cases_on `args` >> gvs[] >- metis_tac[compile_empty_stack_is_word] >>
     Cases_on `t` >> gvs[])
  >~ [`AbiEncode ensure mid`] >- metis_tac[compile_type_abi_encode_not_stack]
  >~ [`AbiDecode unwrap`] >- metis_tac[compile_type_abi_decode_not_stack] >>
  Cases_on `args` >>
  gvs[is_word_type_def]
  >>~- ([`supported_numeric_type ann`], metis_tac[supported_numeric_is_word]) >>
  Cases_on `t` >> gvs[]
QED

Theorem supported_builtin_stack_word:
  supported_builtin_form tops ann bi args /\
  well_typed_builtin_app ann bi (MAP expr_type args) /\
  compile_builtin_dispatch_body f ce ann ty bi args sa =
    (StackValue vt op,sb) ==> is_word_type ann
Proof
  strip_tac >> Cases_on `bi` >>
  gvs[well_typed_builtin_app_def, is_word_type_def] >>
  gvs[supported_builtin_form_def, AllCaseEqs()]
  >~ [`MakeArray opt bd`] >-
    (Cases_on `opt` >> gvs[well_typed_builtin_app_def] >>
     gvs[compile_builtin_dispatch_body_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> gvs[as_ptr_val_not_stack])
  >~ [`Env item`] >-
    (Cases_on `item` >> gvs[env_item_type_def, is_word_type_def])
  >~ [`Acc item`] >-
    (Cases_on `item` >> gvs[account_item_type_def, is_word_type_def] >>
     Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[])
  >~ [`Bop bop`] >-
    (Cases_on `bop` >> gvs[well_typed_binop_def, is_word_type_def] >>
     rename1 `is_word_type rt` >> Cases_on `rt` >>
     gvs[is_word_type_def, is_int_type_def, is_bool_type_def, is_flag_type_def] >>
     rename1 `BaseT b` >> Cases_on `b` >>
     gvs[is_word_type_def, is_int_type_def, is_bool_type_def, is_flag_type_def])
  >>~- ([`is_word_type ann`],
    rename1 `is_word_type rt` >> Cases_on `rt` >> gvs[is_word_type_def, is_bool_type_def,
      is_uint256_type_def, is_bytes32_type_def, is_flag_type_def, is_int_type_def] >>
    rename1 `BaseT b` >> Cases_on `b` >>
    gvs[is_word_type_def, is_bool_type_def, is_uint256_type_def,
        is_bytes32_type_def, is_flag_type_def, is_int_type_def] >>
    rename1 `BytesT bd` >> Cases_on `bd` >>
    gvs[is_word_type_def, is_bytes32_type_def]) >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[as_ptr_val_not_stack]
QED

Theorem compile_external_stack_void:
  args <> [] /\
  compile_call f ce ann ty (ExtCall static skip (name,ats,rt) opts) args drv sa =
    (StackValue vt op,sb) ==> rt = NoneT
Proof
  Cases_on `args` >> simp[compile_call_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> gvs[]
QED
