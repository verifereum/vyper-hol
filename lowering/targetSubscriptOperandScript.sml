Theory targetSubscriptOperand
Ancestors
  exprSafeOperand exprSafeOperandBuiltins exprWordOperand exprOperandVar
  exprLowering compileEnv context vyperTypeSystem vyperAST

(* Callback projection: unwrap_value preserves exclusion of labels. *)
Theorem target_subscript_lower_callback_not_label:
  (!s vv s'. f cenv ty e s = (vv,s') ==>
      !l. vv_operand vv <> Label l) /\
  lower_value f cenv ty e sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  irule unwrap_value_not_label >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem target_subscript_stack_result_not_label[local]:
  as_stack_val ty res = (vv,sb) /\ word_result_ok sb vv ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `res` >> simp[as_stack_val_def] >> strip_tac >>
  gvs[word_result_ok_def, vv_operand_def, safe_operand_def]
QED

Theorem target_subscript_scalar_builtin_not_label[local]:
  (bi = Not \/ bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
   bi = Ceil \/ bi = Floor \/ bi = AddMod \/ bi = MulMod \/ bi = PowMod256 \/
   bi = ECRecover \/ bi = CalldataLen \/ (?item. bi = Env item)) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_scalar] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[target_subscript_stack_result_not_label]
QED

Theorem target_subscript_hash_builtin_not_label[local]:
  (bi = Keccak256 \/ bi = Sha256) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> `word_result_ok sb vv` by metis_tac[word_builtin_hash] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[target_subscript_stack_result_not_label]
QED

Theorem target_subscript_len_builtin_not_label[local]:
  compile_builtin_dispatch_body f cenv vt ty Len args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> `word_result_ok sb vv` by metis_tac[word_builtin_len] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[target_subscript_stack_result_not_label]
QED

Theorem target_subscript_bop_builtin_not_label[local]:
  compile_builtin_dispatch_body f cenv vt ty (Bop bop) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> `word_result_ok sb vv` by metis_tac[word_builtin_bop] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  metis_tac[target_subscript_stack_result_not_label]
QED

Theorem target_subscript_slice_out_not_label[local]:
  compile_slice_out_buf sz sa = ((buf,data),sb) ==> !l. buf <> Label l
Proof
  simp[builtinBytesTheory.compile_slice_out_buf_def, comp_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem target_subscript_slice_data_not_label[local]:
  compile_slice_data len data start lenop sz sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinBytesTheory.compile_slice_data_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem target_subscript_slice_not_label[local]:
  (!start lenop sz sa op sb.
    compile_slice_calldata start lenop sz sa = (op,sb) ==> !l. op <> Label l) /\
  (!start lenop sz sa op sb.
    compile_slice_code start lenop sz sa = (op,sb) ==> !l. op <> Label l) /\
  (!addr start lenop buf data sa op sb.
    (!l. buf <> Label l) /\
    compile_slice_extcode addr start lenop buf data sa = (op,sb) ==>
    !l. op <> Label l)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[builtinBytesTheory.compile_slice_calldata_def,
       builtinBytesTheory.compile_slice_code_def,
       builtinBytesTheory.compile_slice_extcode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[target_subscript_slice_out_not_label]
QED

Theorem target_subscript_uint2str_not_label[local]:
  compile_uint2str v digits sz sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinStringsTheory.compile_uint2str_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem target_subscript_fresh_builtin_not_label[local]:
  ((?n. bi = CalldataSlice n) \/ bi = ECAdd \/ bi = ECMul \/
   (?n. bi = Concat n) \/ (?n. bi = Slice n) \/ (?n. bi = Uint2Str n)) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
  >~ [`LocatedValue _ (base_ptr _)`] >-
    (gvs[vv_operand_def, base_ptr_def] >>
     metis_tac[alloc_buffer_not_label]) >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
  Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[target_subscript_slice_not_label,
            target_subscript_slice_out_not_label,
            target_subscript_slice_data_not_label,
            ec_arith_result_not_label, target_subscript_uint2str_not_label]
QED

Theorem target_subscript_makearray_not_label[local]:
  compile_builtin_dispatch_body f cenv vt ty (MakeArray et bd) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `et` >> simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
  Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[compiler_make_tuple_result, compiler_make_array_result,
            alloc_buffer_not_label]
QED

Theorem target_subscript_acc_not_label[local]:
  (!sa op sb. lower_value f cenv (BaseT AddressT) e sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_acc f cenv e item sa = (op,sb) ==> !l. op <> Label l
Proof
  Cases_on `item` >> simp[compile_acc_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_op_safe_operand, safe_operand_def]
QED

Theorem target_subscript_wei_not_label[local]:
  (!v scale signed sa op sb. (!l. v <> Label l) /\
    compile_as_wei_value_int v scale signed sa = (op,sb) ==> !l. op <> Label l) /\
  (!v scale divisor sa op sb.
    compile_as_wei_value_decimal v scale divisor sa = (op,sb) ==> !l. op <> Label l)
Proof
  conj_tac >> rpt gen_tac >>
  simp[builtinMiscTheory.compile_as_wei_value_int_def,
       builtinMiscTheory.compile_as_wei_value_decimal_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_op_safe_operand, safe_operand_def]
QED

Theorem target_subscript_acc_builtin_not_label[local]:
  (!sa op sb. lower_value f cenv (BaseT AddressT) (HD args) sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_builtin_dispatch_body f cenv vt ty (Acc item) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >>
  metis_tac[target_subscript_acc_not_label]
QED

Theorem target_subscript_wei_builtin_not_label[local]:
  (!sa op sb. lower_value f cenv (expr_type (HD args)) (HD args) sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_builtin_dispatch_body f cenv vt ty (AsWeiValue denom) args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >>
  metis_tac[target_subscript_wei_not_label]
QED

Theorem target_subscript_bytelike_not_label[local]:
  compile_bytelike_literal bs maxlen sa = (buf,sb) ==>
  !l. buf.buf_operand <> Label l
Proof
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem target_subscript_literal_not_label:
  compile_literal_vv t lit sa = (vv,sb) ==> !l. vv_operand vv <> Label l
Proof
  Cases_on `lit`
  >- (Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def] >>
      rpt strip_tac >> gvs[vv_operand_def]) >>
  simp[compile_literal_vv_def, comp_return_def, comp_bind_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[vv_operand_def, base_ptr_def]
  >~ [`compile_bytelike_literal _ _ _ = _`] >-
    (drule (GEN_ALL target_subscript_bytelike_not_label) >> simp[]) >>
  Cases_on `t` >> gvs[comp_return_def, comp_bind_def, vv_operand_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[comp_return_def, comp_bind_def, vv_operand_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[comp_return_def, comp_bind_def, vv_operand_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def, base_ptr_def] >>
  metis_tac[target_subscript_bytelike_not_label]
QED

Theorem target_subscript_method_not_label[local]:
  compile_method_id_runtime ty v flag sa = (op,sb) ==> !l. op <> Label l
Proof
  Cases_on `flag`
  >- metis_tac[compile_method_id_word_safe_operand, safe_operand_def] >>
  simp[builtinHashingTheory.compile_method_id_runtime_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem target_subscript_method_builtin_not_label[local]:
  compile_builtin_dispatch_body f cenv vt ty MethodId args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[target_subscript_literal_not_label]
  >~ [`as_ptr_val _ _ _ = _`] >-
    (qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
     Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
     strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
     metis_tac[target_subscript_method_not_label]) >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >> metis_tac[target_subscript_method_not_label]
QED

Theorem target_subscript_builtin_body_not_label:
  compile_builtin_dispatch_body f cenv ann ty bi args sa = (vv,sb) /\
  well_typed_expr env (Builtin ann bi args) /\
  (!t e s op s'. MEM e args /\ lower_value f cenv t e s = (op,s') ==>
      !l. op <> Label l) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `bi` >> strip_tac
  >~ [`Bop bop`] >- metis_tac[target_subscript_bop_builtin_not_label]
  >~ [`Len`] >- metis_tac[target_subscript_len_builtin_not_label]
  >~ [`MakeArray et bd`] >- metis_tac[target_subscript_makearray_not_label]
  >~ [`MethodId`] >- metis_tac[target_subscript_method_builtin_not_label]
  >~ [`Acc item`] >-
    (irule target_subscript_acc_builtin_not_label >> goal_assum (drule_at Any) >>
     Cases_on `args` >> gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
     metis_tac[])
  >~ [`AsWeiValue denom`] >-
    (irule target_subscript_wei_builtin_not_label >> goal_assum (drule_at Any) >>
     Cases_on `args` >> gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
     metis_tac[]) >>
  metis_tac[target_subscript_scalar_builtin_not_label,
            target_subscript_hash_builtin_not_label,
            target_subscript_fresh_builtin_not_label]
QED

Theorem target_subscript_convert_not_label[local]:
  (!l. v <> Label l) /\ compile_type_convert v conv sa = (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `conv`
  >~ [`compile_type_convert v ConvBytestringToBool`] >-
    metis_tac[compile_type_convert_bytestring_safe, listTheory.MEM, safe_operand_def]
  >~ [`compile_type_convert v (ConvBytestringToInt s n in_n)`] >-
    metis_tac[compile_type_convert_bytestring_safe, listTheory.MEM, safe_operand_def]
  >~ [`compile_type_convert v (ConvBytestringToDecimal d lo hi in_n)`] >-
    metis_tac[compile_type_convert_bytestring_safe, listTheory.MEM, safe_operand_def]
  >~ [`compile_type_convert v (ConvBytestringToBytesM m)`] >-
    metis_tac[compile_type_convert_bytestring_safe, listTheory.MEM, safe_operand_def] >>
  simp[compile_type_convert_def, compile_int_clamp_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def,
                           comp_return_def, LET_THM]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
       IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
       rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_safe_operand >> fs[safe_operand_def] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem target_subscript_widen_not_label[local]:
  compile_bytestring_widen_copy d v sz sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[compile_bytestring_widen_copy_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem target_subscript_convert_body_not_label[local]:
  (!sa op sb. lower_value f cenv (expr_type (HD args)) (HD args) sa = (op,sb)
               ==> !l. op <> Label l) /\
  compile_type_builtin_dispatch_body f cenv vt ty Convert rt args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `COND _ _ _ = _` mp_tac >> IF_CASES_TAC
  >- (strip_tac >> gvs[vv_operand_def]) >>
  pop_assum kall_tac >> IF_CASES_TAC
  >- (pop_assum kall_tac >> strip_tac >>
      qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
      qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
      Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
      strip_tac >> gvs[vv_operand_def] >>
      metis_tac[target_subscript_widen_not_label]) >>
  pop_assum kall_tac >> strip_tac >> Cases_on `rt` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >> strip_tac >>
  gvs[vv_operand_def] >> first_x_assum drule >> strip_tac >>
  metis_tac[target_subscript_convert_not_label]
QED

Theorem target_subscript_abi_encode_not_label[local]:
  lower_abi_encode ensure mid src info maxlen sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinAbiTheory.lower_abi_encode_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem target_subscript_type_nonconvert_not_label[local]:
  tb <> Convert /\
  type_builtin_result_ok tenv tb vt rt (MAP expr_type args) /\
  compile_type_builtin_dispatch_body f cenv vt ty tb rt args sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `tb` >>
  simp[type_builtin_result_ok_def, compile_type_builtin_dispatch_body_def,
       LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> simp[vv_operand_def]
  >~ [`if is_word_type _ then _ else _`] >-
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[vv_operand_def, base_ptr_def] >>
     metis_tac[compile_empty_not_label])
  >~ [`as_stack_val _ _ = _`] >-
    (qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
     Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
     strip_tac >> gvs[vv_operand_def] >>
     drule compile_extract32_load_safe_operand >> strip_tac >>
     metis_tac[compile_clamp_basetype_safe_operand, safe_operand_def]) >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
  Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[target_subscript_abi_encode_not_label, lower_abi_decode_not_label]
QED

Theorem target_subscript_type_builtin_body_not_label:
  compile_type_builtin_dispatch_body f cenv ann ty tb rt args sa = (vv,sb) /\
  well_typed_expr env (TypeBuiltin ann tb rt args) /\
  (!t e s op s'. MEM e args /\ lower_value f cenv t e s = (op,s') ==>
      !l. op <> Label l) ==>
  !l. vv_operand vv <> Label l
Proof
  Cases_on `tb = Convert`
  >- (strip_tac >> gvs[] >> irule target_subscript_convert_body_not_label >>
      goal_assum (drule_at Any) >> Cases_on `args` >>
      gvs[well_typed_expr_def, well_typed_type_builtin_args_def,
          type_builtin_result_ok_def] >> metis_tac[]) >>
  strip_tac >> irule target_subscript_type_nonconvert_not_label >>
  goal_assum (drule_at Any) >>
  gvs[well_typed_expr_def] >> metis_tac[]
QED
