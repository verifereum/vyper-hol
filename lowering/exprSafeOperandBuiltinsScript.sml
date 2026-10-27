(*
 * The safe operands of the lowering's builtins, calls and names (#636)
 *
 * safe_operand (exprSafeOperand) of each builtin helper's result, and
 * word_result_ok of the value compile_call, compile_attribute,
 * compile_subscript, compile_name_vv and compile_literal_vv hand out at a
 * word type.
 *
 * TOP-LEVEL: one *_safe_operand or *_word_result_ok lemma per helper.
 *)

Theory exprSafeOperandBuiltins
Ancestors
  exprSafeOperand
  exprLoweringProps freshWrites compileEnv emitHelper context
  exprLowering exprCallBounds vyperTypeSystem vyperValue vyperAST vyperTypeBuiltins
  builtinSimple builtinMath builtinHashing builtinMisc builtinBytes builtinSystem

(* ===== Builtins ===== *)

Theorem compile_builtin_abs_safe_operand:
  compile_builtin_abs v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_builtin_abs_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_select_safe_operand]
QED

Theorem compile_builtin_len_safe_operand:
  compile_builtin_len ctor imm ptr_op loc sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_builtin_len_def] >> metis_tac[compile_ptr_load_safe_operand]
QED

Theorem compile_acc_safe_operand:
  (acc = Address ==>
     !s r s'. lower_value cfn cenv (BaseT AddressT) e s = (r,s') ==>
                safe_operand s' r) /\
  compile_acc cfn cenv e acc sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `acc` >>
  simp[compile_acc_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_op_safe_operand, safe_operand_Lit]
QED

Theorem compile_env_var_safe_operand:
  compile_env_var item sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `item` >> simp[compile_env_var_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_keccak256_word_safe_operand:
  compile_keccak256_word v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_keccak256_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_keccak256_bytes_safe_operand:
  compile_keccak256_bytes v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_keccak256_bytes_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_keccak256_bytesm_safe_operand:
  compile_keccak256_bytesm v m sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_keccak256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_sha256_word_safe_operand:
  compile_sha256_word v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_sha256_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_sha256_bytes_safe_operand:
  compile_sha256_bytes v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_sha256_bytes_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_sha256_bytesm_safe_operand:
  compile_sha256_bytesm v m sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_sha256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_ecrecover_safe_operand:
  compile_ecrecover h v r s sa = (op,sb) ==> safe_operand sb op
Proof
  simp[compile_ecrecover_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_blockhash_safe_operand:
  compile_blockhash v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_blockhash_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_blobhash_safe_operand:
  compile_blobhash v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_blobhash_def] >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_floor_safe_operand:
  compile_floor v d sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_floor_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_ceil_safe_operand:
  compile_ceil v d sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_ceil_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_as_wei_value_int_safe_operand:
  safe_operand sa v /\ compile_as_wei_value_int v scale signed sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  gvs[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compile_extract32_safe_operand:
  compile_extract32 p v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_extract32_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_clamp_extract32_safe_operand:
  safe_operand sa v /\ compile_clamp_extract32 v clamp sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `clamp` >>
  simp[compile_clamp_extract32_def, LET_THM, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  gvs[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compile_method_id_word_safe_operand:
  compile_method_id_runtime ty v T sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_method_id_runtime_def, comp_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_list_membership_in_safe_operand:
  compile_list_membership_in needle xs sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `xs` >- simp[compile_list_membership_in_def, comp_return_def] >>
  rename1 `_ :: rest` >> Cases_on `rest` >>
  simp[compile_list_membership_in_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_list_membership_notin_safe_operand:
  compile_list_membership_notin needle xs sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `xs` >- simp[compile_list_membership_notin_def, comp_return_def] >>
  rename1 `_ :: rest` >> Cases_on `rest` >>
  simp[compile_list_membership_notin_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_ptr_load_next_var:
  compile_ptr_load ctor imm loc p sa = (v,sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `ctor` >> Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem compile_array_membership_loop_safe_operand:
  (!p s v t. loader p s = (v,t) ==> s.cs_next_var <= t.cs_next_var) /\
  compile_array_membership_loop needle arr len sz off loader isin sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `isin` >> Cases_on `off > 0` >>
  simp[compile_array_membership_loop_def, emit_op_def, emit_inst_def,
       fresh_label_def, new_block_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `!p s v t. _` drule_all >>
  simp[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compile_var_array_membership_safe_operand:
  compile_var_array_membership cenv needle vv ty isin sa = (r,sb) ==>
  safe_operand sb r
Proof
  simp[compile_var_array_membership_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_array_membership_loop_safe_operand, compile_ptr_load_next_var]
QED

(* ===== Calls, names, subscripts and literals ===== *)

Theorem as_stack_val_word_result_ok:
  (!r sb. result = (r,sb) ==> safe_operand sb r) /\
  as_stack_val ty result = (vv,sb) ==> word_result_ok sb vv
Proof
  Cases_on `result` >> simp[as_stack_val_def] >>
  strip_tac >> gvs[word_result_ok_def]
QED

Theorem compile_raw_call_zero_safe_operand:
  compile_raw_call addr p len gas value ct 0 rof sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `ct` >> Cases_on `rof` >>
  simp[compile_raw_call_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_label_def, new_block_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compile_external_call_zero_safe_operand:
  compile_external_call_kwargs cenv addr vals tys memsz abisz mid 0 minsz retsz
    static value gas skip default dop rt dt einfo dinfo sa = (r,sb) ==>
  safe_operand sb r
Proof
  simp[compile_external_call_kwargs_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem compile_call_word_result_ok:
  is_word_type rt /\ compile_call cfn cenv rt ty target args default_ret sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `target` >>
  simp[compile_call_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[word_result_ok_def]
  >~ [`cenv.ce_func_info name = info`] >- suspend "internal"
  >~ [`compile_call cfn cenv rt ty (ExtCall b b0 p l) args default_ret sa = _`]
    >- suspend "external"
  >~ [`r.rcf_max_outsize`] >- suspend "raw"
  >> suspend "send"
QED

Resume compile_call_word_result_ok[internal]:
  Cases_on `returns_count > 0` >> Cases_on `return_buf` >>
  gvs[word_result_ok_def] >> rpt (pairarg_tac >> gvs[word_result_ok_def]) >>
  metis_tac[emit_op_safe_operand]
QED

Resume compile_call_word_result_ok[external]:
  PairCases_on `p` >> Cases_on `args` >>
  gvs[compile_call_def, LET_THM, word_result_ok_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[word_result_ok_def] >>
  qpat_x_assum `(if _ then _ else _) = (vv,sb)` mp_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[word_result_ok_def] >>
  metis_tac[compile_external_call_zero_safe_operand]
QED

Resume compile_call_word_result_ok[raw]:
  Cases_on `args` >> gvs[word_result_ok_def] >> rename1 `list_CASE args1 _ _` >>
  Cases_on `args1` >> gvs[word_result_ok_def] >> rename1 `list_CASE args2 _ _` >>
  Cases_on `args2` >> gvs[word_result_ok_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `r.rcf_max_outsize = 0` >> gvs[word_result_ok_def] >>
  metis_tac[compile_raw_call_zero_safe_operand]
QED

Resume compile_call_word_result_ok[send]:
  Cases_on `args` >> gvs[word_result_ok_def] >> rename1 `list_CASE args1 _ _` >>
  Cases_on `args1` >> gvs[word_result_ok_def] >>
  rename1 `LENGTH args2 = if flag then 1 else 0` >>
  Cases_on `LENGTH args2 = if flag then 1 else 0` >> gvs[word_result_ok_def] >>
  rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Finalise compile_call_word_result_ok

Theorem as_ptr_val_word_result_ok:
  is_word_type ty /\ as_ptr_val ty loc result = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `result` >> simp[as_ptr_val_def, word_result_ok_def] >>
  strip_tac >> gvs[word_result_ok_def]
QED

Theorem compile_attribute_word_result_ok:
  is_word_type rt /\ compile_attribute cfn cenv rt ty e fld sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_attribute_def, LET_THM, comp_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Theorem compile_subscript_word_result_ok:
  is_word_type rt /\ compile_subscript cfn cenv rt ty e idx sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_subscript_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `cenv.ce_is_hashmap name` >>
  Cases_on `cenv.ce_is_hashmap name` >>
  simp[comp_bind_def, comp_return_def] >-
    (strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  Cases_on `cenv.ce_var_type name` >> simp[comp_bind_def, comp_return_def] >-
    (strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  rename1 `cenv.ce_var_type name = SOME vt` >> Cases_on `vt` >> simp[comp_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Theorem compile_builtin_calldatasize_safe_operand:
  compile_builtin_calldatasize sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_builtin_calldatasize_def] >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_name_vv_word_result_ok:
  is_word_type ty /\ compile_name_vv cenv ty id sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `FLOOKUP cenv.ce_vars id` >>
  simp[compile_name_vv_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >-
    (strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  rename1 `FLOOKUP cenv.ce_vars id = SOME bnd` >> Cases_on `bnd` >>
  simp[compile_name_vv_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def]) >>
  gvs[word_result_ok_def]
QED

Theorem compile_literal_vv_word_result_ok:
  is_word_type ty /\ compile_literal_vv ty lit sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def, comp_return_def] >>
  rpt strip_tac
  >~ [`BoolL b`] >-
    (Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def, word_result_ok_def])
  >~ [`BytesV bs`] >-
    (Cases_on `ty` >> gvs[compile_literal_vv_def, comp_bind_def,
                          comp_return_def, word_result_ok_def] >>
     Cases_on `b` >> gvs[compile_literal_vv_def, comp_bind_def,
                         comp_return_def, word_result_ok_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[compile_literal_vv_def, comp_bind_def,
                         comp_return_def, word_result_ok_def] >>
     rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  gvs[word_result_ok_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[word_result_ok_def])
QED
