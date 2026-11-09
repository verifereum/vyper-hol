Theory abiArgsCompilerImage
Ancestors
  exprLowering context compileEnv emitHelper vyperAST exprWordOperand exprSafeOperand exprOperandVar exprSafeOperandBuiltins exprCallBounds fragExec

Theorem abi_image_convert_label:
  compile_type_convert op conv sa = (Label l,sb) ==>
  op = Label l /\ sb.cs_blocks = sa.cs_blocks
Proof
  Cases_on `conv` >>
  simp[compile_type_convert_def, compile_int_clamp_def,
       load_bytestring_as_word_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt (IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_image_alloc_not_label:
  compile_alloc_buffer n sa = (buf,sb) ==> buf.buf_operand <> Label l
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_image_ensure_label:
  compile_ensure_in_memory op loc bytes wc ctor imm sa = (Label l,sb) ==>
  op = Label l /\ sb = sa
Proof
  Cases_on `loc` >>
  simp[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_load_not_label:
  compile_ptr_load ctor imm loc op sa = (v,sb) ==> v <> Label l
Proof
  Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, emit_op_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_image_unwrap_label:
  unwrap_value ce vv sa = (Label l,sb) ==>
  vv_operand vv = Label l /\ sb = sa
Proof
  Cases_on `vv` >> simp[unwrap_value_def, comp_return_def, vv_operand_def] >>
  Cases_on `is_word_type t` >> simp[]
  >- metis_tac[abi_image_load_not_label] >>
  Cases_on `p.ptr_location` >> simp[comp_return_def] >>
  metis_tac[abi_image_ensure_label]
QED

Theorem abi_image_emit_not_label:
  emit_op opc args sa = (op,sb) ==> op <> Label l
Proof
  simp[emit_op_def, comp_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_image_projection_not_label:
  (compile_mapping_subscript bop key sa = (op,sb) ==> op <> Label l) /\
  (compile_tuple_subscript bop off sa = (op,sb) ==> op <> Label l) /\
  (compile_array_subscript bop idx dyn sc ws es signed load sa = (op,sb) ==>
   op <> Label l)
Proof
  rpt conj_tac >>
  simp[compile_mapping_subscript_def, compile_tuple_subscript_def,
       compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  metis_tac[abi_image_emit_not_label]
QED

Theorem abi_image_attribute_not_label:
  compile_attribute f ce rt ty base_e fld sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vv_operand_def, mk_ptr_def] >> metis_tac[abi_image_emit_not_label]
QED

Theorem abi_image_subscript_not_label:
  compile_subscript f ce rt ty base_e idx sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `place_type ce base_e`
  >- (gvs[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def, mk_ptr_def] >>
      metis_tac[abi_image_projection_not_label]) >>
  rename1 `ValPT bt` >> Cases_on `bt` >>
  gvs[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[abi_image_projection_not_label]
QED

Theorem abi_image_bytelike_not_label:
  compile_bytelike_literal bs maxlen sa = (buf,sb) ==>
  buf.buf_operand <> Label l
Proof
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_literal_not_label:
  compile_literal_vv t lit sa = (vv,sb) ==> vv_operand vv <> Label l
Proof
  Cases_on `lit`
  >- (Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def] >>
      rpt strip_tac >> gvs[vv_operand_def]) >>
  simp[compile_literal_vv_def, comp_return_def, comp_bind_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[vv_operand_def, base_ptr_def]
  >~ [`compile_bytelike_literal _ _ _ = _`] >-
    metis_tac[abi_image_bytelike_not_label] >>
  Cases_on `t` >> gvs[comp_return_def, comp_bind_def, vv_operand_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[comp_return_def, comp_bind_def, vv_operand_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[comp_return_def, comp_bind_def, vv_operand_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def, base_ptr_def] >>
  metis_tac[abi_image_bytelike_not_label]
QED

Theorem abi_image_struct_not_label:
  compile_expr_body f g h ce ty (StructLit t nm fields) sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vv_operand_def, base_ptr_def] >> metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_ifexp_not_label:
  compile_expr_body f g h ce ty (IfExp t cond_e then_e else_e) sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[AllCaseEqs(), vv_operand_def, mk_ptr_def]
QED

Theorem abi_image_toplevel_not_label:
  compile_expr_body f g h ce ty (TopLevelName t nsid) sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >>
  simp[compile_expr_body_def, expr_type_def]
  >- (rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[vv_operand_def]) >>
  rename1 `SOME bnd` >> Cases_on `bnd` >>
  simp[] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vv_operand_def, mk_ptr_def]
QED

Theorem abi_image_name_label:
  compile_name_vv ce t id sa = (vv,sb) /\ vv_operand vv = Label l ==>
  sb = sa
Proof
  simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >- (rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[vv_operand_def]) >>
  rename1 `SOME bnd` >> Cases_on `bnd` >>
  simp[comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[vv_operand_def, mk_ptr_def]
QED

Theorem abi_image_default_return_not_label:
  result <> Label l /\
  compile_default_return_path ce rt dt buf result def addr skip mn mx info sa = (op,sb) ==>
  op <> Label l
Proof
  simp[compile_default_return_path_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_image_external_call_not_label:
  compile_external_call_kwargs ce addr vals tys memsz abisz mid retsz mn outsz
    static value gas skip hasdef def rt dt einfo dinfo sa = (op,sb) ==>
  op <> Label l
Proof
  simp[compile_external_call_kwargs_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `rt = NoneT` >- simp[comp_return_def] >>
  simp[] >> Cases_on `hasdef` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_default_return_not_label, abi_image_alloc_not_label]
QED

Theorem abi_image_raw_outbuf_not_label:
  compile_raw_call_outbuf mx sa = ((out_val,out_ptr),sb) ==>
  out_val <> Label l
Proof
  simp[builtinSystemTheory.compile_raw_call_outbuf_def, LET_THM, comp_bind_def,
       comp_return_def] >>
  IF_CASES_TAC >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_raw_finish_not_label:
  out_val <> Label l /\
  compile_raw_call_finish addr data len gas value ct mx rof out_val out_ptr sa = (op,sb) ==>
  op <> Label l
Proof
  Cases_on `ct` >> Cases_on `rof` >> Cases_on `mx > 0` >>
  simp[builtinSystemTheory.compile_raw_call_finish_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label, abi_image_emit_not_label]
QED

Theorem abi_image_call_not_label:
  compile_call f ce rt ty target args default_ret sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  Cases_on `target`
  >~ [`RawCallTarget`] >- suspend "raw"
  >~ [`RawCallCalldataTarget`] >- suspend "rawdata"
  >~ [`CreateTarget _ _ _ _`] >- suspend "create" >>
  simp[compile_call_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def]
  >~ [`ce.ce_func_info name = info`] >- suspend "internal"
  >~ [`compile_call f ce rt ty (ExtCall b b0 p l') args default_ret sa = _`]
    >- suspend "external" >>
  BasicProvers.every_case_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def]
QED

Resume abi_image_call_not_label[create]:
  simp[compile_call_def] >>
  Cases_on `compile_create_call f ce c b b0 args sa` >>
  simp[as_stack_val_def] >> strip_tac >> gvs[vv_operand_def] >>
  drule compile_create_call_safe_operand >> simp[safe_operand_def]
QED

Resume abi_image_call_not_label[raw]:
  Cases_on `args`
  >- (simp[compile_call_def, LET_THM] >> strip_tac >>
      rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def]) >>
  Cases_on `t` >> simp[compile_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), vv_operand_def, mk_ptr_def] >>
  metis_tac[abi_image_raw_finish_not_label, abi_image_raw_outbuf_not_label]
QED

Resume abi_image_call_not_label[rawdata]:
  Cases_on `args`
  >- (simp[compile_call_def, LET_THM] >> strip_tac >>
      rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def]) >>
  Cases_on `t` >> simp[compile_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), vv_operand_def, mk_ptr_def] >>
  metis_tac[abi_image_raw_finish_not_label, abi_image_raw_outbuf_not_label]
QED

Resume abi_image_call_not_label[internal]:
  Cases_on `returns_count > 0` >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[vv_operand_def, base_ptr_def] >>
  metis_tac[abi_image_alloc_not_label, abi_image_emit_not_label]
QED

Resume abi_image_call_not_label[external]:
  PairCases_on `p` >> Cases_on `args` >>
  gvs[compile_call_def, LET_THM, vv_operand_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), vv_operand_def, mk_ptr_def] >>
  metis_tac[abi_image_external_call_not_label]
QED

Finalise abi_image_call_not_label

Theorem abi_image_named_modular_not_label:
  (!ce rt at a bt b mt m sa vv sb.
    compile_addmod_names ce rt at a bt b mt m sa = (vv,sb) ==>
    vv_operand vv <> Label l) /\
  (!ce rt at a bt b mt m sa vv sb.
    compile_mulmod_names ce rt at a bt b mt m sa = (vv,sb) ==>
    vv_operand vv <> Label l) /\
  (!ce rt at a bt b sa vv sb.
    compile_powmod256_names ce rt at a bt b sa = (vv,sb) ==>
    vv_operand vv <> Label l)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_addmod_names_def, compile_mulmod_names_def,
       compile_powmod256_names_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[builtinMathTheory.compile_addmod_def, builtinMathTheory.compile_mulmod_def,
       builtinMathTheory.compile_pow_mod256_def, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `as_stack_val rt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >>
  metis_tac[abi_image_emit_not_label]
QED

Theorem abi_image_pop_operand_not_label:
  compile_dynarray_pop bop ws es is_ctor imm loc sa = (op,sb) ==> op <> Label l
Proof
  simp[compile_dynarray_pop_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  metis_tac[abi_image_emit_not_label]
QED

Theorem abi_image_pop_not_label:
  compile_expr_body f g h ce ty (Pop t target) sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[vv_operand_def, mk_ptr_def] >> metis_tac[abi_image_pop_operand_not_label]
QED

Theorem abi_image_flag_not_label:
  compile_expr_body f g h ce ty (FlagMember t nsid mem_id) sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  simp[compile_expr_body_def, comp_return_def, vv_operand_def] >>
  rpt strip_tac >> gvs[vv_operand_def]
QED

Theorem abi_image_acc_label:
  compile_acc f ce e item sa = (Label l,sb) ==>
  item = Address /\ lower_value f ce (BaseT AddressT) e sa = (Label l,sb)
Proof
  Cases_on `item` >> simp[compile_acc_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_emit_not_label]
QED

Theorem abi_image_wei_int_label:
  compile_as_wei_value_int v scale signed sa = (Label l,sb) ==>
  v = Label l /\ sb = sa /\ scale = 1
Proof
  simp[builtinMiscTheory.compile_as_wei_value_int_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_emit_not_label]
QED

Theorem abi_image_wei_decimal_not_label:
  compile_as_wei_value_decimal v scale divisor sa = (op,sb) ==> op <> Label l
Proof
  Cases_on `scale = 1` >>
  simp[builtinMiscTheory.compile_as_wei_value_decimal_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_emit_not_label]
QED

Theorem abi_image_abi_encode_not_label:
  lower_abi_encode ensure mid src info maxlen sa = (op,sb) ==> op <> Label l
Proof
  simp[builtinAbiTheory.lower_abi_encode_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_abi_decode_not_label:
  lower_abi_decode data info mn mx sz sa = (op,sb) ==> op <> Label l
Proof
  simp[builtinAbiTheory.lower_abi_decode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_stack_not_label:
  as_stack_val t res = (vv,sb) /\ word_result_ok sb vv ==>
  vv_operand vv <> Label l
Proof
  Cases_on `res` >> simp[as_stack_val_def] >> strip_tac >>
  gvs[word_result_ok_def, vv_operand_def, safe_operand_def]
QED

Theorem abi_image_builtin_scalar_not_label:
  (bi = Not \/ bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
   bi = Ceil \/ bi = Floor \/ bi = AddMod \/ bi = MulMod \/ bi = PowMod256 \/
   bi = ECRecover \/ bi = CalldataLen \/ (?item. bi = Env item)) /\
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_scalar] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[abi_image_stack_not_label]
QED

Theorem abi_image_builtin_hash_not_label:
  (bi = Keccak256 \/ bi = Sha256) /\
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_hash] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs(), as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[abi_image_stack_not_label]
QED

Theorem abi_image_builtin_len_not_label:
  compile_builtin_dispatch_body f ce vt ty Len args sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_len] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[abi_image_stack_not_label]
QED

Theorem abi_image_builtin_bop_not_label:
  compile_builtin_dispatch_body f ce vt ty (Bop bop) args sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_bop] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  metis_tac[abi_image_stack_not_label]
QED

Theorem abi_image_slice_out_not_label:
  compile_slice_out_buf sz sa = ((buf,data),sb) ==> buf <> Label l
Proof
  simp[builtinBytesTheory.compile_slice_out_buf_def, comp_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_slice_data_not_label:
  compile_slice_data len data start lenop sz sa = (op,sb) ==> op <> Label l
Proof
  simp[builtinBytesTheory.compile_slice_data_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_slice_adhoc_not_label:
  (!start lenop sz sa op sb.
    compile_slice_calldata start lenop sz sa = (op,sb) ==> op <> Label l) /\
  (!start lenop sz sa op sb.
    compile_slice_code start lenop sz sa = (op,sb) ==> op <> Label l) /\
  (!addr start lenop buf data sa op sb.
    buf <> Label l /\ compile_slice_extcode addr start lenop buf data sa = (op,sb) ==>
    op <> Label l)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[builtinBytesTheory.compile_slice_calldata_def,
       builtinBytesTheory.compile_slice_code_def,
       builtinBytesTheory.compile_slice_extcode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[abi_image_slice_out_not_label]
QED

Theorem abi_image_ec_not_label:
  (!p q sa op sb. compile_ecadd_points p q sa = (op,sb) ==> op <> Label l) /\
  (!p scalar sa op sb. compile_ecmul_point p scalar sa = (op,sb) ==> op <> Label l)
Proof
  conj_tac >> rpt gen_tac >>
  simp[builtinMiscTheory.compile_ecadd_points_def,
       builtinMiscTheory.compile_ecmul_point_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_uint2str_not_label:
  compile_uint2str v digits sz sa = (op,sb) ==> op <> Label l
Proof
  simp[builtinStringsTheory.compile_uint2str_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_image_builtin_fresh_not_label:
  ((?n. bi = CalldataSlice n) \/ bi = ECAdd \/ bi = ECMul \/
   (?n. bi = Concat n) \/ (?n. bi = Slice n) \/ (?n. bi = Uint2Str n)) /\
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
  >~ [`LocatedValue _ (base_ptr _)`] >-
    (gvs[vv_operand_def, base_ptr_def] >> metis_tac[abi_image_alloc_not_label]) >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
  Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[abi_image_slice_adhoc_not_label, abi_image_slice_out_not_label,
            abi_image_slice_data_not_label, abi_image_ec_not_label,
            abi_image_uint2str_not_label]
QED

Theorem abi_image_builtin_makearray_not_label:
  compile_builtin_dispatch_body f ce vt ty (MakeArray et bd) args sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  Cases_on `et` >> simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
  Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
  metis_tac[compiler_make_tuple_result, compiler_make_array_result,
            abi_image_alloc_not_label]
QED

Theorem abi_image_method_not_label:
  compile_method_id_runtime ty v flag sa = (op,sb) ==> op <> Label l
Proof
  Cases_on `flag`
  >- metis_tac[compile_method_id_word_safe_operand, safe_operand_def] >>
  simp[builtinHashingTheory.compile_method_id_runtime_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_builtin_method_not_label:
  compile_builtin_dispatch_body f ce vt ty MethodId args sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[abi_image_literal_not_label]
  >~ [`as_ptr_val _ _ _ = _`] >-
    (qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
     Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
     strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
     metis_tac[abi_image_method_not_label]) >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >> metis_tac[abi_image_method_not_label]
QED

Theorem abi_image_builtin_acc_label:
  compile_builtin_dispatch_body f ce vt ty (Acc item) args sa = (vv,sb) /\
  vv_operand vv = Label l ==>
  item = Address /\ lower_value f ce (BaseT AddressT) (HD args) sa = (Label l,sb)
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >> metis_tac[abi_image_acc_label]
QED

Theorem abi_image_builtin_wei_label:
  compile_builtin_dispatch_body f ce vt ty (AsWeiValue denom) args sa = (vv,sb) /\
  vv_operand vv = Label l ==>
  lower_value f ce (expr_type (HD args)) (HD args) sa = (Label l,sb)
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >>
  metis_tac[abi_image_wei_int_label, abi_image_wei_decimal_not_label]
QED

Theorem abi_image_builtin_label:
  compile_builtin_dispatch_body f ce vt ty bi args sa = (vv,sb) /\
  vv_operand vv = Label l ==>
  (bi = Acc Address /\
   lower_value f ce (BaseT AddressT) (HD args) sa = (Label l,sb)) \/
  (?denom. bi = AsWeiValue denom /\
   lower_value f ce (expr_type (HD args)) (HD args) sa = (Label l,sb))
Proof
  Cases_on `bi` >> strip_tac
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Acc item) _ _ = _`] >-
    (drule_all abi_image_builtin_acc_label >> strip_tac >> gvs[])
  >~ [`compile_builtin_dispatch_body _ _ _ _ (AsWeiValue denom) _ _ = _`] >-
    (drule_all abi_image_builtin_wei_label >> strip_tac >> gvs[]) >>
  metis_tac[abi_image_builtin_scalar_not_label, abi_image_builtin_hash_not_label,
            abi_image_builtin_len_not_label, abi_image_builtin_bop_not_label,
            abi_image_builtin_fresh_not_label, abi_image_builtin_makearray_not_label,
            abi_image_builtin_method_not_label]
QED

Theorem abi_image_empty_not_label:
  compile_builtin_empty_complex sz bs sa = (buf,sb) ==> buf.buf_operand <> Label l
Proof
  simp[builtinSimpleTheory.compile_builtin_empty_complex_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> Cases_on `bs` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_type_builtin_nonconvert_not_label:
  tb <> Convert /\
  compile_type_builtin_dispatch_body f ce vt ty tb rt args sa = (vv,sb) ==>
  vv_operand vv <> Label l
Proof
  Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[vv_operand_def]
  >~ [`if is_word_type _ then _ else _`] >-
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[vv_operand_def, base_ptr_def] >> metis_tac[abi_image_empty_not_label])
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
  metis_tac[abi_image_abi_encode_not_label, abi_image_abi_decode_not_label]
QED

Theorem abi_image_widen_copy_not_label[local]:
  compile_bytestring_widen_copy d v sz sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[compile_bytestring_widen_copy_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_type_builtin_convert_label:
  compile_type_builtin_dispatch_body f ce vt ty Convert rt args sa = (vv,sb) /\
  vv_operand vv = Label l ==>
  ?sm. lower_value f ce (expr_type (HD args)) (HD args) sa = (Label l,sm) /\
       sb.cs_blocks = sm.cs_blocks
Proof
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[AllCaseEqs(), vv_operand_def] >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >>
  metis_tac[abi_image_convert_label, abi_image_widen_copy_not_label]
QED

Theorem abi_image_type_builtin_label:
  compile_type_builtin_dispatch_body f ce vt ty tb rt args sa = (vv,sb) /\
  vv_operand vv = Label l ==>
  tb = Convert /\
  ?sm. lower_value f ce (expr_type (HD args)) (HD args) sa = (Label l,sm) /\
       sb.cs_blocks = sm.cs_blocks
Proof
  Cases_on `tb = Convert` >> strip_tac >> gvs[]
  >- metis_tac[abi_image_type_builtin_convert_label] >>
  metis_tac[abi_image_type_builtin_nonconvert_not_label]
QED

Theorem abi_image_expr_builtin_label:
  compile_expr_body f g h ce ty (Builtin ann bi args) sa = (vv,sb) ==>
  vv_operand vv = Label l ==>
  g ce ann ty bi args sa = (vv,sb)
Proof
  Cases_on `bi = AddMod` >- (gvs[] >> suspend "add") >>
  Cases_on `bi = MulMod` >- (gvs[] >> suspend "mul") >>
  Cases_on `bi = PowMod256` >- (gvs[] >> suspend "pow") >>
  Cases_on `bi` >> gvs[] >>
  simp[compile_expr_body_def, expr_type_def,
       word_list_result_elim, word_expr_result_elim]
QED

Resume abi_image_expr_builtin_label[add]:
  Cases_on `args` >- simp[compile_expr_body_def, expr_type_def] >>
  rename1 `a::rest` >> Cases_on `a` >>
  simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest` >> simp[] >> rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >> Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::Name _ _::m::rest` >>
  Cases_on `m` >> simp[] >> Cases_on `rest` >> simp[] >>
  metis_tac[abi_image_named_modular_not_label]
QED

Resume abi_image_expr_builtin_label[mul]:
  Cases_on `args` >- simp[compile_expr_body_def, expr_type_def] >>
  rename1 `a::rest` >> Cases_on `a` >>
  simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest` >> simp[] >> rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >> Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::Name _ _::m::rest` >>
  Cases_on `m` >> simp[] >> Cases_on `rest` >> simp[] >>
  metis_tac[abi_image_named_modular_not_label]
QED

Resume abi_image_expr_builtin_label[pow]:
  Cases_on `args` >- simp[compile_expr_body_def, expr_type_def] >>
  rename1 `a::rest` >> Cases_on `a` >>
  simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest` >> simp[] >> rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >> Cases_on `rest` >> simp[]
  >- metis_tac[abi_image_named_modular_not_label] >>
  simp[word_expr_result_elim, word_list_result_elim]
QED

Finalise abi_image_expr_builtin_label

Theorem abi_image_expr_body_label:
  (!ann bi args s vv s'.
    g ce ann ty bi args s = (vv,s') /\ vv_operand vv = Label l ==>
    s'.cs_blocks = s.cs_blocks) /\
  (!ann tb rt args s vv s'.
    h ce ann ty tb rt args s = (vv,s') /\ vv_operand vv = Label l ==>
    s'.cs_blocks = s.cs_blocks) /\
  compile_expr_body f g h ce ty e sa = (vv,sb) /\ vv_operand vv = Label l ==>
  sb.cs_blocks = sa.cs_blocks
Proof
  Cases_on `e` >> rpt strip_tac
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _ = _`] >-
    (drule_all abi_image_expr_builtin_label >> metis_tac[])
  >~ [`compile_expr_body _ _ _ _ _ (TopLevelName _ _) _ = _`] >-
    metis_tac[abi_image_toplevel_not_label]
  >~ [`compile_expr_body _ _ _ _ _ (Pop _ _) _ = _`] >-
    metis_tac[abi_image_pop_not_label]
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _ = _`] >-
    metis_tac[abi_image_struct_not_label]
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _ = _`] >-
    metis_tac[abi_image_ifexp_not_label]
  >~ [`compile_expr_body _ _ _ _ _ (FlagMember _ _ _) _ = _`] >-
    metis_tac[abi_image_flag_not_label] >>
  gvs[compile_expr_body_def, expr_type_def, LET_THM] >>
  metis_tac[abi_image_name_label, abi_image_literal_not_label,
            abi_image_subscript_not_label, abi_image_attribute_not_label,
            abi_image_call_not_label]
QED

Theorem abi_image_child_lower_label:
  (!e ce ty s vv s'. expr_size e < bound /\
    f ce ty e s = (vv,s') /\ vv_operand vv = Label l ==>
    s'.cs_blocks = s.cs_blocks) /\
  lower_value (expr_child_callback bound f) ce ty e sa = (Label l,sb) ==>
  sb.cs_blocks = sa.cs_blocks
Proof
  Cases_on `expr_size e < bound` >>
  simp[lower_value_def, comp_bind_def, expr_child_callback_def,
       invalid_expr_call_def, unwrap_value_def, comp_return_def, LET_THM] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[])
  >- (drule abi_image_unwrap_label >> strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[unwrap_value_def, comp_return_def]
QED

Theorem abi_image_compile_mutual:
  (!ce ty e sa vv sb l.
    compile_expr ce ty e sa = (vv,sb) /\ vv_operand vv = Label l ==>
    sb.cs_blocks = sa.cs_blocks) /\
  (!ce ann ty bi args sa vv sb l.
    compile_builtin_dispatch ce ann ty bi args sa = (vv,sb) /\
    vv_operand vv = Label l ==> sb.cs_blocks = sa.cs_blocks) /\
  (!ce ann ty tb rt args sa vv sb l.
    compile_type_builtin_dispatch ce ann ty tb rt args sa = (vv,sb) /\
    vv_operand vv = Label l ==> sb.cs_blocks = sa.cs_blocks)
Proof
  ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume abi_image_compile_mutual[expr]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule abi_image_expr_body_label >>
  goal_assum (drule_at (Pat `compile_expr_body`)) >>
  qexists_tac `l` >> simp[] >> conj_tac
  >- (rpt gen_tac >> simp[builtin_child_callback_def] >>
      Cases_on `list_size expr_size args < expr_size e` >> simp[]
      >- metis_tac[] >>
      simp[invalid_expr_call_def, LET_THM] >> strip_tac >>
      rpt (pairarg_tac >> gvs[vv_operand_def])) >>
  rpt gen_tac >> simp[type_child_callback_def] >>
  Cases_on `list_size expr_size args < expr_size e` >> simp[]
  >- metis_tac[] >>
  simp[invalid_expr_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[vv_operand_def])
QED

Resume abi_image_compile_mutual[builtin]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  drule_all abi_image_builtin_label >> strip_tac >>
  drule_at (Pat `lower_value`) abi_image_child_lower_label >>
  (impl_tac >- metis_tac[]) >> simp[]
QED

Resume abi_image_compile_mutual[type_builtin]:
  rpt gen_tac >> simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  drule_all abi_image_type_builtin_label >> strip_tac >>
  `sm.cs_blocks = sa.cs_blocks` suffices_by metis_tac[] >>
  drule_at (Pat `lower_value`) abi_image_child_lower_label >>
  (impl_tac >- metis_tac[]) >> simp[]
QED

Finalise abi_image_compile_mutual

Theorem abi_image_compile_expr_label:
  compile_expr ce ty e sa = (vv,sb) /\ vv_operand vv = Label l ==>
  sb.cs_blocks = sa.cs_blocks
Proof
  metis_tac[abi_image_compile_mutual]
QED

Theorem abi_image_lower_value_label:
  lower_value compile_expr ce ty e sa = (Label l,sb) ==>
  sb.cs_blocks = sa.cs_blocks
Proof
  simp[lower_value_def, comp_bind_def, LET_THM] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  drule abi_image_unwrap_label >> strip_tac >> gvs[] >>
  metis_tac[abi_image_compile_expr_label]
QED

Theorem abi_image_lower_value_label_emitted:
  lower_value compile_expr ce ty e sa = (Label l,sb) ==>
  emitted_blocks sa sb = []
Proof
  strip_tac >> drule abi_image_lower_value_label >>
  simp[emitted_blocks_def]
QED

Theorem abi_image_lower_value_label_no_collision:
  lower_value compile_expr ce ty e sa = (Label l,sb) ==>
  !bb. MEM bb (emitted_blocks sa sb) ==> bb.bb_label <> sb.cs_current_bb
Proof
  strip_tac >> drule abi_image_lower_value_label_emitted >> simp[]
QED
