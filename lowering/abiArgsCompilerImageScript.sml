Theory abiArgsCompilerImage
Ancestors
  exprLowering context compileEnv emitHelper vyperAST

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
  Cases_on `retsz = 0` >- simp[comp_return_def] >>
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
  >~ [`RawCallCalldataTarget`] >- suspend "rawdata" >>
  simp[compile_call_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> gvs[vv_operand_def]
  >~ [`ce.ce_func_info name = info`] >- suspend "internal"
  >~ [`compile_call f ce rt ty (ExtCall b b0 p l') args default_ret sa = _`]
    >- suspend "external" >>
  suspend "send"
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

Resume abi_image_call_not_label[send]:
  Cases_on `args` >> gvs[vv_operand_def] >>
  rename1 `list_CASE tail _ _` >> Cases_on `tail` >> gvs[vv_operand_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[vv_operand_def]) >>
  simp[vv_operand_def]
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
  compile_dynarray_pop bop ws es load store sa = (op,sb) ==> op <> Label l
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
