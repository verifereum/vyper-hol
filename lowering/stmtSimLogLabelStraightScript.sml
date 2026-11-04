(* Compiler-side conditional straightness for Label-valued results. *)
Theory stmtSimLogLabelStraight
Ancestors
  exprSafeOperand exprLowering context compileEnv abiDecodeStaticProps
  emitHelperProps emitHelper exprLoweringProps venomInst list rich_list
  exprReasonOperand vyperAST

Theorem log_unwrap_label_origin:
  unwrap_value ce vv sa = (Label lab,sb) ==>
  vv_operand vv = Label lab /\ sb = sa
Proof
  Cases_on `vv` >> simp[unwrap_value_def, vv_operand_def, comp_return_def] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty`
  >- (simp[] >> strip_tac >> drule compile_ptr_load_safe_operand >>
      simp[safe_operand_def]) >>
  simp[] >> Cases_on `p.ptr_location` >>
  simp[compile_ensure_in_memory_def, comp_return_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule alloc_buffer_not_label >> simp[]
QED

Theorem log_convert_label_straight:
  compile_type_convert op conv sa = (Label lab,sb) ==>
  op = Label lab /\ dec_straight sa sb
Proof
  Cases_on `conv` >>
  simp[compile_type_convert_def, load_bytestring_as_word_def, compile_int_clamp_def,
       compile_alloc_buffer_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt (IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def]) >>
  strip_tac >> gvs[] >>
  simp[dec_straight_def, inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem log_lower_value_label_straight:
  (!ce ty e sa vv sb lab.
    cfn ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) ==>
  !ce ty e sa sb lab.
    lower_value cfn ce ty e sa = (Label lab,sb) ==>
    dec_straight sa sb
Proof
  strip_tac >> rpt gen_tac >>
  simp[lower_value_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> drule log_unwrap_label_origin >>
  strip_tac >> gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem log_name_label_straight:
  compile_name_vv ce ty id sa = (vv,sb) /\ vv_operand vv = Label lab ==>
  dec_straight sa sb
Proof
  simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[vv_operand_def] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME loc` >> Cases_on `loc` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      vv_operand_def, mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[vv_operand_def]) >>
  simp[dec_straight_def, inst_extends_def, emitted_insts_def]
QED

Theorem log_convert_widen_label[local]:
  (if c then as_stack_val vt (compile_bytestring_widen_copy d v sz st1)
   else y) = (vv,sb) /\
  vv_operand vv = Label lab ==>
  y = (vv,sb)
Proof
  Cases_on `c` >> simp[] >>
  Cases_on `compile_bytestring_widen_copy d v sz st1` >>
  simp[as_stack_val_def] >> strip_tac >> gvs[vv_operand_def] >>
  qpat_x_assum `compile_bytestring_widen_copy _ _ _ _ = _` mp_tac >>
  simp[compile_bytestring_widen_copy_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule alloc_buffer_not_label >> simp[]
QED

Theorem log_type_convert_dispatch_label_straight:
  (!ce ty e sa vv sb lab.
    cfn ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) /\
  compile_type_builtin_dispatch_body cfn ce vt ty Convert rt args sa = (vv,sb) /\
  vv_operand vv = Label lab ==>
  dec_straight sa sb
Proof
  strip_tac >>
  `!ce ty e sa sb lab.
     lower_value cfn ce ty e sa = (Label lab,sb) ==> dec_straight sa sb` by
    (drule log_lower_value_label_straight >> simp[]) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  IF_CASES_TAC >- (strip_tac >> gvs[vv_operand_def]) >>
  pop_assum kall_tac >> strip_tac >>
  drule_all log_convert_widen_label >>
  qpat_x_assum `(if _ then _ else _) = _` kall_tac >>
  Cases_on `rt` >> simp[] >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt cres` >>
  Cases_on `cres` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def] >>
  qpat_x_assum `_ = compile_type_convert _ _ _` (assume_tac o SYM) >>
  drule log_convert_label_straight >> strip_tac >> gvs[] >>
  metis_tac[dec_straight_trans]
QED

Theorem log_acc_label_straight:
  (!ce ty e sa vv sb lab.
    cfn ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) /\
  compile_acc cfn ce e item sa = (Label lab,sb) ==>
  dec_straight sa sb
Proof
  strip_tac >>
  `!ce ty e sa sb lab.
     lower_value cfn ce ty e sa = (Label lab,sb) ==> dec_straight sa sb` by
    (drule log_lower_value_label_straight >> simp[]) >>
  qpat_x_assum `compile_acc _ _ _ _ _ = _` mp_tac >>
  Cases_on `item` >> simp[compile_acc_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_op_safe_operand, safe_operand_def]
QED

Theorem log_wei_int_label_origin:
  compile_as_wei_value_int op scale signed sa = (Label lab,sb) ==>
  op = Label lab /\ sb = sa
Proof
  simp[builtinMiscTheory.compile_as_wei_value_int_def] >>
  IF_CASES_TAC >- simp[comp_return_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def]
QED

Theorem log_wei_dispatch_label_straight:
  (!ce ty e sa vv sb lab.
    cfn ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) /\
  compile_builtin_dispatch_body cfn ce vt ty (AsWeiValue denom) args sa = (vv,sb) /\
  vv_operand vv = Label lab ==>
  dec_straight sa sb
Proof
  strip_tac >>
  `!ce ty e sa sb lab.
     lower_value cfn ce ty e sa = (Label lab,sb) ==> dec_straight sa sb` by
    (drule log_lower_value_label_straight >> simp[]) >>
  qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  pairarg_tac >> gvs[] >> IF_CASES_TAC >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt cres` >>
  Cases_on `cres` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[vv_operand_def]
  >~ [`_ = compile_as_wei_value_int _ _ _ _`]
  >- (qpat_x_assum `_ = compile_as_wei_value_int _ _ _ _` (assume_tac o SYM) >>
      drule log_wei_int_label_origin >> strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[builtinMiscTheory.compile_as_wei_value_decimal_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      AllCaseEqs()] >>
  Cases_on `denomination_multiplier denom = 1` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def]
QED

Theorem log_reason_shape_not_label[local]:
  reason_result_shape ty loc vv ==> vv_operand vv <> Label lab
Proof
  Cases_on `vv` >> simp[reason_result_shape_def, vv_operand_def]
QED

Theorem log_builtin_dispatch_label_straight:
  (!ce ty e sa vv sb lab.
    cfn ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) /\
  compile_builtin_dispatch_body cfn ce vt ty bi args sa = (vv,sb) /\
  vv_operand vv = Label lab ==>
  dec_straight sa sb
Proof
  Cases_on `bi`
  >~ [`Acc item`]
  >- (strip_tac >>
      qpat_x_assum `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_builtin_dispatch_body_def, LET_THM] >>
      qmatch_goalsub_abbrev_tac `as_stack_val vt cres` >>
      Cases_on `cres` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
      strip_tac >> gvs[vv_operand_def] >>
      qpat_x_assum `_ = compile_acc _ _ _ _ _` (assume_tac o SYM) >>
      drule_at (Pat `compile_acc`) log_acc_label_straight >>
      disch_then irule >> first_assum ACCEPT_TAC)
  >~ [`AsWeiValue denom`]
  >- metis_tac[log_wei_dispatch_label_straight] >>
  strip_tac >>
  `reason_result_shape vt LocMemory vv` suffices_by
    metis_tac[log_reason_shape_not_label]
  >~ [`Bop bop`] >- metis_tac[reason_builtin_bop]
  >~ [`Len`] >- metis_tac[reason_builtin_len]
  >~ [`MethodId`] >- metis_tac[reason_builtin_method_id]
  >~ [`MakeArray et bd`] >- metis_tac[reason_builtin_makearray]
  >~ [`Keccak256`] >- metis_tac[reason_builtin_hash]
  >~ [`Sha256`] >- metis_tac[reason_builtin_hash]
  >~ [`CalldataSlice n`] >- metis_tac[reason_builtin_fresh]
  >~ [`ECAdd`] >- metis_tac[reason_builtin_fresh]
  >~ [`ECMul`] >- metis_tac[reason_builtin_fresh]
  >~ [`Concat n`] >- metis_tac[reason_builtin_fresh]
  >~ [`Slice n`] >- metis_tac[reason_builtin_fresh]
  >~ [`Uint2Str n`] >- metis_tac[reason_builtin_fresh] >>
  metis_tac[reason_builtin_scalar]
QED

Theorem log_type_dispatch_label_straight:
  (!ce ty e sa vv sb lab.
    cfn ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) /\
  compile_type_builtin_dispatch_body cfn ce vt ty tb rt args sa = (vv,sb) /\
  vv_operand vv = Label lab ==>
  dec_straight sa sb
Proof
  Cases_on `tb`
  >~ [`Convert`] >- metis_tac[log_type_convert_dispatch_label_straight]
  >~ [`Empty`]
  >- (simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
      IF_CASES_TAC >> simp[] >> rpt (pairarg_tac >> gvs[]) >>
      strip_tac >> gvs[vv_operand_def, base_ptr_def] >>
      metis_tac[exprSafeOperandBuiltinsTheory.compile_empty_not_label])
  >~ [`Extract32`]
  >- (simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
      qmatch_goalsub_abbrev_tac `as_stack_val vt cres` >>
      Cases_on `cres` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
      strip_tac >> gvs[vv_operand_def] >>
      metis_tac[exprSafeOperandBuiltinsTheory.compile_extract32_load_safe_operand,
        exprSafeOperandBuiltinsTheory.compile_clamp_basetype_safe_operand,
        safe_operand_def])
  >~ [`AbiEncode ensure mid`]
  >- (simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
      qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
      qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory cres` >>
      Cases_on `cres` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
      strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
      metis_tac[reason_abi_encode_operand])
  >~ [`AbiDecode unwrap`]
  >- (simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
      qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory cres` >>
      Cases_on `cres` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
      strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
      metis_tac[exprSafeOperandBuiltinsTheory.lower_abi_decode_not_label]) >>
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[vv_operand_def]
QED

Theorem log_expr_body_label_straight:
  (!ce rt ty bi args sa vv sb lab.
    g ce rt ty bi args sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) /\
  (!ce vt ty tb rt args sa vv sb lab.
    h ce vt ty tb rt args sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) /\
  compile_expr_body f g h cenv ty e sa = (vv,sb) /\
  vv_operand vv = Label lab ==>
  dec_straight sa sb
Proof
  strip_tac >> Cases_on `e`
  >~ [`IfExp t cond te ee`]
  >- metis_tac[reason_compile_ifexp, log_reason_shape_not_label]
  >~ [`StructLit t nm fields`]
  >- metis_tac[reason_compile_structlit, log_reason_shape_not_label]
  >~ [`Builtin t bi args`]
  >- (drule reason_compile_expr_builtin_shape_classify >> strip_tac >>
      metis_tac[log_reason_shape_not_label])
  >~ [`TypeBuiltin t tb rt args`]
  >- (gvs[compile_expr_body_def, expr_type_def, LET_THM] >> metis_tac[])
  >~ [`Pop t target`]
  >- (mp_tac reason_compile_pop >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      metis_tac[log_reason_shape_not_label])
  >~ [`TopLevelName t nsid`]
  >- (gvs[compile_expr_body_def, expr_type_def, LET_THM, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[vv_operand_def, mk_ptr_def] >>
      rename1 `FLOOKUP cenv.ce_module_vars nsid = SOME loc` >>
      Cases_on `loc` >> gvs[vv_operand_def, mk_ptr_def]) >>
  gvs[compile_expr_body_def, expr_type_def, LET_THM]
  >~ [`compile_name_vv _ _ _ _ = _`] >- metis_tac[log_name_label_straight]
  >~ [`compile_literal_vv _ _ _ = _`]
  >- metis_tac[reason_compile_literal, log_reason_shape_not_label]
  >~ [`compile_call _ _ _ _ _ _ _ _ = _`]
  >- metis_tac[reason_compile_call, log_reason_shape_not_label]
  >~ [`compile_attribute _ _ _ _ _ _ _ = _`]
  >- metis_tac[exprSafeOperandBuiltinsTheory.compile_attribute_safe_operand,
              safe_operand_def]
  >~ [`compile_subscript _ _ _ _ _ _ _ = _`]
  >- metis_tac[exprSafeOperandBuiltinsTheory.compile_subscript_not_label] >>
  gvs[vv_operand_def]
QED

Theorem log_compiler_label_straight:
  (!ce ty e sa vv sb lab.
    compile_expr ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb) /\
  (!ce rt ty bi args sa vv sb lab.
    compile_builtin_dispatch ce rt ty bi args sa = (vv,sb) /\
    vv_operand vv = Label lab ==> dec_straight sa sb) /\
  (!ce vt ty tb rt args sa vv sb lab.
    compile_type_builtin_dispatch ce vt ty tb rt args sa = (vv,sb) /\
    vv_operand vv = Label lab ==> dec_straight sa sb)
Proof
  ho_match_mp_tac compile_expr_ind >> conj_tac
  >- suspend "expr" >> conj_tac
  >- suspend "builtin" >> suspend "type_builtin"
QED

Resume log_compiler_label_straight[builtin]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def] >>
  qmatch_goalsub_abbrev_tac `compile_builtin_dispatch_body f` >>
  `!ce ty e sa vv sb lab.
    f ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb` by
    (simp[Abbr `f`, exprCallBoundsTheory.expr_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  strip_tac >> drule_at (Pat `compile_builtin_dispatch_body`)
    log_builtin_dispatch_label_straight >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Resume log_compiler_label_straight[type_builtin]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_builtin_dispatch _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def] >>
  qmatch_goalsub_abbrev_tac `compile_type_builtin_dispatch_body f` >>
  `!ce ty e sa vv sb lab.
    f ce ty e sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb` by
    (simp[Abbr `f`, exprCallBoundsTheory.expr_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  strip_tac >> drule_at (Pat `compile_type_builtin_dispatch_body`)
    log_type_dispatch_label_straight >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Resume log_compiler_label_straight[expr]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def] >>
  qmatch_goalsub_abbrev_tac `compile_expr_body f bf tf` >>
  `!ce rt ty bi args sa vv sb lab.
    bf ce rt ty bi args sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb` by
    (simp[Abbr `bf`, exprCallBoundsTheory.builtin_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  `!ce vt ty tb rt args sa vv sb lab.
    tf ce vt ty tb rt args sa = (vv,sb) /\ vv_operand vv = Label lab ==>
    dec_straight sa sb` by
    (simp[Abbr `tf`, exprCallBoundsTheory.type_child_callback_def] >>
     rpt gen_tac >> IF_CASES_TAC >- metis_tac[] >>
     simp[exprCallBoundsTheory.invalid_expr_call_def, LET_THM] >>
     pairarg_tac >> rpt strip_tac >> gvs[vv_operand_def]) >>
  strip_tac >> irule log_expr_body_label_straight >>
  first_assum (irule_at Any) >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise log_compiler_label_straight


Theorem log_lower_compile_expr_label_straight:
  lower_value compile_expr ce ty e sa = (Label lab,sb) ==>
  dec_straight sa sb
Proof
  mp_tac (Q.ISPEC `compile_expr` (GEN_ALL log_lower_value_label_straight)) >>
  metis_tac[CONJUNCT1 log_compiler_label_straight]
QED
