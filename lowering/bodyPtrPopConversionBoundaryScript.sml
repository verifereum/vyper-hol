Theory bodyPtrPopConversionBoundary
Ancestors bodyPtrPopConversionGuardBoundary bodyPtrPopPowBoundary
  bodyPtrPopCompilerBoundary bodyPtrPopClampBoundary
  bodyPtrPopArithmeticBoundary
  bodyPtrPopIntClampBoundary bodyPtrPopBytesWordBoundary
  exprLowering emitHelper compileEnv venomInst list

Theorem pop_convert_int_int_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvIntToInt ins ib outs ob) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def] >> rpt IF_CASES_TAC >>
  simp[comp_return_def] >> rpt strip_tac >> gvs[]
  >>~- ([`compile_int_clamp _ _ _ sa = (r,sb)`],
        drule_all pop_compile_int_clamp_boundary >> simp[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND]
  >~ [`mk_inst _ AND _ _`]
  >- (irule pop_guard_suffix_template >>
      simp[mk_inst_def] >> qexistsl_tac [`AND`,`[GT;ISZERO;SLT;ISZERO]`] >> simp[]) >>
  irule pop_clamp_short_template >> simp[mk_inst_def]
QED

Theorem pop_convert_int_bytes_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvIntToBytesM ins ib m) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def] >> rpt IF_CASES_TAC >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_convert_int_decimal_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvIntToDecimal ins ib d lo hi) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def] >> rpt IF_CASES_TAC >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_convert_decimal_int_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvDecimalToInt d il ih ol oh ins) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def] >> rpt IF_CASES_TAC >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_convert_bytes_address_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvBytesToAddress m) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `m * 8 > 160` >> simp[compile_type_convert_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND]
  >~ [`mk_inst _ ASSERT _ _`]
  >- (irule pop_guard_short_suffix_template >> simp[mk_inst_def] >>
      qexistsl_tac [`GT`,`[SHR]`] >> simp[]) >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_convert_bytes_decimal_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvBytesMToDecimal m d lo hi) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `m * 8 > 168` >> simp[compile_type_convert_def] >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND]
  >~ [`mk_inst _ ASSERT _ _`]
  >- (irule pop_guard_suffix_template >> simp[mk_inst_def] >>
      qexistsl_tac [`AND`,`[SAR;SLT;ISZERO;SGT;ISZERO]`] >> simp[]) >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_convert_bytes_bytes_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvBytesMToBytesM im om) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def] >> IF_CASES_TAC >> simp[comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  drule_at (Pat `_ sa = (_,sb)`) pop_single_bound_check_boundary >> simp[]
QED

Theorem pop_convert_bytestring_cast_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvBytestringCast mx n) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def] >> IF_CASES_TAC >> simp[comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_guard_short_suffix_template >> simp[mk_inst_def] >>
  qexistsl_tac [`GT`,`[MLOAD]`] >> simp[]
QED

Theorem pop_convert_bytes_int_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvBytesToInt m outs ob) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def, Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (Cases_on `outs` >> gvs[] >>
     drule_at (Pat `_ sa = (_,cs')`) pop_emit_op_boundary >> simp[]) >>
  Cases_on `m * 8 > ob` >> gvs[comp_return_def] >>
  drule_all pop_compile_int_clamp_boundary >> simp[]
QED

Theorem pop_convert_bytestring_int_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvBytestringToInt ins ob n) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def, Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `_ sa = (_,cs')`) pop_load_bytestring_as_word_boundary >>
     Cases_on `ins` >> simp[]) >>
  PairCases_on `a` >> gvs[] >>
  Cases_on `n * 8 > ob` >> gvs[comp_return_def] >>
  drule_all pop_compile_int_clamp_boundary >> simp[]
QED

Theorem pop_convert_bytestring_bool_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v ConvBytestringToBool sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def, Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `_ sa = (_,cs')`) pop_load_bytestring_as_word_boundary >> simp[]) >>
  PairCases_on `a` >> gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def, pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED

Theorem pop_convert_bytestring_bytes_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvBytestringToBytesM m) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def, Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `_ sa = (_,cs')`) pop_load_bytestring_as_word_boundary >> simp[]) >>
  PairCases_on `a` >> gvs[] >>
  drule_at (Pat `_ cs' = (_,sb)`) pop_emit_op_boundary >> simp[]
QED

Theorem pop_convert_bytestring_decimal_boundary:
  pop_comp_boundary sa /\
  compile_type_convert v (ConvBytestringToDecimal d lo hi n) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_type_convert_def, Once comp_bind_def] >> pairarg_tac >>
  rpt strip_tac >>
  `pop_comp_boundary cs'` by
    (drule_at (Pat `_ sa = (_,cs')`) pop_load_bytestring_as_word_boundary >> simp[]) >>
  PairCases_on `a` >> Cases_on `n * 8 <= 168` >> gvs[comp_return_def] >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_id_def, fresh_var_def, emit_def,
      pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule pop_clamp_signed_template >> simp[mk_inst_def]
QED

Theorem pop_compile_type_convert_boundary:
  pop_comp_boundary sa /\ compile_type_convert v conversion sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `conversion` >> rpt strip_tac
  >~ [`compile_type_convert v (ConvIntToInt _ _ _ _) sa = _`]
  >- (drule_all pop_convert_int_int_boundary >> simp[])
  >~ [`compile_type_convert v (ConvIntToBytesM _ _ _) sa = _`]
  >- (drule_all pop_convert_int_bytes_boundary >> simp[])
  >~ [`compile_type_convert v (ConvIntToDecimal _ _ _ _ _) sa = _`]
  >- (drule_all pop_convert_int_decimal_boundary >> simp[])
  >~ [`compile_type_convert v (ConvDecimalToInt _ _ _ _ _ _) sa = _`]
  >- (drule_all pop_convert_decimal_int_boundary >> simp[])
  >~ [`compile_type_convert v (ConvBytesToAddress _) sa = _`]
  >- (drule_all pop_convert_bytes_address_boundary >> simp[])
  >~ [`compile_type_convert v (ConvBytesMToDecimal _ _ _ _) sa = _`]
  >- (drule_all pop_convert_bytes_decimal_boundary >> simp[])
  >~ [`compile_type_convert v (ConvBytesMToBytesM _ _) sa = _`]
  >- (drule_all pop_convert_bytes_bytes_boundary >> simp[])
  >~ [`compile_type_convert v (ConvBytestringCast _ _) sa = _`]
  >- (drule_all pop_convert_bytestring_cast_boundary >> simp[])
  >~ [`compile_type_convert v (ConvBytesToInt _ _ _) sa = _`]
  >- (drule_all pop_convert_bytes_int_boundary >> simp[])
  >~ [`compile_type_convert v (ConvBytestringToInt _ _ _) sa = _`]
  >- (drule_all pop_convert_bytestring_int_boundary >> simp[])
  >~ [`compile_type_convert v ConvBytestringToBool sa = _`]
  >- (drule_all pop_convert_bytestring_bool_boundary >> simp[])
  >~ [`compile_type_convert v (ConvBytestringToBytesM _) sa = _`]
  >- (drule_all pop_convert_bytestring_bytes_boundary >> simp[])
  >~ [`compile_type_convert v (ConvBytestringToDecimal _ _ _ _) sa = _`]
  >- (drule_all pop_convert_bytestring_decimal_boundary >> simp[])
  >~ [`compile_type_convert v (ConvToFlag n) sa = _`]
  >- (gvs[compile_type_convert_def] >> Cases_on `n < 256` >>
      gvs[comp_return_def] >> drule_all pop_compile_int_clamp_boundary >> simp[]) >>
  gvs[compile_type_convert_def, emit_op_def, emit_void_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
      emit_def, pop_comp_boundary_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND]
  >~ [`mk_inst _ ASSERT _ _`]
  >- (irule pop_clamp_short_template >> simp[mk_inst_def]) >>
  irule pop_no_sub_finished_template >> simp[mk_inst_def]
QED
