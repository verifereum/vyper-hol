Theory convertScalarDecimalRun
Ancestors
  convertScalarChecks convertScalarDecimal exprSimConvert exprLowering
  emitHelperProps exprLoweringProps compileEnv vyperArith vyperValue
  integer integer_word words venomState
Libs
  intLib

Theorem scalar_int_decimal_signed_checks:
  !bits i. 0 < bits /\ bits <= 256 /\ within_int_bound (Signed bits) i ==>
    ((word_lt (i2w i:bytes32)
        (i2w ((-&(2 ** 167)) quot decimal_scale))) <=>
      i < (-&(2 ** 167)) quot decimal_scale) /\
    ((word_gt (i2w i:bytes32)
        (i2w ((&(2 ** 167) - 1) quot decimal_scale))) <=>
      i > (&(2 ** 167) - 1) quot decimal_scale)
Proof
  rpt strip_tac >>
  `w2i (i2w i:bytes32) = i` by
    (irule w2i_i2w_within_signed >> metis_tac[]) >>
  `w2i (i2w ((-&(2 ** 167)) quot decimal_scale):bytes32) =
      (-&(2 ** 167)) quot decimal_scale` by
    (irule w2i_i2w_within_signed >> qexists_tac `256` >>
     simp[scalar_decimal_prescale_endpoints]) >>
  `w2i (i2w ((&(2 ** 167) - 1) quot decimal_scale):bytes32) =
      (&(2 ** 167) - 1) quot decimal_scale` by
    (irule w2i_i2w_within_signed >> qexists_tac `256` >>
     simp[scalar_decimal_prescale_endpoints]) >>
  simp[WORD_LTi, WORD_GTi]
QED

Theorem scalar_int_decimal_unsigned_check:
  !bits i. 0 < bits /\ bits <= 256 /\ within_int_bound (Unsigned bits) i ==>
    (w2n (i2w i:bytes32) >
       w2n (i2w ((&(2 ** 167) - 1) quot decimal_scale):bytes32) <=>
     i > (&(2 ** 167) - 1) quot decimal_scale)
Proof
  rpt strip_tac >>
  `?n. i = &n /\ n < 2 ** bits` by
    (gvs[within_int_bound_ineq] >>
     `?n. i = &n` by (irule NUM_POSINT_EXISTS >> intLib.ARITH_TAC) >>
     gvs[]) >>
  `n < dimword (:256)` by
    (rewrite_tac[dimword_def] >>
     irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** bits` >> simp[]) >>
  gvs[i2w_pos, w2n_n2w] >>
  simp[decimal_scale_def, dimword_def, w2n_i2w] >> intLib.ARITH_TAC
QED

Theorem scalar_comparison_assert_extends[local]:
  !opc x c st bad st1 ok st2 st3.
    emit_op opc [x; Lit c] st = (bad,st1) /\
    emit_op ISZERO [bad] st1 = (ok,st2) /\
    emit_void ASSERT [ok] st2 = ((),st3) ==>
    st3.cs_current_insts = st.cs_current_insts ++ emitted_insts st st3
Proof
  rpt strip_tac >>
  drule_all scalar_assert_zero_extends >> strip_tac >>
  qpat_assum `emit_op opc _ _ = _`
    (mp_then Any strip_assume_tac emit_op_extends) >>
  `emitted_insts st st3 = emitted_insts st st1 ++ emitted_insts st1 st3` by
    (irule emitted_insts_append >> simp[]) >> simp[]
QED

Theorem scalar_int_decimal_lower_ok:
  !x bits i st st' ss.
    0 < bits /\ bits <= 256 /\ within_int_bound (Signed bits) i /\
    (-&(2 ** 167)) quot decimal_scale <= i /\
    (if -&(2 ** (bits - 1)) < (-&(2 ** 167)) quot decimal_scale then
       do bad <- emit_op SLT [x; Lit (i2w ((-&(2 ** 167)) quot decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      fresh_vars_wrt st' ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st st' /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt strip_tac >>
  Cases_on `-&(2 ** (bits - 1)) < (-&(2 ** 167)) quot decimal_scale`
  >- (gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
      `0 < bits` by decide_tac >>
      `~word_lt (i2w i:bytes32)
         (i2w ((-&(2 ** 167)) quot decimal_scale))` by
        (drule_all scalar_int_decimal_signed_checks >> strip_tac >>
         gvs[] >> intLib.ARITH_TAC) >>
      gvs[] >> drule_all scalar_comparison_assert_extends >> strip_tac >>
      drule_all scalar_signed_lower_ok >> simp[]) >>
  gvs[comp_return_def, emitted_insts_refl, run_inst_seq_nil, same_blocks_def]
QED

Theorem scalar_int_decimal_signed_upper_ok:
  !x bits i st st' ss.
    0 < bits /\ bits <= 256 /\ within_int_bound (Signed bits) i /\
    i <= (&(2 ** 167) - 1) quot decimal_scale /\
    (if &(2 ** (bits - 1) - 1) > (&(2 ** 167) - 1) quot decimal_scale then
       do bad <- emit_op SGT [x; Lit (i2w ((&(2 ** 167) - 1) quot decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      fresh_vars_wrt st' ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st st' /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt strip_tac >>
  drule_all scalar_int_decimal_signed_checks >> strip_tac >>
  `~word_gt (i2w i:bytes32)
       (i2w ((&(2 ** 167) - 1) quot decimal_scale))` by
    (gvs[] >> intLib.ARITH_TAC) >>
  Cases_on `&(2 ** (bits - 1) - 1) > (&(2 ** 167) - 1) quot decimal_scale`
  >- (gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
      drule_all scalar_comparison_assert_extends >> strip_tac >>
      drule_all scalar_signed_upper_ok >> simp[]) >>
  gvs[comp_return_def, emitted_insts_refl, run_inst_seq_nil, same_blocks_def]
QED

Theorem scalar_int_decimal_unsigned_upper_ok:
  !x bits i st st' ss.
    0 < bits /\ bits <= 256 /\ within_int_bound (Unsigned bits) i /\
    i <= (&(2 ** 167) - 1) quot decimal_scale /\
    (if &(2 ** bits - 1) > (&(2 ** 167) - 1) quot decimal_scale then
       do bad <- emit_op GT [x; Lit (i2w ((&(2 ** 167) - 1) quot decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      fresh_vars_wrt st' ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st st' /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt strip_tac >>
  drule_all scalar_int_decimal_unsigned_check >> strip_tac >>
  `w2n (i2w i:bytes32) <=
       w2n (i2w ((&(2 ** 167) - 1) quot decimal_scale):bytes32)` by
    (gvs[] >> intLib.ARITH_TAC) >>
  Cases_on `&(2 ** bits - 1) > (&(2 ** 167) - 1) quot decimal_scale`
  >- (gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
      drule_all scalar_comparison_assert_extends >> strip_tac >>
      drule_all scalar_unsigned_upper_ok >> simp[]) >>
  gvs[comp_return_def, emitted_insts_refl, run_inst_seq_nil, same_blocks_def]
QED


Theorem scalar_int_to_decimal_ok:
  !sg bits i x op st st' ss.
    0 < bits /\ bits <= 256 /\
    within_int_bound (if sg then Signed bits else Unsigned bits) i /\
    within_int_bound decimal_bound (i * decimal_scale) /\
    compile_type_convert x
      (ConvIntToDecimal sg bits 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1))
      st = (op,st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (i2w (i * decimal_scale))
Proof
  rpt strip_tac >>
  gns[scalar_decimal_prescale] >>
  Cases_on `sg` >> gns[]
  >- suspend "signed"
  >> suspend "unsigned"
QED

Resume scalar_int_to_decimal_ok[signed]:
      qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
      simp[compile_type_convert_def] >>
      qmatch_goalsub_abbrev_tac `comp_ignore_bind lower rest st = (op,st')` >>
      pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
      Cases_on `lower st` >> simp[] >> strip_tac >>
      rename1 `lower st = (u,st1)` >> Cases_on `u` >>
      gvs[Abbr `lower`] >>
      drule_all (SRULE[decimal_scale_def] scalar_int_decimal_lower_ok) >>
      strip_tac >>
      rename1 `run_inst_seq (emitted_insts st st1) ss = OK s_lower` >>
      qpat_x_assum `rest st1 = _` mp_tac >>
      simp[Abbr `rest`] >>
      qmatch_goalsub_abbrev_tac `comp_ignore_bind upper_action suffix_action st1 = (op,st')` >>
      pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
      Cases_on `upper_action st1` >> simp[] >> strip_tac >>
      rename1 `upper_action st1 = (u,st2)` >> Cases_on `u` >>
      gvs[Abbr `upper_action`, Abbr `suffix_action`] >>
      `eval_operand x s_lower = SOME (i2w i)` by metis_tac[] >>
      drule_all (SRULE[decimal_scale_def] scalar_int_decimal_signed_upper_ok) >>
      strip_tac >>
      rename1 `run_inst_seq (emitted_insts st1 st2) s_lower = OK s_upper` >>
      `eval_operand x s_upper = SOME (i2w i)` by metis_tac[] >>
      `eval_operand (Lit 0x2540BE400w) s_upper = SOME 0x2540BE400w`
        by simp[eval_operand_def] >>
      drule_all emit_op_MUL_correct >> strip_tac >>
      rename1 `eval_operand op s_result = SOME _` >>
      drule emit_op_extends >> strip_tac >>
      qexists_tac `s_result` >> conj_tac
      >- (irule scalar_run_suffix >> qexistsl_tac [`s_upper`, `st2`] >>
          simp[] >> conj_tac
          >- (irule scalar_run_suffix >>
              qexistsl_tac [`s_lower`, `st1`] >> simp[]) >>
          sym_tac >> irule emitted_insts_append >> simp[]) >>
      simp[GSYM word_i2w_mul, i2w_pos]
QED

Resume scalar_int_to_decimal_ok[unsigned]:
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp[compile_type_convert_def] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind lower rest st = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  simp[Abbr `lower`, comp_return_def] >>
  simp[Abbr `rest`] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind upper_action suffix_action st = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `upper_action st` >> simp[] >> strip_tac >>
  rename1 `upper_action st = (u,st1)` >> Cases_on `u` >>
  gvs[Abbr `upper_action`, Abbr `suffix_action`] >>
  drule_all (SRULE[decimal_scale_def] scalar_int_decimal_unsigned_upper_ok) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) ss = OK s_upper` >>
  `eval_operand x s_upper = SOME (i2w i)` by metis_tac[] >>
  `eval_operand (Lit 0x2540BE400w) s_upper = SOME 0x2540BE400w`
    by simp[eval_operand_def] >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  rename1 `eval_operand op s_result = SOME _` >>
  drule emit_op_extends >> strip_tac >>
  qexists_tac `s_result` >> conj_tac
  >- (irule scalar_run_suffix >> qexistsl_tac [`s_upper`, `st1`] >> simp[]) >>
  simp[GSYM word_i2w_mul, i2w_pos]
QED

Finalise scalar_int_to_decimal_ok

Theorem scalar_int_decimal_lower_abort:
  !x bits i st st' ss.
    0 < bits /\ bits <= 256 /\ within_int_bound (Signed bits) i /\
    i < (-&(2 ** 167)) quot decimal_scale /\
    (if -&(2 ** (bits - 1)) < (-&(2 ** 167)) quot decimal_scale then
       do bad <- emit_op SLT [x; Lit (i2w ((-&(2 ** 167)) quot decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `-&(2 ** (bits - 1)) < (-&(2 ** 167)) quot decimal_scale` by
    (qpat_x_assum `within_int_bound _ i` mp_tac >>
     asm_simp_tac pure_ss [within_int_bound_ineq] >> intLib.ARITH_TAC) >>
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  `0 < bits` by decide_tac >>
  `word_lt (i2w i:bytes32)
     (i2w ((-&(2 ** 167)) quot decimal_scale))` by
    (drule_all scalar_int_decimal_signed_checks >> simp[]) >>
  gvs[] >> drule_all scalar_signed_lower_abort >> simp[]
QED

Theorem scalar_int_decimal_signed_upper_abort:
  !x bits i st st' ss.
    0 < bits /\ bits <= 256 /\ within_int_bound (Signed bits) i /\
    i > (&(2 ** 167) - 1) quot decimal_scale /\
    (if &(2 ** (bits - 1) - 1) > (&(2 ** 167) - 1) quot decimal_scale then
       do bad <- emit_op SGT [x; Lit (i2w ((&(2 ** 167) - 1) quot decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `&(2 ** (bits - 1) - 1) > (&(2 ** 167) - 1) quot decimal_scale` by
    (qpat_x_assum `within_int_bound _ i` mp_tac >>
     asm_simp_tac pure_ss [within_int_bound_ineq] >> intLib.ARITH_TAC) >>
  drule_all scalar_int_decimal_signed_checks >> strip_tac >>
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all scalar_signed_upper_abort >> simp[]
QED

Theorem scalar_int_decimal_unsigned_upper_abort:
  !x bits i st st' ss.
    0 < bits /\ bits <= 256 /\ within_int_bound (Unsigned bits) i /\
    i > (&(2 ** 167) - 1) quot decimal_scale /\
    (if &(2 ** bits - 1) > (&(2 ** 167) - 1) quot decimal_scale then
       do bad <- emit_op GT [x; Lit (i2w ((&(2 ** 167) - 1) quot decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `&(2 ** bits - 1) > (&(2 ** 167) - 1) quot decimal_scale` by
    (qpat_x_assum `within_int_bound _ i` mp_tac >>
     asm_simp_tac pure_ss [within_int_bound_ineq] >> intLib.ARITH_TAC) >>
  drule_all scalar_int_decimal_unsigned_check >> strip_tac >>
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  irule scalar_unsigned_upper_abort >>
  metis_tac[arithmeticTheory.GREATER_DEF]
QED

Theorem scalar_conditional_assert_extends[local]:
  !guard opc x c st st'.
    (if guard then
       do bad <- emit_op opc [x; Lit c];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') ==>
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt strip_tac >> Cases_on `guard` >> gvs[comp_return_def]
  >- (gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
      drule_all scalar_comparison_assert_extends >> simp[]) >>
  simp[emitted_insts_refl]
QED

Theorem scalar_int_to_decimal_abort:
  !sg bits i x op st st' ss.
    0 < bits /\ bits <= 256 /\
    within_int_bound (if sg then Signed bits else Unsigned bits) i /\
    ~within_int_bound decimal_bound (i * decimal_scale) /\
    compile_type_convert x
      (ConvIntToDecimal sg bits 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1))
      st = (op,st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gns[scalar_decimal_prescale] >>
  Cases_on `sg` >> gns[]
  >- suspend "signed"
  >> suspend "unsigned"
QED

Resume scalar_int_to_decimal_abort[signed]:
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp[compile_type_convert_def] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind lower rest st = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `lower st` >> simp[] >> strip_tac >>
  rename1 `lower st = (u,st1)` >> Cases_on `u` >>
  qpat_x_assum `rest st1 = _` mp_tac >> simp[Abbr `rest`] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind upper_action suffix_action st1 = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `upper_action st1` >> simp[] >> strip_tac >>
  rename1 `upper_action st1 = (u,st2)` >> Cases_on `u` >>
  gnvs[Abbr `lower`, Abbr `upper_action`, Abbr `suffix_action`] >>
  drule_all scalar_conditional_assert_extends >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  Cases_on `i < -18707220957835557353007165858768422651595`
  >- (drule_all (SRULE[decimal_scale_def] scalar_int_decimal_lower_abort) >>
      strip_tac >>
      qpat_assum `(if _ then _ else _) st = _`
        (mp_then Any strip_assume_tac scalar_conditional_assert_extends) >>
      `emitted_insts st1 st' = emitted_insts st1 st2 ++ emitted_insts st2 st'` by
        (irule emitted_insts_append >> simp[]) >>
      `st'.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st'`
        by simp[] >>
      qspecl_then [`st`, `st1`, `st'`, `ss`] mp_tac run_inst_seq_chain_err >>
      simp[] >> metis_tac[]) >>
  `-18707220957835557353007165858768422651595 <= i` by intLib.ARITH_TAC >>
  `i > 18707220957835557353007165858768422651595` by intLib.ARITH_TAC >>
  drule_all (SRULE[decimal_scale_def] scalar_int_decimal_lower_ok) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) ss = OK s_lower` >>
  `eval_operand x s_lower = SOME (i2w i)` by metis_tac[] >>
  drule_all (SRULE[decimal_scale_def] scalar_int_decimal_signed_upper_abort) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) s_lower = Abort Revert_abort s_abort` >>
  `run_inst_seq (emitted_insts st st2) ss = Abort Revert_abort s_abort` by
    (irule scalar_run_suffix >> qexistsl_tac [`s_lower`, `st1`] >> simp[]) >>
  `emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2` by
    (irule emitted_insts_append >> simp[]) >>
  `st2.cs_current_insts = st.cs_current_insts ++ emitted_insts st st2` by simp[] >>
  qspecl_then [`st`, `st2`, `st'`, `ss`] mp_tac run_inst_seq_chain_err >>
  simp[] >> metis_tac[]
QED

Resume scalar_int_to_decimal_abort[unsigned]:
  `0 <= i` by (fs[within_int_bound_ineq]) >>
  `i > 18707220957835557353007165858768422651595` by intLib.ARITH_TAC >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp[compile_type_convert_def] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind lower rest st = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  simp[Abbr `lower`, comp_return_def] >>
  simp[Abbr `rest`] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind upper_action suffix_action st = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `upper_action st` >> simp[] >> strip_tac >>
  rename1 `upper_action st = (u,st1)` >> Cases_on `u` >>
  gnvs[Abbr `upper_action`, Abbr `suffix_action`] >>
  drule_all (SRULE[decimal_scale_def] scalar_int_decimal_unsigned_upper_abort) >>
  strip_tac >>
  drule_all scalar_conditional_assert_extends >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qspecl_then [`st`, `st1`, `st'`, `ss`] mp_tac run_inst_seq_chain_err >>
  simp[] >> metis_tac[]
QED

Finalise scalar_int_to_decimal_abort

Theorem scalar_decimal_lower_ok:
  !x l i st st' ss.
    within_int_bound decimal_bound i /\ l <= 0 /\ l * decimal_scale <= i /\
    (if -&(2 ** 167) < l * decimal_scale then
       do bad <- emit_op SLT [x; Lit (i2w (l * decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      fresh_vars_wrt st' ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st st' /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt strip_tac >>
  Cases_on `-&(2 ** 167) < l * decimal_scale`
  >- (drule_all scalar_decimal_scaled_lower_endpoint >> strip_tac >>
      `w2i (i2w i:bytes32) = i` by
        (irule w2i_i2w_within_signed >> qexists_tac `168` >> gvs[]) >>
      `w2i (i2w (l * decimal_scale):bytes32) = l * decimal_scale` by
        (irule w2i_i2w_within_signed >> qexists_tac `256` >> simp[]) >>
      `~word_lt (i2w i:bytes32) (i2w (l * decimal_scale))` by (gvs[WORD_LTi] >> intLib.ARITH_TAC) >>
      gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
      drule_all scalar_comparison_assert_extends >> strip_tac >>
      drule_all scalar_signed_lower_ok >> simp[]) >>
  gvs[comp_return_def, emitted_insts_refl, run_inst_seq_nil, same_blocks_def]
QED

Theorem scalar_decimal_upper_ok:
  !x h i st st' ss.
    within_int_bound decimal_bound i /\ 0 <= h /\ i <= h * decimal_scale /\
    (if &(2 ** 167) - 1 > h * decimal_scale then
       do bad <- emit_op SGT [x; Lit (i2w (h * decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      fresh_vars_wrt st' ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st st' /\
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt strip_tac >>
  Cases_on `&(2 ** 167) - 1 > h * decimal_scale`
  >- (`h * decimal_scale < &(2 ** 167) - 1` by intLib.ARITH_TAC >>
      drule_all scalar_decimal_scaled_upper_endpoint >> strip_tac >>
      `w2i (i2w i:bytes32) = i` by
        (irule w2i_i2w_within_signed >> qexists_tac `168` >> gvs[]) >>
      `w2i (i2w (h * decimal_scale):bytes32) = h * decimal_scale` by
        (irule w2i_i2w_within_signed >> qexists_tac `256` >> simp[]) >>
      `~word_gt (i2w i:bytes32) (i2w (h * decimal_scale))` by (gvs[WORD_GTi] >> intLib.ARITH_TAC) >>
      gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
      drule_all scalar_comparison_assert_extends >> strip_tac >>
      drule_all scalar_signed_upper_ok >> simp[]) >>
  gvs[comp_return_def, emitted_insts_refl, run_inst_seq_nil, same_blocks_def]
QED

Theorem scalar_decimal_lower_abort:
  !x l i st st' ss.
    within_int_bound decimal_bound i /\ l <= 0 /\ i < l * decimal_scale /\
    (if -&(2 ** 167) < l * decimal_scale then
       do bad <- emit_op SLT [x; Lit (i2w (l * decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `-&(2 ** 167) < l * decimal_scale` by
    (gvs[within_int_bound_def] >> intLib.ARITH_TAC) >>
  drule_all scalar_decimal_scaled_lower_endpoint >> strip_tac >>
  `w2i (i2w i:bytes32) = i` by
    (irule w2i_i2w_within_signed >> qexists_tac `168` >> gvs[]) >>
  `w2i (i2w (l * decimal_scale):bytes32) = l * decimal_scale` by
    (irule w2i_i2w_within_signed >> qexists_tac `256` >> simp[]) >>
  `word_lt (i2w i:bytes32) (i2w (l * decimal_scale))` by
    (gvs[WORD_LTi] >> intLib.ARITH_TAC) >>
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all scalar_signed_lower_abort >> simp[]
QED

Theorem scalar_decimal_upper_abort:
  !x h i st st' ss.
    within_int_bound decimal_bound i /\ 0 <= h /\ i > h * decimal_scale /\
    (if &(2 ** 167) - 1 > h * decimal_scale then
       do bad <- emit_op SGT [x; Lit (i2w (h * decimal_scale))];
          ok <- emit_op ISZERO [bad]; emit_void ASSERT [ok] od
     else return ()) st = ((),st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `h * decimal_scale < &(2 ** 167) - 1` by
    (gvs[within_int_bound_def] >> intLib.ARITH_TAC) >>
  `&(2 ** 167) - 1 > h * decimal_scale` by intLib.ARITH_TAC >>
  drule_all scalar_decimal_scaled_upper_endpoint >> strip_tac >>
  `w2i (i2w i:bytes32) = i` by
    (irule w2i_i2w_within_signed >> qexists_tac `168` >> gvs[]) >>
  `w2i (i2w (h * decimal_scale):bytes32) = h * decimal_scale` by
    (irule w2i_i2w_within_signed >> qexists_tac `256` >> simp[]) >>
  `word_gt (i2w i:bytes32) (i2w (h * decimal_scale))` by
    (gvs[WORD_GTi] >> intLib.ARITH_TAC) >>
  gvs[comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  drule_all scalar_signed_upper_abort >> simp[]
QED

Theorem scalar_decimal_to_int_ok:
  !lo hi i x op st st' ss.
    within_int_bound decimal_bound i /\ lo <= 0 /\ 0 <= hi /\
    lo * decimal_scale <= i /\ i <= hi * decimal_scale /\
    compile_type_convert x
      (ConvDecimalToInt 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1) lo hi T)
      st = (op,st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (i2w (i quot decimal_scale))
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp[compile_type_convert_def] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind lower rest st = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `lower st` >> simp[] >> strip_tac >>
  rename1 `lower st = (u,st1)` >> Cases_on `u` >>
  gvs[Abbr `lower`] >>
  drule_all (SRULE[decimal_scale_def] scalar_decimal_lower_ok) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) ss = OK s_lower` >>
  qpat_x_assum `rest st1 = _` mp_tac >> simp[Abbr `rest`] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind upper_action suffix_action st1 = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `upper_action st1` >> simp[] >> strip_tac >>
  rename1 `upper_action st1 = (u,st2)` >> Cases_on `u` >>
  gvs[Abbr `upper_action`, Abbr `suffix_action`] >>
  `eval_operand x s_lower = SOME (i2w i)` by metis_tac[] >>
  drule_all (SRULE[decimal_scale_def] scalar_decimal_upper_ok) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) s_lower = OK s_upper` >>
  `eval_operand x s_upper = SOME (i2w i)` by metis_tac[] >>
  `eval_operand (Lit 0x2540BE400w) s_upper = SOME 0x2540BE400w`
    by simp[eval_operand_def] >>
  drule_all emit_op_SDIV_correct >> strip_tac >>
  rename1 `eval_operand op s_result = SOME _` >>
  drule emit_op_extends >> strip_tac >>
  qexists_tac `s_result` >> conj_tac
  >- (irule scalar_run_suffix >> qexistsl_tac [`s_upper`, `st2`] >>
      simp[] >> conj_tac
      >- (irule scalar_run_suffix >> qexistsl_tac [`s_lower`, `st1`] >> simp[]) >>
      sym_tac >> irule emitted_insts_append >> simp[]) >>
  drule (SRULE[decimal_scale_def] scalar_decimal_sdiv) >> simp[]
QED

Theorem scalar_decimal_to_int_abort:
  !lo hi i x op st st' ss.
    within_int_bound decimal_bound i /\ lo <= 0 /\ 0 <= hi /\
    ~(lo * decimal_scale <= i /\ i <= hi * decimal_scale) /\
    compile_type_convert x
      (ConvDecimalToInt 10000000000 (-&(2 ** 167)) (&(2 ** 167)-1) lo hi T)
      st = (op,st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp[compile_type_convert_def] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind lower rest st = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `lower st` >> simp[] >> strip_tac >>
  rename1 `lower st = (u,st1)` >> Cases_on `u` >>
  qpat_x_assum `rest st1 = _` mp_tac >> simp[Abbr `rest`] >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind upper_action suffix_action st1 = (op,st')` >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `upper_action st1` >> simp[] >> strip_tac >>
  rename1 `upper_action st1 = (u,st2)` >> Cases_on `u` >>
  gnvs[Abbr `lower`, Abbr `upper_action`, Abbr `suffix_action`] >>
  drule_all scalar_conditional_assert_extends >> strip_tac >>
  qpat_assum `emit_op SDIV _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  Cases_on `i < lo * 10000000000`
  >- suspend "lower"
  >> suspend "upper"
QED

Resume scalar_decimal_to_int_abort[lower]:
  drule_all (SRULE[decimal_scale_def] scalar_decimal_lower_abort) >> strip_tac >>
  qpat_assum `(if _ then _ else _) st = _`
    (mp_then Any strip_assume_tac scalar_conditional_assert_extends) >>
  `emitted_insts st1 st' = emitted_insts st1 st2 ++ emitted_insts st2 st'` by
    (irule emitted_insts_append >> simp[]) >>
  `st'.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st'` by simp[] >>
  qspecl_then [`st`, `st1`, `st'`, `ss`] mp_tac run_inst_seq_chain_err >>
  simp[] >> metis_tac[]
QED

Resume scalar_decimal_to_int_abort[upper]:
  `lo * 10000000000 <= i` by intLib.ARITH_TAC >>
  `i > hi * 10000000000` by (gvs[] >> intLib.ARITH_TAC) >>
  drule_all (SRULE[decimal_scale_def] scalar_decimal_lower_ok) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st1) ss = OK s_lower` >>
  `eval_operand x s_lower = SOME (i2w i)` by metis_tac[] >>
  drule_all (SRULE[decimal_scale_def] scalar_decimal_upper_abort) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) s_lower = Abort Revert_abort s_abort` >>
  `run_inst_seq (emitted_insts st st2) ss = Abort Revert_abort s_abort` by
    (irule scalar_run_suffix >> qexistsl_tac [`s_lower`, `st1`] >> simp[]) >>
  `emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2` by
    (irule emitted_insts_append >> simp[]) >>
  `st2.cs_current_insts = st.cs_current_insts ++ emitted_insts st st2` by simp[] >>
  qspecl_then [`st`, `st2`, `st'`, `ss`] mp_tac run_inst_seq_chain_err >>
  simp[] >> metis_tac[]
QED

Finalise scalar_decimal_to_int_abort
