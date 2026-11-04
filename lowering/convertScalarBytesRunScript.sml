Theory convertScalarBytesRun
Ancestors
  convertScalarEncoding convertScalarChecks exprSimConvert arithmeticProps exprLowering
  exprLoweringProps emitHelperProps compileEnv vyperArith vyperValue
  integer integer_word words venomState valueEncoding byte vyperValueOperation moduleLoweringProps
Libs
  intLib

Theorem scalar_int_clamp_eq:
  !sg b x.
    compile_int_clamp sg b x =
      clamp_and_return x (if sg then BaseT (IntT b) else BaseT (UintT b))
Proof
  Cases >> simp[compile_int_clamp_def, clamp_and_return_def,
    compile_clamp_def, type_bounds_def, type_bits_def, is_signed_type_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, FUN_EQ_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[])
QED

Theorem scalar_int_clamp_word_ok:
  !sg b x st op st' ss w.
    compile_int_clamp sg b x st = (op,st') /\
    eval_operand x ss = SOME w /\ fresh_vars_wrt st ss /\
    in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
      (if sg then w2i w else &(w2n w)) /\ b <= 256 ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME w
Proof
  rpt strip_tac >>
  irule clamp_and_return_ok >>
  qexistsl_tac [`st`, `x`, `ss`,
    `if sg then BaseT (IntT b) else BaseT (UintT b)`] >>
  gvs[scalar_int_clamp_eq, emitted_insts_def, run_inst_seq_def] >>
  Cases_on `sg` >> gvs[math_val_def, is_signed_type_def, type_bits_def]
QED

Theorem scalar_int_clamp_word_abort:
  !sg b x st op st' ss w.
    compile_int_clamp sg b x st = (op,st') /\
    eval_operand x ss = SOME w /\ fresh_vars_wrt st ss /\
    ~in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
      (if sg then w2i w else &(w2n w)) /\ b <= 256 ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  irule clamp_and_return_out_of_range >>
  qexistsl_tac [`st`, `op`, `x`, `ss`,
    `if sg then BaseT (IntT b) else BaseT (UintT b)`, `w`] >>
  gvs[scalar_int_clamp_eq, emitted_insts_def, run_inst_seq_def] >>
  Cases_on `sg` >> gvs[math_val_def, is_signed_type_def, type_bits_def]
QED

Theorem scalar_emit_shift:
  !sg a x st op st' ss k w.
    emit_op (if sg then SAR else SHR) [a;x] st = (op,st') /\
    eval_operand a ss = SOME k /\ eval_operand x ss = SOME w /\
    fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (if sg then w >> w2n k else w >>> w2n k) /\
      fresh_vars_wrt st' ss'
Proof
  rpt strip_tac >> Cases_on `sg` >> gvs[]
  >- (qspecl_then [`SAR`, `\k w. w >> w2n k`]
        (mp_tac o BETA_RULE) emit_op_pure2_correct >>
      disch_then drule >>
      disch_then (qspecl_then [`k`,`w`,`ss`] mp_tac) >>
      (impl_tac >- (simp[] >> irule step_SAR >> simp[])) >>
      metis_tac[]) >>
  drule_all emit_op_SHR_correct >> metis_tac[]
QED

Theorem scalar_bytes_int_word_ok:
  !sg m b x st op st' ss w.
    compile_type_convert x (ConvBytesToInt m sg b) st = (op,st') /\
    eval_operand x ss = SOME w /\ fresh_vars_wrt st ss /\
    in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
      (if sg then w2i (w >> w2n (n2w ((32-m)*8):bytes32))
       else &(w2n (w >>> w2n (n2w ((32-m)*8):bytes32)))) /\ b <= 256 ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME
        (if sg then w >> w2n (n2w ((32-m)*8):bytes32)
         else w >>> w2n (n2w ((32-m)*8):bytes32))
Proof
  rpt strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rename1 `(if sg then emit_op SAR _ else emit_op SHR _) st = (shifted,mid)` >>
  `emit_op (if sg then SAR else SHR) [Lit (n2w ((32-m)*8));x] st =
     (shifted,mid)` by (Cases_on `sg` >> gvs[]) >>
  `?ss1. run_inst_seq (emitted_insts st mid) ss = OK ss1 /\
     eval_operand shifted ss1 = SOME
       (if sg then w >> w2n (n2w ((32-m)*8):bytes32)
        else w >>> w2n (n2w ((32-m)*8):bytes32)) /\
     fresh_vars_wrt mid ss1` by
    (irule scalar_emit_shift >> simp[] >>
     qexistsl_tac [`Lit (n2w ((32-m)*8))`, `x`] >>
     simp[eval_operand_def, arithmeticTheory.MULT_COMM]) >>
  qmatch_asmsub_abbrev_tac `eval_operand shifted ss1 = SOME sw` >>
  `in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
    (if sg then w2i sw else &(w2n sw))` by
      (Cases_on `sg` >> gvs[Abbr `sw`]) >>
  Cases_on `m*8 > b`
  >- (gvs[] >> drule_all scalar_int_clamp_word_ok >> strip_tac >>
      imp_res_tac emit_op_extends >>
      `st'.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid st'` by
        (irule (cj 1 clamp_and_return_extends) >>
         qexistsl_tac [`op`, `shifted`,
           `if sg then BaseT (IntT b) else BaseT (UintT b)`] >>
         simp[GSYM scalar_int_clamp_eq]) >>
      drule_all scalar_run_suffix >> metis_tac[]) >>
  gvs[comp_return_def]
QED

Theorem scalar_bytes_int_word_abort:
  !sg m b x st op st' ss w.
    compile_type_convert x (ConvBytesToInt m sg b) st = (op,st') /\
    eval_operand x ss = SOME w /\ fresh_vars_wrt st ss /\ m*8 > b /\
    ~in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
      (if sg then w2i (w >> w2n (n2w ((32-m)*8):bytes32))
       else &(w2n (w >>> w2n (n2w ((32-m)*8):bytes32)))) /\ b <= 256 ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rename1 `(if sg then emit_op SAR _ else emit_op SHR _) st = (shifted,mid)` >>
  `emit_op (if sg then SAR else SHR) [Lit (n2w ((32-m)*8));x] st =
     (shifted,mid)` by (Cases_on `sg` >> gvs[]) >>
  `?ss1. run_inst_seq (emitted_insts st mid) ss = OK ss1 /\
     eval_operand shifted ss1 = SOME
       (if sg then w >> w2n (n2w ((32-m)*8):bytes32)
        else w >>> w2n (n2w ((32-m)*8):bytes32)) /\
     fresh_vars_wrt mid ss1` by
    (irule scalar_emit_shift >> simp[] >>
     qexistsl_tac [`Lit (n2w ((32-m)*8))`, `x`] >>
     simp[eval_operand_def, arithmeticTheory.MULT_COMM]) >>
  qmatch_asmsub_abbrev_tac `eval_operand shifted ss1 = SOME sw` >>
  `~in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
    (if sg then w2i sw else &(w2n sw))` by
      (Cases_on `sg` >> gvs[Abbr `sw`]) >>
  drule_all scalar_int_clamp_word_abort >> strip_tac >>
  imp_res_tac emit_op_extends >>
  `st'.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid st'` by
    (irule (cj 1 clamp_and_return_extends) >>
     qexistsl_tac [`op`, `shifted`,
       `if sg then BaseT (IntT b) else BaseT (UintT b)`] >>
     simp[GSYM scalar_int_clamp_eq]) >>
  drule_all scalar_run_suffix >> metis_tac[]
QED

Theorem scalar_signed_mod_bound:
  !b i. 0 < b ==> within_int_bound (Signed b) (signed_int_mod b i)
Proof
  rpt strip_tac >>
  simp[within_int_bound_ineq, vyperValueOperationTheory.signed_int_mod_def, LET_THM] >>
  `2 ** b = 2 * 2 ** (b - 1)` by
    (`b = SUC (b - 1)` by simp[] >> pop_assum SUBST1_TAC >> simp[arithmeticTheory.EXP]) >>
  `0i < &(2 ** b)` by simp[] >>
  `&(2 ** b) <> 0i` by simp[] >>
  drule integerTheory.INT_MOD_BOUNDS >>
  disch_then (qspec_then `i` strip_assume_tac) >>
  qabbrev_tac `r = i % &(2 ** b)` >>
  Cases_on `r >= &(2 ** (b - 1))` >> simp[] >>
  qpat_x_assum `Abbrev _` kall_tac >>
  `~(&(2 ** b) < 0i)` by simp[] >> fs[] >>
  qpat_x_assum `2 ** b = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE[th, GSYM integerTheory.INT_MUL]) >>
    PURE_REWRITE_TAC[th, GSYM integerTheory.INT_MUL]) >>
  intLib.ARITH_TAC
QED

Theorem scalar_int_bound_mono:
  !sg a b i. 0 < a /\ a <= b /\
    within_int_bound (if sg then Signed a else Unsigned a) i ==>
    within_int_bound (if sg then Signed b else Unsigned b) i
Proof
  rpt strip_tac >>
  Cases_on `sg` >> gvs[within_int_bound_ineq] >>
  `&(2 ** a) <= &(2 ** b):int` by simp[] >>
  `&(2 ** (a-1)) <= &(2 ** (b-1)):int` by simp[] >>
  intLib.ARITH_TAC
QED

Theorem scalar_int_range:
  !sg b i. 0 < b ==>
    (in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b)) i <=>
    within_int_bound (if sg then Signed b else Unsigned b) i)
Proof
  Cases >> rpt strip_tac >>
  simp[in_type_range_def, type_bits_def, is_signed_type_def,
    within_int_bound_ineq, GSYM integerTheory.INT_SUB] >> intLib.ARITH_TAC
QED

Theorem scalar_bytes_shift_value:
  !sg m bs. LENGTH bs = m /\ m <= 32 ==>
    (if sg then
       typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >>
         w2n (n2w ((32-m)*8):bytes32)
     else
       typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >>>
         w2n (n2w ((32-m)*8):bytes32)) =
    i2w (if sg then
       w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >> (8*(32-m)))
     else &(w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)))
Proof
  rpt strip_tac >>
  `((32-m)*8) < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  simp[w2n_n2w, arithmeticTheory.MULT_COMM] >>
  Cases_on `sg` >> simp[i2w_w2i, i2w_pos] >>
  simp[typed_val_to_w256_def] >>
  metis_tac[scalar_fixed_shr]
QED

Theorem scalar_bytes_signed_bound:
  !bs m. LENGTH bs = m /\ 0 < m /\ m <= 32 ==>
    within_int_bound (Signed (8*m))
      (w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >> (8*(32-m))))
Proof
  rpt strip_tac >>
  `0 < 8*m /\ 8*m <= 256` by decide_tac >>
  `within_int_bound (Signed (8*m))
     (signed_int_mod (8*m) (&(num_of_bytes (REVERSE bs))))` by
    (irule scalar_signed_mod_bound >> simp[]) >>
  `w2i (i2w (signed_int_mod (8*m) (&(num_of_bytes (REVERSE bs)))):bytes32) =
     signed_int_mod (8*m) (&(num_of_bytes (REVERSE bs)))` by
    (irule w2i_i2w_within_signed >> metis_tac[]) >>
  gvs[typed_val_to_w256_def, scalar_fixed_sar]
QED

Theorem scalar_bytes_unsigned_bound:
  !bs m. LENGTH bs = m /\ m <= 32 ==>
    0 <= &(w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)) /\
    &(w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)) < &(2 ** (8*m))
Proof
  rpt strip_tac >> simp[scalar_address_encoding_num, w2n_n2w] >>
  qspec_then `REVERSE bs` mp_tac num_of_bytes_lt >>
  simp[arithmeticTheory.EXP_EXP_MULT] >>
  strip_tac >> irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
  qexists_tac `num_of_bytes (REVERSE bs)` >> simp[arithmeticTheory.MOD_LESS_EQ]
QED

Theorem scalar_bytes_shift_math:
  !sg m bs sw i.
    LENGTH bs = m /\ m <= 32 /\
    sw = (if sg then
       typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >>
         w2n (n2w ((32-m)*8):bytes32)
     else
       typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >>>
         w2n (n2w ((32-m)*8):bytes32)) /\
    i = (if sg then
       w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >> (8*(32-m)))
     else &(w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32))) ==>
    (if sg then w2i sw else &(w2n sw)) = i
Proof
  rpt strip_tac >>
  `((32-m)*8) < dimword (:256)` by
    (simp[dimword_def] >> decide_tac) >>
  Cases_on `sg` >> gvs[w2n_n2w, arithmeticTheory.MULT_COMM] >>
  simp[typed_val_to_w256_def] >> metis_tac[scalar_fixed_shr]
QED

Theorem scalar_bytes_int_run_ok:
  !sg m b bs i x st op st' ss.
    LENGTH bs = m /\ m <= 32 /\ (sg ==> 0 < m) /\
    0 < b /\ (sg ==> 1 < b) /\ b <= 256 /\
    i = (if sg then
       w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >> (8*(32-m)))
     else &(w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32))) /\
    compile_type_convert x (ConvBytesToInt m sg b) st = (op,st') /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
    fresh_vars_wrt st ss /\ within_int_bound (if sg then Signed b else Unsigned b) i ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (i2w i)
Proof
  rpt strip_tac >>
  drule scalar_bytes_int_word_ok >>
  disch_then (qspecl_then [`ss`, `typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)`] mp_tac) >>
  impl_tac
  >- (simp[scalar_int_range] >>
      qabbrev_tac `sw = if sg then
        typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >>
          w2n (n2w ((32-m)*8):bytes32)
        else typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >>>
          w2n (n2w ((32-m)*8):bytes32)` >>
      `(if sg then w2i sw else &(w2n sw)) = i` by
        (irule scalar_bytes_shift_math >>
         qexistsl_tac [`bs`, `m`] >> simp[Abbr `sw`]) >>
      qpat_x_assum `i = _` kall_tac >>
      qpat_x_assum `(if sg then w2i sw else _) = i` mp_tac >>
      simp[Abbr `sw`, COND_RAND] >> metis_tac[]) >>
  strip_tac >>
  drule_all scalar_bytes_shift_value >> strip_tac >> gvs[]
QED

Theorem scalar_bytes_int_omitted_bound:
  !sg m b bs i.
    LENGTH bs = m /\ m <= 32 /\ (sg ==> 0 < m) /\
    0 < b /\ m*8 <= b /\
    i = (if sg then
       w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >> (8*(32-m)))
     else &(w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32))) ==>
    within_int_bound (if sg then Signed b else Unsigned b) i
Proof
  rpt strip_tac >> Cases_on `sg` >> gvs[]
  >- (qspec_then `bs` mp_tac scalar_bytes_signed_bound >>
      simp[] >> strip_tac >>
      irule (SRULE[] (Q.SPEC `T` scalar_int_bound_mono)) >>
      qexists_tac `8*LENGTH bs` >> simp[]) >>
  qspec_then `bs` mp_tac scalar_bytes_unsigned_bound >> simp[] >> strip_tac >>
  simp[within_int_bound_ineq] >>
  `&(2 ** (8*LENGTH bs)) <= &(2 ** b):int` by simp[] >>
  intLib.ARITH_TAC
QED

Theorem scalar_bytes_int_run_abort:
  !sg m b bs i x st op st' ss.
    LENGTH bs = m /\ m <= 32 /\ (sg ==> 0 < m) /\
    0 < b /\ (sg ==> 1 < b) /\ b <= 256 /\
    i = (if sg then
       w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >> (8*(32-m)))
     else &(w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32))) /\
    compile_type_convert x (ConvBytesToInt m sg b) st = (op,st') /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
    fresh_vars_wrt st ss /\ ~within_int_bound (if sg then Signed b else Unsigned b) i ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `m*8 > b` by
    (Cases_on `m*8 > b` >> simp[] >>
     `m*8 <= b` by decide_tac >>
     drule_all scalar_bytes_int_omitted_bound >> simp[]) >>
  drule scalar_bytes_int_word_abort >>
  disch_then (qspecl_then [`ss`, `typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)`] mp_tac) >>
  impl_tac
  >- (simp[scalar_int_range] >>
      qabbrev_tac `sw = if sg then
        typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >>
          w2n (n2w ((32-m)*8):bytes32)
        else typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >>>
          w2n (n2w ((32-m)*8):bytes32)` >>
      `(if sg then w2i sw else &(w2n sw)) = i` by
        (irule scalar_bytes_shift_math >>
         qexistsl_tac [`bs`, `m`] >> simp[Abbr `sw`]) >>
      qpat_x_assum `i = _` kall_tac >>
      qpat_x_assum `(if sg then w2i sw else _) = i` mp_tac >>
      simp[Abbr `sw`, COND_RAND] >> metis_tac[]) >>
  simp[]
QED

Theorem scalar_bytes_address_eq:
  !m x. compile_type_convert x (ConvBytesToAddress m) =
    compile_type_convert x (ConvBytesToInt m F 160)
Proof
  simp[compile_type_convert_def, compile_int_clamp_def]
QED

Theorem scalar_bytes_address_run_ok:
  !m bs u x st op st' ss.
    LENGTH bs = m /\ m <= 32 /\
    u = w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32) /\
    compile_type_convert x (ConvBytesToAddress m) st = (op,st') /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
    fresh_vars_wrt st ss /\ u < 2 ** 160 ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (n2w u)
Proof
  rpt strip_tac >>
  mp_tac (SRULE[within_int_bound_ineq, i2w_pos]
    (Q.SPECL [`F`, `m`, `160`, `bs`, `&u`] scalar_bytes_int_run_ok)) >>
  simp[GSYM scalar_bytes_address_eq] >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `ss` mp_tac) >> gvs[]
QED

Theorem scalar_bytes_address_run_abort:
  !m bs u x st op st' ss.
    LENGTH bs = m /\ m <= 32 /\
    u = w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32) /\
    compile_type_convert x (ConvBytesToAddress m) st = (op,st') /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
    fresh_vars_wrt st ss /\ ~(u < 2 ** 160) ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  mp_tac (SRULE[within_int_bound_ineq]
    (Q.SPECL [`F`, `m`, `160`, `bs`, `&u`] scalar_bytes_int_run_abort)) >>
  simp[GSYM scalar_bytes_address_eq] >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `ss` mp_tac) >> gvs[]
QED

Theorem scalar_bytes_decimal_eq:
  !m divisor x.
    compile_type_convert x
      (ConvBytesMToDecimal m divisor (-&(2**167)) (&(2**167)-1)) =
    compile_type_convert x (ConvBytesToInt m T 168)
Proof
  simp[compile_type_convert_def, compile_int_clamp_def,
    GSYM integerTheory.INT_SUB]
QED

Theorem scalar_bytes_decimal_run_ok:
  !m divisor bs i x st op st' ss.
    LENGTH bs = m /\ 0 < m /\ m <= 32 /\
    i = w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >> (8*(32-m))) /\
    compile_type_convert x
      (ConvBytesMToDecimal m divisor (-&(2**167)) (&(2**167)-1)) st = (op,st') /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
    fresh_vars_wrt st ss /\ within_int_bound decimal_bound i ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (i2w i)
Proof
  rpt strip_tac >>
  fs[scalar_bytes_decimal_eq, decimal_bits_def] >>
  mp_tac (SRULE[]
    (Q.SPECL [`T`, `m`, `168`, `bs`, `i`] scalar_bytes_int_run_ok)) >>
  simp[] >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `ss` mp_tac) >> gvs[decimal_bits_def]
QED

Theorem scalar_bytes_decimal_run_abort:
  !m divisor bs i x st op st' ss.
    LENGTH bs = m /\ 0 < m /\ m <= 32 /\
    i = w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) >> (8*(32-m))) /\
    compile_type_convert x
      (ConvBytesMToDecimal m divisor (-&(2**167)) (&(2**167)-1)) st = (op,st') /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
    fresh_vars_wrt st ss /\ ~within_int_bound decimal_bound i ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  fs[scalar_bytes_decimal_eq, decimal_bits_def] >>
  mp_tac (SRULE[]
    (Q.SPECL [`T`, `m`, `168`, `bs`, `i`] scalar_bytes_int_run_abort)) >>
  simp[] >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `ss` mp_tac) >> gvs[decimal_bits_def]
QED

Theorem scalar_bytes_narrow_run_ok:
  !m n bs x st op st' ss.
    LENGTH bs = m /\ n < m /\ m <= 32 /\
    compile_type_convert x (ConvBytesMToBytesM m n) st = (op,st') /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
    fresh_vars_wrt st ss /\ EVERY (\b. b = 0w) (DROP n bs) ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))
Proof
  rpt strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  `eval_operand (Lit (n2w (n*8))) ss = SOME (n2w (n*8))` by
    simp[eval_operand_def] >>
  qspecl_then [`SHL`, `\k w. w << w2n k`]
    (mp_tac o BETA_RULE) emit_op_pure2_correct >>
  disch_then drule >>
  disch_then (qspecl_then [`n2w (n*8)`,
    `typed_val_to_w256 (BaseTV (BytesT (Fixed (LENGTH bs)))) (BytesV bs)`, `ss`] mp_tac) >>
  (impl_tac >- simp[step_SHL, eval_operand_def]) >> strip_tac >>
  rename1 `eval_operand truncated s_shifted = SOME _` >>
  `n*8 < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `(word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) << (8*n) = 0w` by
    (irule (iffRL (Q.SPECL [`bs`, `n`] scalar_fixed_narrow_test)) >> simp[]) >>
  `w2n (n2w (n*8):bytes32) = 8*n` by simp[w2n_n2w] >>
  `typed_val_to_w256 (BaseTV (BytesT (Fixed (LENGTH bs)))) (BytesV bs) =
    word_of_bytes_be (PAD_RIGHT 0w 32 bs)` by rewrite_tac[typed_val_to_w256_def] >>
  `eval_operand truncated s_shifted = SOME 0w` by
    (qpat_x_assum `eval_operand truncated _ = _` mp_tac >>
     asm_rewrite_tac[]) >>
  drule_all scalar_assert_zero_ok >> strip_tac >>
  drule_all scalar_assert_zero_extends >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all scalar_run_suffix >> metis_tac[]
QED

Theorem scalar_bytes_narrow_run_abort:
  !m n bs x st op st' ss.
    LENGTH bs = m /\ n < m /\ m <= 32 /\
    compile_type_convert x (ConvBytesMToBytesM m n) st = (op,st') /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
    fresh_vars_wrt st ss /\ ~EVERY (\b. b = 0w) (DROP n bs) ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  `eval_operand (Lit (n2w (n*8))) ss = SOME (n2w (n*8))` by
    simp[eval_operand_def] >>
  qspecl_then [`SHL`, `\k w. w << w2n k`]
    (mp_tac o BETA_RULE) emit_op_pure2_correct >>
  disch_then drule >>
  disch_then (qspecl_then [`n2w (n*8)`,
    `typed_val_to_w256 (BaseTV (BytesT (Fixed (LENGTH bs)))) (BytesV bs)`, `ss`] mp_tac) >>
  (impl_tac >- simp[step_SHL, eval_operand_def]) >> strip_tac >>
  rename1 `eval_operand truncated s_shifted = SOME _` >>
  `n*8 < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `(word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) << (8*n) <> 0w` by
    (mp_tac (Q.SPECL [`bs`, `n`] scalar_fixed_narrow_test) >> simp[]) >>
  `w2n (n2w (n*8):bytes32) = 8*n` by simp[w2n_n2w] >>
  `typed_val_to_w256 (BaseTV (BytesT (Fixed (LENGTH bs)))) (BytesV bs) =
    word_of_bytes_be (PAD_RIGHT 0w 32 bs)` by rewrite_tac[typed_val_to_w256_def] >>
  `eval_operand truncated s_shifted = SOME
    ((word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) << (8*n))` by
    (qpat_x_assum `eval_operand truncated _ = _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all scalar_assert_zero_abort >> strip_tac >>
  drule_all scalar_assert_zero_extends >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all scalar_run_suffix >> metis_tac[]
QED
