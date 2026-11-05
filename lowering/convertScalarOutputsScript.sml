Theory convertScalarOutputs
Ancestors
  exprUnopStraight
  convertScalarBytes convertScalarBytesRun convertScalarEncoding convertScalarProps exprSimConvert exprSimUnop
  exprLowering compileEnv vyperValue valueEncoding vyperValueOperation
  exprLoweringProps emitHelperProps emitHelper venomExecSemantics
  arithmetic words integer_word list venomState venomInst exprSimArith arithmeticProps
Libs
  pairLib

Theorem scalar_emit_SHL_correct:
  !op1 op2 v1 v2 st v st' ss.
    emit_op SHL [op1; op2] st = (v, st') /\
    eval_operand op1 ss = SOME v1 /\ eval_operand op2 ss = SOME v2 /\
    fresh_vars_wrt st ss ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand v ss' = SOME (word_lsl v2 (w2n v1)) /\
      same_blocks st st' /\ fresh_vars_wrt st' ss' /\
      (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
      (!a. a < LENGTH ss.vs_memory ==> EL a ss'.vs_memory = EL a ss.vs_memory) /\
      LENGTH ss'.vs_memory = LENGTH ss.vs_memory
Proof
  rpt strip_tac >>
  qspecl_then [`SHL`, `\x y. y << w2n x`] (mp_tac o BETA_RULE)
    emit_op_pure2_correct >>
  disch_then irule >>
  simp[] >> qexistsl_tac [`op1`, `op2`] >> simp[] >>
  irule step_SHL >> simp[]
QED

Theorem scalar_int_bytes_run:
  !x sg bits m w sa op sb ss.
    bits <= 8 * m /\ m <= 32 /\
    compile_type_convert x (ConvIntToBytesM sg bits m) sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME w ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
          eval_operand op ss' = SOME (w << (8 * (32-m)))
Proof
  rpt strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_return_def, LET_THM] >>
  drule scalar_emit_SHL_correct >>
  disch_then (qspecl_then [`n2w (8*(32-m))`, `w`, `ss`] mp_tac) >>
  simp[eval_operand_def, dimword_def] >>
  `8 * (32-m) < 2 ** 256` by simp[] >>
  fs[] >> metis_tac[]
QED

Theorem scalar_int_bytes_result_frag:
  !ctx func cenv cx sg bits m i es0.
    bits <= 8*m /\ m <= 32 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM sg bits m))
      (i2w i) (BaseT (BytesT (Fixed m)))
      (convert_result cx (BaseT (if sg then IntT bits else UintT bits))
        (BaseT (BytesT (Fixed m))) (IntV i)) es0
Proof
  rpt strip_tac >> Cases_on `sg` >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >> strip_tac >>
  qexists_tac `(i2w i:bytes32) << (8*(32-m))` >>
  simp[evaluate_type_def, scalar_word_to_fixed] >>
  rpt strip_tac >> drule_all scalar_int_bytes_run >> simp[]
QED

Theorem scalar_address_bytes_result_frag:
  !ctx func cenv cx bs m es0.
    LENGTH bs = 20 /\ 20 <= m /\ m <= 32 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM F 160 m))
      (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
      (BaseT (BytesT (Fixed m)))
      (convert_result cx (BaseT AddressT)
        (BaseT (BytesT (Fixed m))) (BytesV bs)) es0
Proof
  rpt strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >> strip_tac >>
  qexists_tac `typed_val_to_w256 (BaseTV AddressT) (BytesV bs) << (8*(32-m))` >>
  simp[evaluate_type_def, scalar_address_to_fixed] >>
  rpt strip_tac >> irule scalar_int_bytes_run >> simp[] >>
  qexistsl_tac [`160`, `F`, `x`] >> simp[]
QED

Theorem scalar_flag_bytes_result_frag:
  !ctx func cenv cx nsid k m es0.
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM F 256 32))
      (typed_val_to_w256 (FlagTV k) (FlagV m))
      (BaseT (BytesT (Fixed 32)))
      (convert_result cx (FlagT nsid)
        (BaseT (BytesT (Fixed 32))) (FlagV m)) es0
Proof
  rpt strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >> strip_tac >>
  qexists_tac `typed_val_to_w256 (FlagTV k) (FlagV m)` >>
  simp[evaluate_type_def, scalar_flag_to_bytes32] >>
  rpt strip_tac >>
  qspecl_then [`x`, `F`, `256`, `32`] mp_tac scalar_int_bytes_run >>
  simp[] >> disch_then drule_all >>
  `!w:bytes32. w << 0 = w` by wordsLib.WORD_DECIDE_TAC >> simp[]
QED

Theorem scalar_address_uint_result_frag:
  !ctx func cenv cx bs b es0.
    LENGTH bs = 20 /\ 0 < b /\ b <= 256 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToInt F 160 F b))
      (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
      (BaseT (UintT b))
      (convert_result cx (BaseT AddressT) (BaseT (UintT b)) (BytesV bs)) es0
Proof
  rpt strip_tac >>
  `within_int_bound (Unsigned 160)
    (&w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32))` by
    (drule scalar_bytes_unsigned_bound >> simp[within_int_bound_ineq]) >>
  qabbrev_tac `i:int = &w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)` >>
  `typed_val_to_w256 (BaseTV AddressT) (BytesV bs) = i2w i` by
    simp[Abbr `i`, typed_val_to_w256_def, i2w_pos] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert, is_word_type_def] >>
  Cases_on `within_int_bound (Unsigned b) i` >> simp[]
  >- (strip_tac >> qexists_tac `i2w i` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >> drule convert_int_run >>
      disch_then (qspecl_then [`i`, `ss`] mp_tac) >> simp[]) >>
  strip_tac >> rpt strip_tac >> drule convert_int_run >>
  disch_then (qspecl_then [`i`, `ss`] mp_tac) >> simp[]
QED

Theorem scalar_address_word_range:
  !i. -&(2**255) <= i /\ i < &(2**256) ==>
    (within_int_bound (Unsigned 160) (&w2n (i2w i:bytes32)) <=>
     within_int_bound (Unsigned 160) i)
Proof
  rpt strip_tac >>
  `(&w2n (i2w i:bytes32):int) = i % &(2**256)` by
    simp[w2n_i2w, dimword_def] >>
  asm_rewrite_tac[] >>
  simp[within_int_bound_ineq] >>
  Cases_on `0 <= i`
  >- (fs[integerTheory.INT_MOD_ID] >> intLib.ARITH_TAC) >>
  `i % &(2**256) = i + &(2**256)` by
    (irule integerTheory.INT_MOD_UNIQUE >>
     qexists_tac `-1` >> fs[] >> intLib.ARITH_TAC) >>
  fs[] >> intLib.ARITH_TAC
QED

Theorem scalar_to_address_clamp:
  !x. compile_type_convert x ConvToAddress = compile_int_clamp F 160 x
Proof
  simp[compile_type_convert_def, compile_int_clamp_def]
QED

Theorem scalar_int_address_run_ok:
  !x st op st' ss i.
    compile_type_convert x ConvToAddress st = (op,st') /\
    fresh_vars_wrt st ss /\ eval_operand x ss = SOME (i2w i) /\
    within_int_bound (Unsigned 160) i ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (i2w i)
Proof
  rpt strip_tac >>
  gvs[scalar_to_address_clamp] >>
  irule scalar_int_clamp_word_ok >> simp[] >>
  qexistsl_tac [`160`, `F`, `x`] >>
  simp[in_type_range_within] >>
  `0 <= i /\ i < &(2**160)` by gvs[within_int_bound_ineq] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  `Num i < 2**256` by (fs[] >> intLib.ARITH_TAC) >>
  qpat_x_assum `i = &Num i` SUBST1_TAC >>
  fs[i2w_pos, w2n_n2w, dimword_def, in_type_range_def,
     type_bounds_def, is_signed_type_def, type_bits_def] >> intLib.ARITH_TAC
QED

Theorem scalar_int_address_run_abort:
  !x st op st' ss i.
    compile_type_convert x ConvToAddress st = (op,st') /\
    fresh_vars_wrt st ss /\ eval_operand x ss = SOME (i2w i) /\
    -&(2**255) <= i /\ i < &(2**256) /\
    ~within_int_bound (Unsigned 160) i ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >> gvs[scalar_to_address_clamp] >>
  irule scalar_int_clamp_word_abort >> simp[] >>
  qexistsl_tac [`160`, `op`, `F`, `i2w i`, `x`] >>
  `~within_int_bound (Unsigned 160) (&w2n (i2w i:bytes32))` by
    (qspec_then `i` mp_tac scalar_address_word_range >> fs[]) >>
  gvs[in_type_range_def, type_bits_def, is_signed_type_def,
      within_int_bound_ineq]
QED

Theorem scalar_int_address_result_frag:
  !ctx func cenv cx src i es0.
    -&(2**255) <= i /\ i < &(2**256) ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x ConvToAddress)
      (i2w i) (BaseT AddressT)
      (convert_result cx src (BaseT AddressT) (IntV i)) es0
Proof
  rpt strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >>
  Cases_on `within_int_bound (Unsigned 160) i` >> simp[]
  >- (strip_tac >> qexists_tac `i2w i` >>
      `0 <= i /\ i < &(2**160)` by fs[within_int_bound_ineq] >>
      `i = &Num i` by intLib.ARITH_TAC >>
      `Num i < 2**160` by (fs[] >> intLib.ARITH_TAC) >>
      simp[evaluate_type_def, scalar_typed_address_word] >>
      conj_tac
      >- (qpat_x_assum `i = &Num i` SUBST1_TAC >>
          simp[i2w_pos, w2w_def, w2n_n2w, dimword_def,
               fcpLib.INDEX_CONV ``dimindex(:160)``] >> fs[]) >>
      rpt strip_tac >> drule_all scalar_int_address_run_ok >> simp[]) >>
  strip_tac >> rpt strip_tac >> drule_all scalar_int_address_run_abort >> simp[]
QED
