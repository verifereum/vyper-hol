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

(* Bool and decimal sources: the encoded word of a bool is 0 or 1 and a
   decimal is its scaled signed value, so each of these conversions is the
   integer conversion of that word. *)
Theorem scalar_bool_word:
  !b. typed_val_to_w256 (BaseTV BoolT) (BoolV b) = i2w (if b then 1 else 0)
Proof
  Cases >> simp[typed_val_to_w256_def, val_to_w256_def, integer_wordTheory.i2w_def]
QED

Theorem scalar_bool_bytes_result_frag:
  !ctx func cenv cx m b es0.
    0 < m /\ m <= 32 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM F 8 m))
      (typed_val_to_w256 (BaseTV BoolT) (BoolV b))
      (BaseT (BytesT (Fixed m)))
      (convert_result cx (BaseT BoolT) (BaseT (BytesT (Fixed m))) (BoolV b)) es0
Proof
  rpt strip_tac >>
  `convert_result cx (BaseT BoolT) (BaseT (BytesT (Fixed m))) (BoolV b) =
   convert_result cx (BaseT (UintT 8)) (BaseT (BytesT (Fixed m)))
     (IntV (if b then 1 else 0))` by
    (Cases_on `b` >>
     simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
          integer_wordTheory.i2w_def]) >>
  simp[scalar_bool_word] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `F`, `8`, `m`,
               `if b then 1 else 0`, `es0`] mp_tac scalar_int_bytes_result_frag >>
  simp[]
QED

Theorem scalar_decimal_bytes_result_frag:
  !ctx func cenv cx m i es0.
    21 <= m /\ m <= 32 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM T 168 m))
      (typed_val_to_w256 (BaseTV DecimalT) (DecimalV i))
      (BaseT (BytesT (Fixed m)))
      (convert_result cx (BaseT DecimalT) (BaseT (BytesT (Fixed m)))
         (DecimalV i)) es0
Proof
  rpt strip_tac >>
  `convert_result cx (BaseT DecimalT) (BaseT (BytesT (Fixed m))) (DecimalV i) =
   convert_result cx (BaseT (IntT 168)) (BaseT (BytesT (Fixed m))) (IntV i)` by
    simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  `typed_val_to_w256 (BaseTV DecimalT) (DecimalV i) = i2w i` by
    simp[typed_val_to_w256_def, val_to_w256_def] >>
  simp[] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `T`, `168`, `m`, `i`, `es0`]
    mp_tac scalar_int_bytes_result_frag >>
  simp[]
QED

Theorem scalar_decimal_bool_run:
  !i x sa sb op ss.
    within_int_bound (Signed 168) i /\
    compile_type_convert x ConvToBool sa = (op, sb) /\
    fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV DecimalT) (DecimalV i)) ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
          eval_operand op ss' = SOME (bool_to_word (i <> 0))
Proof
  rpt strip_tac >> gvs[typed_val_to_w256_def, val_to_w256_def] >>
  drule_all convert_bool_run >> strip_tac >>
  qexists_tac `ss'` >> simp[] >>
  qspecl_then [`168`, `T`, `i`] mp_tac i2w_eq_0_within >> simp[] >>
  Cases_on `i = 0` >> gvs[bool_to_word_def] >>
  simp[integer_wordTheory.i2w_def]
QED

Theorem scalar_address_bool_run:
  !bs x sa sb op ss.
    LENGTH bs = 20 /\
    compile_type_convert x ConvToBool sa = (op, sb) /\
    fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
          eval_operand op ss' = SOME (bool_to_word (EXISTS (\b. b <> 0w) bs))
Proof
  rpt strip_tac >> gvs[typed_val_to_w256_def, val_to_w256_def] >>
  drule_all convert_bool_run >> strip_tac >>
  qexists_tac `ss'` >> simp[scalar_address_zero] >>
  simp[EXISTS_MEM, EVERY_MEM] >> Cases_on `EXISTS (\b. b <> 0w) bs` >>
  gvs[EXISTS_MEM, EVERY_MEM, bool_to_word_def]
QED

Theorem scalar_bool_decimal_run:
  !b x sa sb op ss.
    compile_type_convert x (ConvBoolToDecimal 10000000000) sa = (op, sb) /\
    fresh_vars_wrt sa ss /\
    eval_operand x ss = SOME (typed_val_to_w256 (BaseTV BoolT) (BoolV b)) ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
          eval_operand op ss' = SOME (i2w (if b then decimal_scale else 0))
Proof
  rpt strip_tac >>
  gvs[typed_val_to_w256_def, val_to_w256_def, compile_type_convert_def] >>
  qspecl_then [`x`, `Lit (n2w 10000000000)`, `if b then 1w else 0w`,
               `n2w 10000000000`, `sa`, `op`, `sb`, `ss`] mp_tac
    emit_op_MUL_correct >>
  simp[eval_operand_def] >> strip_tac >> qexists_tac `ss'` >> simp[] >>
  Cases_on `b` >>
  simp[decimal_scale_def, integer_wordTheory.i2w_def,
       wordsTheory.WORD_MULT_CLAUSES]
QED

Theorem scalar_decimal_bool_result_frag:
  !ctx func cenv cx i es0.
    within_int_bound (Signed 168) i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x ConvToBool)
      (typed_val_to_w256 (BaseTV DecimalT) (DecimalV i))
      (BaseT BoolT)
      (convert_result cx (BaseT DecimalT) (BaseT BoolT) (DecimalV i)) es0
Proof
  rpt strip_tac >> irule unop_frag_straight >>
  simp[straight_fresh_convert, is_word_type_def] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  strip_tac >> qexists_tac `bool_to_word (i <> 0)` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  conj_tac >- (Cases_on `i = 0` >> simp[bool_to_word_def]) >>
  rpt strip_tac >>
  qspecl_then [`i`, `x`, `sa`, `sb`, `op`, `ss`] mp_tac scalar_decimal_bool_run >>
  impl_tac >- gvs[typed_val_to_w256_def, val_to_w256_def] >> simp[]
QED

Theorem scalar_address_bool_result_frag:
  !ctx func cenv cx bs es0.
    LENGTH bs = 20 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x ConvToBool)
      (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
      (BaseT BoolT)
      (convert_result cx (BaseT AddressT) (BaseT BoolT) (BytesV bs)) es0
Proof
  rpt strip_tac >> irule unop_frag_straight >>
  simp[straight_fresh_convert, is_word_type_def] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  strip_tac >> qexists_tac `bool_to_word (EXISTS (\b. b <> 0w) bs)` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  conj_tac >- (Cases_on `EXISTS (\b. b <> 0w) bs` >> simp[bool_to_word_def]) >>
  rpt strip_tac >>
  qspecl_then [`bs`, `x`, `sa`, `sb`, `op`, `ss`] mp_tac scalar_address_bool_run >>
  impl_tac >- gvs[typed_val_to_w256_def, val_to_w256_def] >> simp[]
QED

Theorem scalar_bool_decimal_result_frag:
  !ctx func cenv cx b es0.
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvBoolToDecimal 10000000000))
      (typed_val_to_w256 (BaseTV BoolT) (BoolV b))
      (BaseT DecimalT)
      (convert_result cx (BaseT BoolT) (BaseT DecimalT) (BoolV b)) es0
Proof
  rpt strip_tac >> irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  strip_tac >>
  qexists_tac `i2w (if b then decimal_scale else 0)` >>
  simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  rpt strip_tac >>
  qspecl_then [`b`, `x`, `sa`, `sb`, `op`, `ss`] mp_tac scalar_bool_decimal_run >>
  impl_tac >- gvs[typed_val_to_w256_def, val_to_w256_def] >> simp[]
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
