(* Scalar output suffixes proved from primitive instruction execution. *)
Theory bodyMemTbConvertScalarOutputs
Ancestors
  bodyMemTbConvertScalarBytes bodyUnopFragMemory
  convertScalarBytesRun convertScalarEncoding convertScalarProps exprSimConvert
  exprLowering compileEnv vyperValue valueEncoding vyperValueOperation
  exprLoweringProps emitHelperProps emitHelper venomExecSemantics
  arithmetic words integer_word list venomState venomInst exprSimArith arithmeticProps
Libs
  pairLib

Theorem scalar_to_fixed_frag_mem:
  !ctx func cenv cx sg bits m w t res es0.
    bits <= 8*m /\ m <= 32 /\ is_word_type t /\
    (expr_res_ok res ==> ?v. res = INL v /\
      !tv. evaluate_type (get_tenv cx) t = SOME tv ==>
        typed_val_to_w256 tv v = w << (8*(32-m))) ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM sg bits m)) w t res es0
Proof
  rpt strip_tac >> irule unop_frag_mem_straight >>
  simp[straight_fresh_convert_scalar] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  qexists_tac `w << (8*(32-m))` >> simp[] >>
  rpt strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_return_def, LET_THM] >>
  qspecl_then [`SHL`, `\x y. y << w2n x`] (mp_tac o BETA_RULE)
    emit_op_pure2_correct >>
  disch_then drule >>
  disch_then (qspecl_then [`n2w (8*(32-m))`, `w`, `ss`] mp_tac) >>
  (impl_tac >- (conj_tac >- simp[eval_operand_def] >>
               conj_tac >- simp[] >> conj_tac >- simp[] >>
               irule step_SHL >> simp[eval_operand_def])) >>
  `8 * (32-m) < 2 ** 256` by simp[] >>
  simp[dimword_def] >> metis_tac[]
QED

Theorem scalar_int_bytes_result_frag_mem:
  !ctx func cenv cx sg bits m i es0.
    bits <= 8*m /\ m <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM sg bits m))
      (i2w i) (BaseT (BytesT (Fixed m)))
      (convert_result cx (BaseT (if sg then IntT bits else UintT bits))
        (BaseT (BytesT (Fixed m))) (IntV i)) es0
Proof
  rpt strip_tac >> irule scalar_to_fixed_frag_mem >>
  simp[is_word_type_def] >> Cases_on `sg` >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       evaluate_type_def, scalar_word_to_fixed]
QED

Theorem scalar_address_uint_result_frag_mem:
  !ctx func cenv cx bs b es0.
    LENGTH bs = 20 /\ 0 < b /\ b <= 256 ==>
    unop_frag_mem ctx func cenv cx
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
  irule unop_frag_mem_straight >>
  simp[straight_fresh_convert, is_word_type_def] >>
  Cases_on `within_int_bound (Unsigned b) i` >> simp[]
  >- (strip_tac >> qexists_tac `i2w i` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >> drule convert_int_run >>
      disch_then (qspecl_then [`i`, `ss`] mp_tac) >> simp[]) >>
  strip_tac >> rpt strip_tac >> drule convert_int_run >>
  disch_then (qspecl_then [`i`, `ss`] mp_tac) >> simp[]
QED

Theorem scalar_address_bytes_result_frag_mem:
  !ctx func cenv cx bs m es0.
    LENGTH bs = 20 /\ 20 <= m /\ m <= 32 ==>
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM F 160 m))
      (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
      (BaseT (BytesT (Fixed m)))
      (convert_result cx (BaseT AddressT)
        (BaseT (BytesT (Fixed m))) (BytesV bs)) es0
Proof
  rpt strip_tac >> irule scalar_to_fixed_frag_mem >>
  simp[is_word_type_def, convert_result_def, evaluate_convert_from_def,
       evaluate_type_def, scalar_address_to_fixed]
QED

Theorem scalar_flag_bytes_result_frag_mem:
  !ctx func cenv cx nsid k m es0.
    unop_frag_mem ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToBytesM F 256 32))
      (typed_val_to_w256 (FlagTV k) (FlagV m))
      (BaseT (BytesT (Fixed 32)))
      (convert_result cx (FlagT nsid)
        (BaseT (BytesT (Fixed 32))) (FlagV m)) es0
Proof
  rpt strip_tac >> irule scalar_to_fixed_frag_mem >>
  simp[is_word_type_def, convert_result_def, evaluate_convert_from_def,
       evaluate_convert_def, evaluate_type_def] >>
  qspecl_then [`k`, `m`] assume_tac scalar_flag_to_bytes32 >>
  `!w:bytes32. w << 0 = w` by wordsLib.WORD_DECIDE_TAC >> simp[]
QED
