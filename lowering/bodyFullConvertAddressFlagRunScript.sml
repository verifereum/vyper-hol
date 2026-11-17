(* Address and flag source physical conversion execution. *)
Theory bodyFullConvertAddressFlagRun
Ancestors
  bodyPtrTypeBuiltinsIntegerSemantic convertScalarOutputs convertScalarEncoding
  convertScalarBytesRun exprSimConvert exprLowering exprLoweringProps compileEnv
  vyperValue vyperValueOperation vyperTypeSystem vyperTyping vyperAST valueEncoding
  venomExecSemantics venomState emitHelperProps emitHelper
  integer_word words arithmeticProps list finite_map

Theorem scalar_address_flag_source_run:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ fresh_vars_wrt sa s /\ ~s.vs_halted /\
  (src = BaseT AddressT \/ (?name. src = FlagT name)) ==>
  case convert_result cx src dst v of
    INL vout => ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (typed_val_to_w256 tout vout)
  | INR exc => (?msg. exc = Error (RuntimeError msg)) /\
      ?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t
Proof
  strip_tac >> gvs[]
  >- (Cases_on `dst` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def] >>
      Cases_on `b` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def]
      >- suspend "address_uint"
      >- suspend "address_bool" >> suspend "address_bytes") >>
  Cases_on `dst` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def] >>
  Cases_on `b` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def]
  >- suspend "flag_uint" >> suspend "flag_bytes"
QED
Resume scalar_address_flag_source_run[address_uint]:
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[mk_convert_op_def] >>
  qabbrev_tac `i:int = &w2n (word_of_bytes_be (PAD_LEFT 0w 32 l):bytes32)` >>
  `within_int_bound (Unsigned 160) i` by
    (simp[Abbr `i`, within_int_bound_ineq] >>
     drule scalar_bytes_unsigned_bound >> simp[]) >>
  `typed_val_to_w256 (BaseTV AddressT) (BytesV l) = i2w i` by
    simp[Abbr `i`, typed_val_to_w256_def, integer_wordTheory.i2w_pos] >>
  gvs[] >>
  drule_at (Pat `compile_type_convert _ _ _ = _`) scalar_integer_actual_run >>
  disch_then (qspecl_then [`s`,`i`] mp_tac) >> simp[] >>
  Cases_on `within_int_bound (Unsigned n) i` >> simp[] >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       typed_val_to_w256_def, val_to_w256_def, Abbr `i`] >> metis_tac[]
QED
Resume scalar_address_flag_source_run[address_bool]:
  Cases_on `v` >> gvs[value_has_type_def, mk_convert_op_def] >>
  drule_all scalar_address_bool_run >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `EXISTS (\b. b <> 0w) l` >> simp[bool_to_word_def]
QED
Resume scalar_address_flag_source_run[address_bytes]:
  Cases_on `v` >> gvs[value_has_type_def] >>
  Cases_on `b'` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def,
      mk_convert_op_def] >>
  `160 <= 8 * n` by decide_tac >>
  drule_all scalar_int_bytes_run >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def] >>
  simp[scalar_address_to_fixed]
QED
Resume scalar_address_flag_source_run[flag_uint]:
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs()] >>
  gvs[mk_convert_op_def, typed_val_to_w256_def, val_to_w256_def] >>
  `n < 2 ** 256` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists `2 ** m` >> simp[]) >>
  `within_int_bound (Unsigned 256) (&n)` by simp[within_int_bound_ineq] >>
  `eval_operand x s = SOME (i2w (&n))` by simp[integer_wordTheory.i2w_pos] >>
  drule_at (Pat `compile_type_convert _ _ _ = _`) scalar_integer_actual_run >>
  disch_then (qspecl_then [`s`,`&n`] mp_tac) >> simp[] >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       typed_val_to_w256_def, val_to_w256_def] >> metis_tac[]
QED
Resume scalar_address_flag_source_run[flag_bytes]:
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs()] >>
  gvs[mk_convert_op_def, typed_val_to_w256_def, val_to_w256_def] >>
  drule_all (SRULE [] (Q.SPECL [`x`,`F`,`256`,`32`] scalar_int_bytes_run)) >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       scalar_flag_to_bytes32] >>
  `!w:bytes32. w << 0 = w` by wordsLib.WORD_DECIDE_TAC >>
  pure_rewrite_tac[Q.SPEC `m` scalar_flag_to_bytes32] >>
  simp[typed_val_to_w256_def, val_to_w256_def]
QED
Finalise scalar_address_flag_source_run
