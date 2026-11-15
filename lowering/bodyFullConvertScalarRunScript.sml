(* Physical scalar conversion runs, independent of horizons and ghosts. *)
Theory bodyFullConvertScalarRun
Ancestors
  bodyPtrTypeBuiltinsScalarSemantic bodyPtrTypeBuiltinsScalarRawOutcome
  bodyFullConvertIntegerRun bodyFullConvertDecimalRun bodyFullConvertAddressFlagRun
  bodyFullConvertResultTyping
  exprSimConvert convertScalarBytesRun convertScalarEncoding convertScalarFlags
  convertScalarBytes convertScalarOutputs convertScalarDecimalFrag
  bodyPtrTypeBuiltinsIntegerSemantic bodyPtrTypeBuiltinsScalarArithmetic
  exprUnopStraight exprSimUnop exprLoweringProps exprLowering
  vyperTyping vyperValue vyperValueOperation compileEnv vyperAST vyperTypeSystem
  venomExecSemantics venomState freshWrites emitHelperProps emitHelper
  integer_word words arithmeticProps list rich_list finite_map convertScalarProps valueEncoding
  varsExt fragGasFresh

(* Fixed bytes0 is represented by a zero word.  In particular SAR 256 is
   defined, so this case does not need a dynamic buffer loader. *)
Theorem scalar_fixed_zero_decimal_raw[local]:
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed 0))) (BaseT DecimalT)) sa = (r,sb) /\
  eval_operand x ss = SOME 0w /\ fresh_vars_wrt sa ss ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\ eval_operand r sf = SOME 0w
Proof
  simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
       type_bits_def, is_signed_type_def, w2i_i2w] >>
  rewrite_tac[SRULE [] scalar_bytes_decimal_eq] >> strip_tac >>
  irule bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_fixed_zero_int_raw >> simp[] >> qexistsl_tac [`168`,`T`,`x`] >> gvs[scalar_bytes_decimal_eq, compile_type_convert_def]
QED

Theorem scalar_fixed_source_run:
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
  (?m. src = BaseT (BytesT (Fixed m))) ==>
  case convert_result cx src dst v of
    INL vout => ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand out t = SOME (typed_val_to_w256 tout vout)
  | INR exc => (?msg. exc = Error (RuntimeError msg)) /\
      ?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t
Proof
  strip_tac >> gvs[] >>
  Cases_on `dst` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def] >>
  Cases_on `b` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def]
  >- suspend "uint"
  >- suspend "int"
  >- suspend "bool"
  >- suspend "decimal"
  >- suspend "bytes"
  >> suspend "address"
QED

Resume scalar_fixed_source_run[uint]:
  Cases_on `v` >> gvs[value_has_type_def, mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `within_int_bound (Unsigned n) (&(w2n (word_of_bytes_be (PAD_LEFT 0w 32 l):bytes32)))`
  >- (drule_all (SRULE [] (Q.SPEC `F` scalar_bytes_int_run_ok)) >> strip_tac >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
           typed_val_to_w256_def, val_to_w256_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.SPEC `F` scalar_bytes_int_run_abort)) >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def] >>
  metis_tac[]
QED
Resume scalar_fixed_source_run[int]:
  Cases_on `m = 0`
  >- (gvs[] >> drule bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_fixed_zero_value >> strip_tac >> gvs[] >>
      simp[bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_fixed_zero_signed_result, typed_val_to_w256_def, val_to_w256_def] >>
      gvs[mk_convert_op_def, is_bytestring_type_def] >>
      drule_all bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_fixed_zero_int_raw >> simp[] >>
      metis_tac[i2w_0]) >>
  Cases_on `v` >> gvs[value_has_type_def, mk_convert_op_def, is_bytestring_type_def] >>
  `0 < LENGTH l` by (Cases_on `l` >> gvs[]) >>
  `0 < n` by decide_tac >>
  Cases_on `within_int_bound (Signed n) (w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed (LENGTH l)))) (BytesV l) >> (8*(32-LENGTH l))))`
  >- (drule_all (SRULE [] (Q.SPEC `T` scalar_bytes_int_run_ok)) >> strip_tac >>
      gvs[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
           typed_val_to_w256_def, val_to_w256_def] >> metis_tac[]) >>
  drule_all (SRULE [] (Q.SPEC `T` scalar_bytes_int_run_abort)) >> strip_tac >>
  gvs[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
      typed_val_to_w256_def, val_to_w256_def] >> metis_tac[]
QED
Resume scalar_fixed_source_run[bool]:
  Cases_on `v` >> gvs[value_has_type_def, mk_convert_op_def, is_bytestring_type_def] >>
  drule_all convert_bool_run >> strip_tac >>
  gvs[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
      typed_val_to_w256_def, val_to_w256_def, scalar_fixed_zero,
      EVERY_MEM, EXISTS_MEM, bool_to_word_def] >>
  Cases_on `?b. MEM b l /\ b <> 0w` >> simp[bool_to_word_def]
QED
Resume scalar_fixed_source_run[decimal]:
  Cases_on `m = 0`
  >- (gvs[] >> drule bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_fixed_zero_value >> strip_tac >> gvs[] >>
      simp[bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_fixed_zero_signed_result, typed_val_to_w256_def, val_to_w256_def] >>
      drule_all scalar_fixed_zero_decimal_raw >> simp[] >> metis_tac[i2w_0]) >>
  Cases_on `v` >> gvs[value_has_type_def, mk_convert_op_def, is_bytestring_type_def,
      type_bounds_def, type_bits_def, is_signed_type_def, w2i_i2w,
      SRULE [] (Q.SPEC `167` arithmeticPropsTheory.w2i_i2w_neg_pow2),
      SRULE [] (Q.SPEC `167` arithmeticPropsTheory.w2i_i2w_pow2_sub1)] >>
  `0 < LENGTH l` by (Cases_on `l` >> gvs[]) >>
  Cases_on `within_int_bound decimal_bound (w2i (typed_val_to_w256 (BaseTV (BytesT (Fixed (LENGTH l)))) (BytesV l) >> (8*(32-LENGTH l))))`
  >- (drule_all (SIMP_RULE std_ss [integerTheory.INT_SUB,
        EVAL ``(-&(2 ** 167):int)``, EVAL ``(&(2 ** 167):int) - 1``]
          scalar_bytes_decimal_run_ok) >> strip_tac >>
      gvs[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
          bounded_decimal_op_def, typed_val_to_w256_def, val_to_w256_def] >> metis_tac[]) >>
  drule_all (SIMP_RULE std_ss [integerTheory.INT_SUB,
    EVAL ``(-&(2 ** 167):int)``, EVAL ``(&(2 ** 167):int) - 1``]
      scalar_bytes_decimal_run_abort) >> strip_tac >>
  gvs[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
      bounded_decimal_op_def, typed_val_to_w256_def, val_to_w256_def] >> metis_tac[]
QED
Resume scalar_fixed_source_run[address]:
  Cases_on `v` >> gvs[value_has_type_def, mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `w2n (word_of_bytes_be (PAD_LEFT 0w 32 l):bytes32) < 2**160`
  >- (drule_all (SIMP_RULE bool_ss [] scalar_bytes_address_run_ok) >> strip_tac >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
           scalar_typed_address_word, wordsTheory.w2w_def, wordsTheory.w2n_n2w,
           wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:160)``] >> fs[]) >>
  drule_all (SIMP_RULE bool_ss [] scalar_bytes_address_run_abort) >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def] >> metis_tac[]
QED
Resume scalar_fixed_source_run[bytes]:
  Cases_on `b'` >> gvs[valid_conversion_def, vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def, mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `LENGTH l <= n`
  >- (gvs[compile_type_convert_def, comp_return_def, emitted_insts_def,
          run_inst_seq_def] >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
           scalar_fixed_widen]) >>
  `n < LENGTH l` by decide_tac >>
  Cases_on `EVERY (\b. b = 0w) (DROP n l)`
  >- (drule_all (SRULE [] scalar_bytes_narrow_run_ok) >> strip_tac >>
      simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
           scalar_fixed_narrow] >> metis_tac[]) >>
  drule_all (SIMP_RULE bool_ss [] scalar_bytes_narrow_run_abort) >> strip_tac >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def] >>
  metis_tac[]
QED
Finalise scalar_fixed_source_run

Theorem scalar_convert_physical_frame:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)
Proof
  strip_tac >> drule_all bodyPtrTypeBuiltinsScalarRawOutcomeTheory.scalar_dispatch_straight_fresh >>
  disch_then (qspecl_then [`x`, `cenv`] mp_tac) >>
  simp[straight_fresh_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `t = _` SUBST1_TAC >> simp[]) >>
  simp[lookup_var_def]
QED

Theorem scalar_convert_typed_run_raw[local]:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ fresh_vars_wrt sa s /\ ~s.vs_halted ==>
  ((!vout. convert_result cx src dst v = INL vout ==>
     ?dtv t. evaluate_type (get_tenv cx) dst = SOME dtv /\
       value_has_type dtv vout /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand out t = SOME (typed_val_to_w256 dtv vout) /\
       (t with vs_vars := s.vs_vars) = s /\
       (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)) /\
   (!exc. convert_result cx src dst v = INR exc ==>
     (?msg. exc = Error (RuntimeError msg)) /\
     ?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t))
Proof
  strip_tac >>
  `case convert_result cx src dst v of
     INL vout => ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand out t = SOME (typed_val_to_w256 tout vout)
   | INR exc => (?msg. exc = Error (RuntimeError msg)) /\
       ?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t` by
    (suspend "dispatch") >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_all scalar_convert_result_typed >> strip_tac >>
      drule_all scalar_convert_physical_frame >> strip_tac >>
      simp[]) >>
  rpt strip_tac >> gvs[]
QED
Resume scalar_convert_typed_run_raw[dispatch]:
  `is_word_type src` by (irule (cj 1 bodyPtrTypeBuiltinsScalarSemanticTheory.scalar_source_word_types) >> simp[] >>
    qexistsl [`dst`, `get_tenv cx`] >> simp[]) >>
  Cases_on `src` >> gvs[is_word_type_def]
  >- (Cases_on `b`
      >- (irule scalar_integer_source_run >> simp[] >> metis_tac[])
      >- (irule scalar_integer_source_run >> simp[] >> metis_tac[])
      >- (irule scalar_decimal_bool_source_run >> simp[] >> metis_tac[])
      >- (irule scalar_decimal_bool_source_run >> simp[] >> metis_tac[])
      >- gvs[is_bytestring_type_def]
      >- (Cases_on `b'` >> gvs[is_bytestring_type_def] >>
          irule scalar_fixed_source_run >> simp[is_bytestring_type_def] >> metis_tac[]) >>
      irule scalar_address_flag_source_run >> simp[] >> metis_tac[]) >>
  irule scalar_address_flag_source_run >> simp[] >> metis_tac[]
QED
Finalise scalar_convert_typed_run_raw

Theorem scalar_convert_typed_run:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  evaluate_type (get_tenv cx) src = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  (!name n. dst = FlagT name /\ FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) ==>
    cenv.ce_flag_n_members (nsid_to_string name) = n) /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ ~s.vs_halted ==>
  ((!vout. convert_result cx src dst v = INL vout ==>
     ?dtv t. evaluate_type (get_tenv cx) dst = SOME dtv /\
       value_has_type dtv vout /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand out t = SOME (typed_val_to_w256 dtv vout) /\
       (t with vs_vars := s.vs_vars) = s /\
       (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)) /\
   (!exc. convert_result cx src dst v = INR exc ==>
     (?msg. exc = Error (RuntimeError msg)) /\
     ?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t))
Proof
  strip_tac >>
  `eval_operand x (drop_fresh sa s) = SOME (typed_val_to_w256 tv v)` by
    (Cases_on `x` >> gvs[eval_operand_def, lookup_var_drop_fresh, drop_fresh_def]) >>
  `fresh_vars_wrt sa (drop_fresh sa s) /\ ~(drop_fresh sa s).vs_halted` by
    simp[fresh_vars_wrt_drop_fresh, drop_fresh_def] >>
  `writes_fresh sa (emitted_insts sa sb)` by
    (drule_all bodyPtrTypeBuiltinsScalarRawOutcomeTheory.scalar_dispatch_straight_fresh >>
     disch_then (qspecl_then [`x`,`cenv`] mp_tac) >>
     simp[straight_fresh_def] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (drule writes_fresh_path_opcodes >> simp[EVERY_MEM] >> metis_tac[]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  drule_at (Pat `compile_type_convert _ _ _ = _`) scalar_convert_typed_run_raw >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[] >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!vout. _` drule >> strip_tac >>
      gvs[vars_ext_result_def] >>
      `eval_operand out t' = SOME (typed_val_to_w256 tout vout)` by
        metis_tac[vars_ext_def, eval_operand_vars_ext, optionTheory.NOT_NONE_SOME] >>
      qpat_x_assum `run_inst_seq _ (drop_fresh _ _) = _` kall_tac >>
      drule_all scalar_convert_physical_frame >> strip_tac >> metis_tac[]) >>
  rpt strip_tac >> qpat_x_assum `!exc. _` drule >> strip_tac >>
  gvs[vars_ext_result_def] >> metis_tac[]
QED
