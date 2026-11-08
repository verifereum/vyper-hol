Theory bodyPtrTypeBuiltinsScalarRawOutcome
Ancestors
  bodyPtrTypeBuiltinsScalarSemantic bodyPtrTypeBuiltinsIntegerSemantic
  exprLowering exprLoweringProps compileEnv venomExecSemantics exprSimDefs
  valueEncoding loweringPosts exprSimConvert convertScalarBytes convertScalarOutputs

Theorem scalar_identity_actual_outcome:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) = ConvIdentity /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v /\
  evaluate_type (get_tenv cx) dst = SOME tout /\
  compile_type_convert x ConvIdentity sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) ==>
  ?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx src dst v = INL vout /\ expr_val_rel cx dst vout out t
Proof
  strip_tac >> drule_all scalar_identity_semantic_packet >> strip_tac >>
  `is_word_type dst` by (irule (cj 2 scalar_source_word_types) >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl,
      run_inst_seq_def] >>
  simp[expr_val_rel_def]
QED

Theorem scalar_fixed_bool_actual_outcome:
  LENGTH bs = m /\ m <= 32 /\
  compile_type_convert x ConvToBool sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
  fresh_vars_wrt sa s ==>
  ?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (BytesT (Fixed m))) (BaseT BoolT) (BytesV bs) = INL vout /\
    expr_val_rel cx (BaseT BoolT) vout out t
Proof
  strip_tac >> drule_all convert_bool_run >> strip_tac >>
  qexistsl_tac [`ss'`, `BoolV (EXISTS (\b. b <> 0w) bs)`] >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_not_address_bytes,
       vyperValueOperationTheory.evaluate_convert_def, expr_val_rel_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  gvs[typed_val_to_w256_def, convertScalarEncodingTheory.scalar_fixed_zero,
      listTheory.EVERY_MEM, listTheory.EXISTS_MEM, bool_to_word_def] >>
  IF_CASES_TAC >> simp[bool_to_word_def]
QED

Theorem scalar_fixed_widen_actual_outcome:
  LENGTH bs = m /\ m <= n /\ n <= 32 /\
  compile_type_convert x (ConvBytesMToBytesM m n) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) ==>
  ?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (BytesT (Fixed n))) (BytesV bs) = INL vout /\
    expr_val_rel cx (BaseT (BytesT (Fixed n))) vout out t
Proof
  strip_tac >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl, run_inst_seq_def] >>
  qexists_tac `BytesV (PAD_RIGHT 0w n bs)` >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_not_address_bytes,
       vyperValueOperationTheory.evaluate_convert_def, expr_val_rel_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       convertScalarEncodingTheory.scalar_fixed_widen]
QED

Theorem scalar_fixed_narrow_actual_outcome:
  LENGTH bs = m /\ n < m /\ m <= 32 /\
  compile_type_convert x (ConvBytesMToBytesM m n) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
  fresh_vars_wrt sa s ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (BytesT (Fixed n))) (BytesV bs) = INL vout /\
    expr_val_rel cx (BaseT (BytesT (Fixed n))) vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (BaseT (BytesT (Fixed m)))
      (BaseT (BytesT (Fixed n))) (BytesV bs)) (Abort err t))
Proof
  strip_tac >> Cases_on `EVERY (\b. b = 0w) (DROP n bs)`
  >- (drule_all convertScalarBytesRunTheory.scalar_bytes_narrow_run_ok >> strip_tac >>
      disj1_tac >> qexistsl_tac [`ss'`, `BytesV (TAKE n bs)`] >>
      simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_not_address_bytes,
           vyperValueOperationTheory.evaluate_convert_def, expr_val_rel_def,
           vyperValueTheory.evaluate_type_def, is_word_type_def,
           convertScalarEncodingTheory.scalar_fixed_narrow]) >>
  drule_all convertScalarBytesRunTheory.scalar_bytes_narrow_run_abort >> strip_tac >>
  disj2_tac >> qexistsl_tac [`Revert_abort`, `ss'`] >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_not_address_bytes,
       vyperValueOperationTheory.evaluate_convert_def, expr_exit_def]
QED

Theorem scalar_fixed_address_actual_outcome:
  LENGTH bs = m /\ m <= 32 /\
  compile_type_convert x (ConvBytesToAddress m) sa = (out,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
  fresh_vars_wrt sa s ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (BytesT (Fixed m))) (BaseT AddressT) (BytesV bs) = INL vout /\
    expr_val_rel cx (BaseT AddressT) vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (BaseT (BytesT (Fixed m)))
      (BaseT AddressT) (BytesV bs)) (Abort err t))
Proof
  strip_tac >>
  qabbrev_tac `u = w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)` >>
  `u = w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)` by simp[Abbr `u`] >>
  Cases_on `u < 2 ** 160`
  >- (drule_all convertScalarBytesRunTheory.scalar_bytes_address_run_ok >> strip_tac >>
      disj1_tac >> qexistsl_tac [`ss'`, `AddressV (n2w u)`] >>
      simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_not_address_bytes,
           vyperValueOperationTheory.evaluate_convert_def, expr_val_rel_def,
           vyperValueTheory.evaluate_type_def, is_word_type_def,
           scalar_typed_address_word, wordsTheory.w2w_def, wordsTheory.w2n_n2w,
           wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:160)``, Abbr `u`] >>
      gvs[wordsTheory.word_0_n2w, wordsTheory.n2w_w2n]) >>
  drule_all convertScalarBytesRunTheory.scalar_bytes_address_run_abort >> strip_tac >>
  disj2_tac >> qexistsl_tac [`Revert_abort`, `ss'`] >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_not_address_bytes,
       vyperValueOperationTheory.evaluate_convert_def, expr_exit_def, Abbr `u`]
QED

(* Normalize the existing typed raw packets without repeating source-family
   arithmetic. Runtime framing remains available in the original packets. *)
Theorem scalar_typed_packet_outcome:
  evaluate_type (get_tenv cx) dst = SOME tout /\ is_word_type dst /\
  (case result of
     INL v => ?t. run_inst_seq code s = OK t /\
       eval_operand out t = SOME (typed_val_to_w256 tout v) /\ frame t
   | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
       ?t. run_inst_seq code s = Abort Revert_abort t) ==>
  (?t v. run_inst_seq code s = OK t /\ result = INL v /\
    expr_val_rel cx dst v out t) \/
  (?err t. run_inst_seq code s = Abort err t /\ expr_exit result (Abort err t))
Proof
  Cases_on `result` >> simp[] >> strip_tac
  >- (goal_assum (drule_at Any) >> simp[expr_val_rel_def]) >>
  qexistsl_tac [`Revert_abort`, `t`] >> simp[expr_exit_def]
QED

Theorem scalar_fixed_integer_actual_outcome:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT (if sg then IntT b else UintT b)) = SOME tout /\
  value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b))) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (BytesT (Fixed m))) (BaseT (if sg then IntT b else UintT b)) v = INL vout /\
    expr_val_rel cx (BaseT (if sg then IntT b else UintT b)) vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (BaseT (BytesT (Fixed m)))
      (BaseT (if sg then IntT b else UintT b)) v) (Abort err t))
Proof
  strip_tac >> drule_all scalar_fixed_int_all_typed_actual >>
  disch_tac >> irule scalar_typed_packet_outcome >>
  conj_tac >- (Cases_on `sg` >> simp[is_word_type_def]) >>
  qexistsl_tac [`\t. (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)`, `tout`] >>
  simp[]
QED

Theorem scalar_fixed_decimal_actual_outcome:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT DecimalT) = SOME tout /\ value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m))) (BaseT DecimalT)) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) v = INL vout /\
    expr_val_rel cx (BaseT DecimalT) vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) v) (Abort err t))
Proof
  strip_tac >> drule_all scalar_fixed_decimal_all_typed_actual >>
  disch_tac >> irule scalar_typed_packet_outcome >>
  simp[is_word_type_def] >> metis_tac[]
QED

Theorem scalar_integer_actual_outcome:
  evaluate_type (get_tenv cx) (BaseT (if si then IntT bi else UintT bi)) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT (if so then IntT bo else UintT bo)) = SOME tout /\
  value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (if si then IntT bi else UintT bi))
    (BaseT (if so then IntT bo else UintT bo))) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (if si then IntT bi else UintT bi))
      (BaseT (if so then IntT bo else UintT bo)) v = INL vout /\
    expr_val_rel cx (BaseT (if so then IntT bo else UintT bo)) vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (BaseT (if si then IntT bi else UintT bi))
      (BaseT (if so then IntT bo else UintT bo)) v) (Abort err t))
Proof
  strip_tac >> drule_all scalar_integer_typed_actual >>
  disch_tac >> irule scalar_typed_packet_outcome >>
  conj_tac >- (Cases_on `so` >> simp[is_word_type_def]) >>
  qexistsl_tac [`\t. (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)`, `tout`] >> simp[]
QED

Theorem scalar_fixed_source_actual_outcome:
  valid_conversion (BaseT (BytesT (Fixed m))) dst /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m))) dst) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ fresh_vars_wrt sa s /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (BytesT (Fixed m))) dst v = INL vout /\
    expr_val_rel cx dst vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (BaseT (BytesT (Fixed m))) dst v) (Abort err t))
Proof
  Cases_on `dst` >> simp[vyperTypeSystemTheory.valid_conversion_def] >>
  Cases_on `b` >> simp[vyperTypeSystemTheory.valid_conversion_def]
  >- (strip_tac >>
      drule_all (SRULE [] (Q.INST [`sg` |-> `F`] scalar_fixed_integer_actual_outcome)) >> simp[])
  >- (strip_tac >>
      drule_all (SRULE [] (Q.INST [`sg` |-> `T`] scalar_fixed_integer_actual_outcome)) >> simp[])
  >- (strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
      fs[mk_convert_op_def, is_bytestring_type_def] >>
      disj1_tac >> irule scalar_fixed_bool_actual_outcome >>
      metis_tac[])
  >- (strip_tac >> drule_all scalar_fixed_decimal_actual_outcome >> simp[])
  >- (Cases_on `b'` >> simp[vyperTypeSystemTheory.valid_conversion_def] >> strip_tac >>
      gvs[vyperValueTheory.evaluate_type_def] >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
      fs[mk_convert_op_def, is_bytestring_type_def] >>
      Cases_on `LENGTH l <= n`
      >- (disj1_tac >> irule scalar_fixed_widen_actual_outcome >> metis_tac[]) >>
      irule scalar_fixed_narrow_actual_outcome >> metis_tac[arithmeticTheory.NOT_LESS_EQUAL]) >>
  strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  fs[mk_convert_op_def, is_bytestring_type_def] >>
  irule scalar_fixed_address_actual_outcome >> metis_tac[]
QED

Theorem scalar_integer_bool_actual_outcome:
  within_int_bound (if sg then Signed bits else Unsigned bits) i /\ bits <= 256 /\
  compile_type_convert x ConvToBool sa = (out,sb) /\
  eval_operand x s = SOME (i2w i) /\ fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    expr_val_rel cx (BaseT BoolT) (BoolV (i <> 0)) out t
Proof
  strip_tac >> drule_all convert_bool_run >> strip_tac >>
  `i2w i = (0w:bytes32) <=> i = 0` by
    metis_tac[exprSimArithTheory.i2w_eq_0_within, integer_wordTheory.i2w_pos] >>
  qexists_tac `ss'` >>
  simp[expr_val_rel_def, vyperValueTheory.evaluate_type_def, is_word_type_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `i = 0` >> gvs[bool_to_word_def, integer_wordTheory.i2w_def]
QED

Theorem scalar_integer_bytes_actual_outcome:
  bits <= 8*m /\ m <= 32 /\
  compile_type_convert x (ConvIntToBytesM sg bits m) sa = (out,sb) /\
  fresh_vars_wrt sa s /\ eval_operand x s = SOME (i2w i) ==>
  ?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (if sg then IntT bits else UintT bits))
      (BaseT (BytesT (Fixed m))) (IntV i) = INL vout /\
    expr_val_rel cx (BaseT (BytesT (Fixed m))) vout out t
Proof
  strip_tac >> drule_all scalar_int_bytes_run >> strip_tac >>
  qexistsl_tac [`ss'`, `BytesV (DROP (32-m) (word_to_bytes_be (i2w i:bytes32)))`] >>
  Cases_on `sg` >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_def,
       vyperValueOperationTheory.evaluate_convert_def, expr_val_rel_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       convertScalarEncodingTheory.scalar_word_to_fixed]
QED

Theorem scalar_address_bytes_actual_outcome:
  LENGTH bs = 20 /\ 20 <= m /\ m <= 32 /\
  compile_type_convert x (ConvIntToBytesM F 160 m) sa = (out,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) ==>
  ?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT AddressT) (BaseT (BytesT (Fixed m))) (BytesV bs) = INL vout /\
    expr_val_rel cx (BaseT (BytesT (Fixed m))) vout out t
Proof
  strip_tac >> `160 <= 8*m` by decide_tac >>
  drule_all scalar_int_bytes_run >> strip_tac >>
  qexistsl_tac [`ss'`, `BytesV (PAD_LEFT 0w m bs)`] >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_def,
       expr_val_rel_def, vyperValueTheory.evaluate_type_def, is_word_type_def,
       convertScalarEncodingTheory.scalar_address_to_fixed]
QED

Theorem scalar_flag_bytes_actual_outcome:
  compile_type_convert x (ConvIntToBytesM F 256 32) sa = (out,sb) /\
  fresh_vars_wrt sa s /\ eval_operand x s = SOME (typed_val_to_w256 (FlagTV k) (FlagV m)) ==>
  ?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (FlagT name) (BaseT (BytesT (Fixed 32))) (FlagV m) = INL vout /\
    expr_val_rel cx (BaseT (BytesT (Fixed 32))) vout out t
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.SPECL [`x`, `F`, `256`, `32`] scalar_int_bytes_run)) >> strip_tac >>
  qexistsl_tac [`ss'`, `BytesV (word_to_bytes_be (n2w m:bytes32))`] >>
  simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_def,
       vyperValueOperationTheory.evaluate_convert_def, expr_val_rel_def,
       vyperValueTheory.evaluate_type_def, is_word_type_def,
       convertScalarEncodingTheory.scalar_flag_to_bytes32] >>
  `!w:bytes32. w << 0 = w` by wordsLib.WORD_DECIDE_TAC >>
  gvs[GSYM typed_val_to_w256_def, convertScalarEncodingTheory.scalar_flag_to_bytes32]
QED

Theorem scalar_address_uint_actual_outcome:
  LENGTH bs = 20 /\ 0 < bits /\ bits <= 256 /\
  compile_type_convert x (ConvIntToInt F 160 F bits) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT AddressT) (BaseT (UintT bits)) (BytesV bs) = INL vout /\
    expr_val_rel cx (BaseT (UintT bits)) vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (BaseT AddressT) (BaseT (UintT bits)) (BytesV bs)) (Abort err t))
Proof
  strip_tac >>
  qabbrev_tac `i:int = &w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)` >>
  `within_int_bound (Unsigned 160) i` by
    (simp[Abbr `i`, within_int_bound_ineq] >>
     drule convertScalarBytesRunTheory.scalar_bytes_unsigned_bound >> simp[]) >>
  `typed_val_to_w256 (BaseTV AddressT) (BytesV bs) = i2w i` by
    simp[Abbr `i`, typed_val_to_w256_def, integer_wordTheory.i2w_pos] >>
  drule (SRULE [] (Q.INST [`si` |-> `F`, `bi` |-> `160`, `so` |-> `F`]
    scalar_integer_actual_run)) >>
  disch_then (qspecl_then [`s`, `i`] mp_tac) >> simp[] >>
  Cases_on `within_int_bound (Unsigned bits) i` >> simp[] >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`sf`, `IntV i`] >>
      simp[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_def,
        vyperValueOperationTheory.evaluate_convert_def, expr_val_rel_def,
        vyperValueTheory.evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def, Abbr `i`]) >>
  disj2_tac >> qexistsl_tac [`Revert_abort`, `sf`] >>
  simp[expr_exit_def, convert_result_def,
    vyperValueOperationTheory.evaluate_convert_from_def,
    vyperValueOperationTheory.evaluate_convert_def, Abbr `i`]
QED

Theorem scalar_flag_integer_actual_outcome:
  m < 2 ** 256 /\ 0 < bits /\ (sg ==> 1 < bits) /\ bits <= 256 /\
  compile_type_convert x (ConvIntToInt F 256 sg bits) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (typed_val_to_w256 (FlagTV k) (FlagV m)) ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (FlagT name) (BaseT (if sg then IntT bits else UintT bits)) (FlagV m) = INL vout /\
    expr_val_rel cx (BaseT (if sg then IntT bits else UintT bits)) vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (FlagT name) (BaseT (if sg then IntT bits else UintT bits)) (FlagV m)) (Abort err t))
Proof
  strip_tac >>
  `within_int_bound (Unsigned 256) (&m)` by simp[within_int_bound_ineq] >>
  `eval_operand x s = SOME (i2w (&m))` by
    simp[GSYM typed_val_to_w256_def, integer_wordTheory.i2w_pos,
      typed_val_to_w256_def, val_to_w256_def] >>
  drule (SRULE [] (Q.INST [`si` |-> `F`, `bi` |-> `256`]
    scalar_integer_actual_run)) >>
  disch_then (qspecl_then [`s`, `&m`] mp_tac) >> simp[] >>
  Cases_on `within_int_bound (if sg then Signed bits else Unsigned bits) (&m)` >>
  simp[] >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`sf`, `IntV (&m)`] >> Cases_on `sg` >>
      gvs[convert_result_def, vyperValueOperationTheory.evaluate_convert_from_def,
        vyperValueOperationTheory.evaluate_convert_def, expr_val_rel_def,
        vyperValueTheory.evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def]) >>
  disj2_tac >> qexistsl_tac [`Revert_abort`, `sf`] >> Cases_on `sg` >>
  gvs[expr_exit_def, convert_result_def,
    vyperValueOperationTheory.evaluate_convert_from_def,
    vyperValueOperationTheory.evaluate_convert_def]
QED

Theorem scalar_uint_flag_actual_outcome:
  FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) /\ n <= 256 /\
  within_int_bound (Unsigned 256) i /\
  compile_type_convert x (ConvToFlag n) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ eval_operand x s = SOME (i2w i) ==>
  (?t vout. run_inst_seq (emitted_insts sa sb) s = OK t /\
    convert_result cx (BaseT (UintT 256)) (FlagT name) (IntV i) = INL vout /\
    expr_val_rel cx (FlagT name) vout out t) \/
  (?err t. run_inst_seq (emitted_insts sa sb) s = Abort err t /\
    expr_exit (convert_result cx (BaseT (UintT 256)) (FlagT name) (IntV i)) (Abort err t))
Proof
  strip_tac >> drule_all scalar_flag_semantic_actual >>
  disch_tac >> irule scalar_typed_packet_outcome >>
  simp[is_word_type_def] >>
  qexistsl_tac [`\t. (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)`, `FlagTV n`] >>
  simp[vyperValueTheory.evaluate_type_def] >>
  Cases_on `convert_result cx (BaseT (UintT 256)) (FlagT name) (IntV i)` >> gvs[]
QED
