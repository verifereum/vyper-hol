(* Coverage audit for word-source conversion continuations. *)
Theory bodyPtrTypeBuiltinsScalarSemantic
Ancestors exprSimConvert exprLowering exprLoweringProps exprSimDefs
  vyperTypeSystem vyperValue compileEnv vyperAST exprSimHyps
  vyperTyping vyperValueOperation valueEncoding integer_word venomExecSemantics
  bodyPtrTypeBuiltinsUintClampSemantics venomState fragExec words arithmetic
  bodyPtrTypeBuiltinsScalarChecks varsExt emitHelper emitHelperProps rich_list
  venomInst list freshWrites exprSimHypsDefs finite_map convertScalarBytesRun
  convertScalarEncoding byte bodyPtrTypeBuiltinsScalarArithmetic

(* Unlike scalar_conversion_word_types this includes int_convert_pair and
   derives the non-bytestring destination from valid_conversion itself. *)
Theorem scalar_source_word_types:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  IS_SOME (evaluate_type tenv src) /\ IS_SOME (evaluate_type tenv dst) ==>
  is_word_type src /\ is_word_type dst /\ ~is_bytestring_type dst
Proof
  Cases_on `src` >> Cases_on `dst` >>
  gvs[valid_conversion_def, is_bytestring_type_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def] >>
  Cases_on `b` >> gvs[valid_conversion_def, is_bytestring_type_def,
                      is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  Cases_on `b'` >> gvs[valid_conversion_def, is_bytestring_type_def,
                       is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  rpt (FIRST [Cases_on `b''`, Cases_on `b`] >>
       gvs[valid_conversion_def, is_bytestring_type_def,
           is_word_type_def, vyperValueTheory.evaluate_type_def])
QED

Theorem scalar_source_dispatch_partition:
  valid_conversion src dst /\ ~is_bytestring_type src ==>
  case (case dst of FlagT name =>
          ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
        | _ => mk_convert_op src dst) of
    ConvToBool => T
  | ConvIntToInt _ _ _ _ => T
  | ConvBytesToInt _ _ _ => T
  | ConvIntToBytesM _ _ _ => T
  | ConvIntToDecimal _ _ _ _ _ => T
  | ConvDecimalToInt _ _ _ _ _ _ => T
  | ConvBoolToDecimal _ => T
  | ConvBytesMToDecimal _ _ _ _ => T
  | ConvToAddress => T
  | ConvBytesToAddress _ => T
  | ConvToFlag _ => T
  | ConvBytesMToBytesM _ _ => T
  | ConvIdentity => T
  | _ => F
Proof
  Cases_on `dst` >>
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `b` >> simp[mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `src` >>
  gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def] >>
  Cases_on `b` >>
  gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def] >>
  rpt (FIRST [Cases_on `b'`, Cases_on `b''`] >>
       gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def]) >>
  simp[type_bounds_def, type_bits_def, is_signed_type_def] >>
  IF_CASES_TAC >> simp[]
QED

(* These are typing-valid corner cases, not dynamic-bytestring residuals.
   scalar_operand_typed_frag excludes them; their SAR/SDIV semantics therefore
   need a separate execution boundary before complete scalar assembly. *)
Theorem fixed_zero_signed_typing_probe:
  valid_conversion (BaseT (BytesT (Fixed 0))) (BaseT (IntT 256)) /\
  valid_conversion (BaseT (BytesT (Fixed 0))) (BaseT DecimalT) /\
  well_formed_type tenv (BaseT (BytesT (Fixed 0))) /\
  well_formed_type tenv (BaseT (IntT 256)) /\
  well_formed_type tenv (BaseT DecimalT)
Proof
  EVAL_TAC
QED

(* The generic conversion precondition and typing interface suffice here;
   importing convertScalarTyping would currently fail in its immutable
   expr_sim_inv_def reference, so consumers use this stronger word boundary. *)
Theorem scalar_source_body_word_types:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  ~is_bytestring_type (expr_type e) ==>
  ann = dst /\ valid_conversion (expr_type e) dst /\
  expr_body_pre cenv cx env e es /\
  is_word_type (expr_type e) /\ is_word_type dst /\ ~is_bytestring_type dst
Proof
  strip_tac >>
  `IS_SOME (evaluate_type (get_tenv cx) dst)` by
    (drule expr_body_pre_type_evaluates >> simp[expr_type_def] >>
     drule expr_body_pre_convert >> simp[] >> metis_tac[]) >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    (drule_all expr_body_pre_type_evaluates >> simp[]) >>
  drule_all scalar_source_word_types >> simp[]
QED

(* Semantic/counting coverage map for subsequent continuations:
   - int_convert_pair: exprSimConvert.convert_frag_word requires source typing
     and IS_SOME destination evaluation; the fragment uses val_to_w256, so
     typed_val_to_w256 alignment must be established at its extraction boundary.
   - Other scalar pairs: convertScalarBridge.scalar_operand_typed_frag requires
     the full outer expr_body_pre, the actual successful operand evaluation,
     non-bytestring endpoints, NOT int_convert_pair, and NOT fixed bytes0 to
     Int/Decimal. It returns the dispatched unop_frag (target FlagT is special).
     That theory is currently unavailable through convertScalarTyping; do not
     repair the immutable ancestor or assume the excluded cases away.
   - Successful and aborting pointer certificates already exist for ToFlag,
     ToAddress, IntToInt and BytesMToBytesM in ScalarChecks; BytesToInt and
     BytesMToDecimal in ScalarArithmetic; IntToBytesM, IntToDecimal and
     DecimalToInt in CheckedArithmetic. Bool and Identity have their existing
     pure/zero-edge boundaries. ScalarArithmetic also covers BoolToDecimal,
     although valid_conversion does not permit that pair.
   - Fixed bytes0 to signed Int/Decimal passes valid_conversion and all type
     evaluation checks (fixed_zero_signed_typing_probe). The compiler emits
     SAR with count 256, optionally followed by decimal conversion. No runtime
     payload load is involved. Separate exact-run semantics on its zero input
     is required; the signed dynamic-bytestring residual cannot cover it.
   No scalar coverage conclusion depends on the retained counterexample or
   the authorized dynamic-bytestring residual. *)

Theorem scalar_identity_source_partition:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  (case dst of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
   | _ => mk_convert_op src dst) = ConvIdentity ==>
  src = BaseT BoolT /\ ((?n. dst = BaseT (IntT n)) \/ (?n. dst = BaseT (UintT n)))
Proof
  Cases_on `src` >> Cases_on `dst` >>
  gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def] >>
  Cases_on `b` >>
  gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def] >>
  rpt (FIRST [Cases_on `b'`, Cases_on `b''`, Cases_on `b`] >>
       gvs[valid_conversion_def, is_bytestring_type_def, mk_convert_op_def]) >>
  simp[type_bounds_def, type_bits_def, is_signed_type_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem scalar_identity_semantic_packet:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  (case dst of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
   | _ => mk_convert_op src dst) = ConvIdentity /\
  evaluate_type (get_tenv cx) src = SOME tv /\ value_has_type tv v1 /\
  evaluate_type (get_tenv cx) dst = SOME tout ==>
  ?v. convert_result cx src dst v1 = INL v /\
      typed_val_to_w256 tout v = typed_val_to_w256 tv v1
Proof
  strip_tac >> drule_all scalar_identity_source_partition >> strip_tac >> gvs[] >>
  Cases_on `v1` >> gvs[vyperValueTheory.evaluate_type_def, value_has_type_def] >>
  rename1 `BoolV b` >> Cases_on `b` >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       typed_val_to_w256_def, val_to_w256_def, bool_to_word_def, i2w_def]
QED

Theorem scalar_flag_raw_exact:
  compile_type_convert op (ConvToFlag n) sa = (r,sb) /\
  eval_operand op ss = SOME w /\ fresh_vars_wrt sa ss ==>
  if w2n w < 2 ** n then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
         eval_operand r sf = SOME w
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >> Cases_on `n < 256`
  >- (`compile_int_clamp F n op sa = (r,sb)` by fs[compile_type_convert_def] >>
      `n <= 256` by decide_tac >>
      `w2n w <= w2n (n2w (2 ** n-1):bytes32) <=> w2n w < 2 ** n` by
        (simp[uint_clamp_test, within_int_bound_def] >> decide_tac) >>
      drule_all uint_clamp_raw_exact >>
      Cases_on `w2n w < 2 ** n` >> simp[] >> metis_tac[]) >>
  `w2n w < 2 ** n` by
    (irule LESS_LESS_EQ_TRANS >> qexists_tac `dimword(:256)` >>
     simp[w2n_lt, dimword_def]) >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl, run_inst_seq_def]
QED

Theorem scalar_flag_replay:
  compile_type_convert op (ConvToFlag n) sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  Cases_on `n < 256` >>
  gvs[compile_type_convert_def, compile_int_clamp_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem scalar_flag_actual_exact:
  compile_type_convert op (ConvToFlag n) sa = (r,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ eval_operand op ss = SOME w ==>
  if w2n w < 2 ** n then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
         eval_operand r sf = SOME w /\
         (sf with vs_vars := ss.vs_vars) = ss /\
         (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand op (drop_fresh sa ss) = SOME w` by simp[eval_operand_drop_fresh] >>
  drule_all scalar_flag_raw_exact >>
  drule scalar_flag_replay >> disch_then (qspec_then `ss` mp_tac) >>
  Cases_on `w2n w < 2 ** n` >> simp[] >> rpt strip_tac >>
  gvs[vars_ext_result_def]
  >- (rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >>
      conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      irule convert_flag_runtime_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >>
  metis_tac[]
QED

Theorem scalar_flag_source_partition:
  valid_conversion src (FlagT name) ==> src = BaseT (UintT 256)
Proof
  Cases_on `src` >> simp[valid_conversion_def] >>
  Cases_on `b` >> simp[valid_conversion_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem scalar_flag_semantic_packet:
  FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) /\
  within_int_bound (Unsigned 256) i ==>
  convert_result cx (BaseT (UintT 256)) (FlagT name) (IntV i) =
    if Num i < 2 ** n then INL (FlagV (Num i))
    else INR (Error (RuntimeError "convert int flag bound"))
Proof
  strip_tac >> `0 <= i` by fs[within_int_bound_ineq] >>
  Cases_on `Num i < 2 ** n` >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def]
QED

Theorem scalar_flag_semantic_actual:
  FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) /\
  within_int_bound (Unsigned 256) i /\
  compile_type_convert x (ConvToFlag n) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ eval_operand x ss = SOME (i2w i) ==>
  case convert_result cx (BaseT (UintT 256)) (FlagT name) (IntV i) of
    INL v => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (FlagTV n) v) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => ex = Error (RuntimeError "convert int flag bound") /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `0 <= i /\ i < &(dimword(:256))` by
    fs[within_int_bound_ineq, integer_wordTheory.INT_MIN_def,
       integer_wordTheory.UINT_MAX_def, dimword_def] >>
  `w2n (i2w i : bytes32) = Num i` by
    (`i = &Num i` by intLib.ARITH_TAC >>
     qpat_x_assum `i = &Num i` SUBST_ALL_TAC >>
     fs[i2w_pos, w2n_n2w, dimword_def]) >>
  drule_all scalar_flag_semantic_packet >> disch_then SUBST1_TAC >>
  drule_all scalar_flag_actual_exact >>
  Cases_on `Num i < 2 ** n` >> simp[] >> strip_tac >>
  simp[typed_val_to_w256_def, val_to_w256_def, i2w_pos] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  qpat_x_assum `i = &Num i` SUBST1_TAC >> simp[i2w_pos]
QED

Theorem scalar_flag_body_packet:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (FlagT name) [e]) es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 ==>
  ?n i. ann = FlagT name /\ expr_type e = BaseT (UintT 256) /\
    FLOOKUP (get_tenv cx) name = SOME (FlagArgs n) /\
    cenv.ce_flag_n_members (nsid_to_string name) = n /\
    evaluate_type (get_tenv cx) (FlagT name) = SOME (FlagTV n) /\
    v1 = IntV i /\ within_int_bound (Unsigned 256) i /\
    typed_val_to_w256 tv v1 = i2w i
Proof
  strip_tac >>
  `IS_SOME (evaluate_type (get_tenv cx) (FlagT name))` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[expr_type_def] >> drule expr_body_pre_convert >> metis_tac[]) >>
  drule expr_body_pre_convert >> strip_tac >>
  drule_all scalar_flag_source_partition >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, optionTheory.IS_SOME_EXISTS, AllCaseEqs()] >>
  Cases_on `v1` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  fs[expr_body_pre_def, expr_sim_inv_def] >>
  simp[within_int_bound_def]
QED

Theorem scalar_flag_compile_frame:
  compile_type_convert x (ConvToFlag n) sa = (r,sb) ==>
  r = x /\ inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)
Proof
  Cases_on `n < 256` >>
  simp[compile_type_convert_def, compile_int_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, inst_extends_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem scalar_fixed_int_raw_semantic:
  LENGTH bs = m /\ 0 < m /\ m <= 32 /\
  0 < b /\ (sg ==> 1 < b) /\ b <= 256 /\
  compile_type_convert x (ConvBytesToInt m sg b) sa = (r,sb) /\
  eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
  fresh_vars_wrt sa ss ==>
  case convert_result cx (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b)) (BytesV bs) of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME
        (typed_val_to_w256 (BaseTV (if sg then IntT b else UintT b)) out)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >> `bs <> []` by (Cases_on `bs` >> gvs[]) >>
  Cases_on `sg` >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def] >>
  IF_CASES_TAC >> simp[typed_val_to_w256_def, val_to_w256_def]
  >- (`?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
          eval_operand r sf = SOME (i2w (w2i
            ((word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) >> (8*(32-m)))):bytes32)`
        suffices_by simp[i2w_w2i] >>
      irule (Q.SPEC `T` scalar_bytes_int_run_ok) >>
      simp[] >> qexistsl_tac [`b`,`bs`,`x`] >>
      fs[typed_val_to_w256_def])
  >- (irule (Q.SPEC `T` scalar_bytes_int_run_abort) >>
      simp[] >> qexistsl_tac [`b`,`bs`,`r`,`x`] >>
      fs[typed_val_to_w256_def])
  >- (`?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
          eval_operand r sf = SOME (i2w (&w2n
            (word_of_bytes_be (PAD_LEFT 0w 32 bs):bytes32)):bytes32)`
        suffices_by simp[i2w_pos, n2w_w2n] >>
      irule (Q.SPEC `F` scalar_bytes_int_run_ok) >>
      simp[] >> qexistsl_tac [`b`,`bs`,`x`] >>
      fs[typed_val_to_w256_def]) >>
  irule (Q.SPEC `F` scalar_bytes_int_run_abort) >>
  simp[] >> qexistsl_tac [`b`,`bs`,`r`,`x`] >> fs[typed_val_to_w256_def]
QED

Theorem scalar_fixed_int_replay:
  compile_type_convert x (ConvBytesToInt m sg b) sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  Cases_on `sg` >> Cases_on `m*8 > b` >>
  gvs[compile_type_convert_def, compile_int_clamp_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem scalar_fixed_int_actual_semantic:
  LENGTH bs = m /\ 0 < m /\ m <= 32 /\
  0 < b /\ (sg ==> 1 < b) /\ b <= 256 /\
  compile_type_convert x (ConvBytesToInt m sg b) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) ==>
  case convert_result cx (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b)) (BytesV bs) of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME
        (typed_val_to_w256 (BaseTV (if sg then IntT b else UintT b)) out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh sa ss) =
    SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))` by
    simp[eval_operand_drop_fresh] >>
  drule_all scalar_fixed_int_raw_semantic >>
  disch_then (qspec_then `cx` mp_tac) >>
  Cases_on `convert_result cx (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b)) (BytesV bs)` >> simp[] >> strip_tac >>
  drule scalar_fixed_int_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >> gvs[]
  >- (rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >>
      conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      irule convert_bytes_int_runtime_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >>
  simp[]
QED

Theorem scalar_fixed_int_typed_actual:
  0 < m /\ evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT (if sg then IntT b else UintT b)) = SOME tout /\
  value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b))) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  case convert_result cx (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b)) v of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 tout out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  Cases_on `sg` >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs(), mk_convert_op_def,
    is_bytestring_type_def, type_bits_def, type_bounds_def, is_signed_type_def]
  >- (irule (SRULE [] (Q.INST [`sg` |-> `T`] scalar_fixed_int_actual_semantic)) >>
      simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  irule (SRULE [] (Q.INST [`sg` |-> `F`] scalar_fixed_int_actual_semantic)) >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem scalar_fixed_zero_value:
  value_has_type (BaseTV (BytesT (Fixed 0))) v ==>
  v = BytesV [] /\ typed_val_to_w256 (BaseTV (BytesT (Fixed 0))) v = 0w
Proof
  Cases_on `v` >> simp[value_has_type_def] >> strip_tac >> gvs[] >>
  EVAL_TAC >> simp[]
QED

Theorem scalar_fixed_zero_signed_result:
  convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT (IntT b)) (BytesV []) = INL (IntV 0) /\
  convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT DecimalT) (BytesV []) = INL (DecimalV 0)
Proof
  `word_of_bytes_be (PAD_RIGHT (0w:word8) 32 []):bytes32 = 0w` by
    (EVAL_TAC >> simp[]) >>
  `((0w:bytes32) >> 256) = 0w` by wordsLib.WORD_DECIDE_TAC >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       within_int_bound_def, bounded_decimal_op_def, w2i_def,
       word_msb_def, word_0] >> Cases_on `0 < b` >> simp[]
QED

Theorem scalar_fixed_zero_int_raw:
  compile_type_convert x (ConvBytesToInt 0 sg b) sa = (r,sb) /\
  eval_operand x ss = SOME 0w /\ fresh_vars_wrt sa ss /\ b <= 256 ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\ eval_operand r sf = SOME 0w
Proof
  Cases_on `sg` >> strip_tac >>
  `((0w:bytes32) >> w2n (n2w ((32-0)*8):bytes32)) = 0w` by
    (simp[] >> wordsLib.WORD_DECIDE_TAC) >>
  drule scalar_bytes_int_word_ok >>
  disch_then (qspecl_then [`ss`,`0w:bytes32`] mp_tac) >>
  simp[arithmeticPropsTheory.in_type_range_def, type_bits_def, is_signed_type_def, w2i_def,
       word_msb_def, word_0]
QED

Theorem scalar_fixed_zero_int_actual:
  compile_type_convert x (ConvBytesToInt 0 sg b) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ eval_operand x ss = SOME 0w /\ b <= 256 ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\ eval_operand r sf = SOME 0w /\
    (sf with vs_vars := ss.vs_vars) = ss /\
    (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
Proof
  strip_tac >>
  `eval_operand x (drop_fresh sa ss) = SOME 0w` by simp[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all scalar_fixed_zero_int_raw >> strip_tac >>
  drule scalar_fixed_int_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >> gvs[] >>
  rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >> conj_tac
  >- (fs[vars_ext_def] >>
      qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
      simp[eval_operand_vars_ext]) >>
  irule convert_bytes_int_runtime_frame >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any)
QED

Theorem scalar_fixed_zero_decimal_actual:
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed 0))) (BaseT DecimalT)) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\ eval_operand x ss = SOME 0w ==>
  ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\ eval_operand r sf = SOME 0w /\
    (sf with vs_vars := ss.vs_vars) = ss /\
    (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
Proof
  simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
       type_bits_def, is_signed_type_def, w2i_i2w] >>
  rewrite_tac[SRULE [] scalar_bytes_decimal_eq] >> strip_tac >>
  irule scalar_fixed_zero_int_actual >> simp[] >> qexistsl_tac [`168`,`T`,`x`] >> simp[]
QED

Theorem scalar_fixed_zero_unsigned_result:
  convert_result cx (BaseT (BytesT (Fixed 0))) (BaseT (UintT b)) (BytesV []) = INL (IntV 0)
Proof
  `word_of_bytes_be (PAD_LEFT (0w:word8) 32 []):bytes32 = 0w` by
    (EVAL_TAC >> simp[]) >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       within_int_bound_def, word_0]
QED

Theorem scalar_fixed_int_all_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT (if sg then IntT b else UintT b)) = SOME tout /\
  value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b))) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  case convert_result cx (BaseT (BytesT (Fixed m)))
    (BaseT (if sg then IntT b else UintT b)) v of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 tout out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  Cases_on `m = 0`
  >- (gvs[] >> Cases_on `sg` >> simp[vyperValueTheory.evaluate_type_def] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      drule scalar_fixed_zero_value >> strip_tac >> gvs[] >>
      simp[scalar_fixed_zero_signed_result, scalar_fixed_zero_unsigned_result,
           typed_val_to_w256_def, val_to_w256_def, i2w_def] >>
      irule scalar_fixed_zero_int_actual >>
      fs[mk_convert_op_def, is_bytestring_type_def, type_bits_def,
         type_bounds_def, is_signed_type_def] >> metis_tac[]) >>
  strip_tac >> irule scalar_fixed_int_typed_actual >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem scalar_fixed_decimal_raw_semantic:
  LENGTH bs = m /\ 0 < m /\ m <= 32 /\
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m))) (BaseT DecimalT)) sa = (r,sb) /\
  eval_operand x ss = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs)) /\
  fresh_vars_wrt sa ss ==>
  case convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) (BytesV bs) of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV DecimalT) out)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >> `bs <> []` by (Cases_on `bs` >> gvs[]) >>
  fs[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
     type_bits_def, is_signed_type_def, w2i_i2w] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       bounded_decimal_op_def] >>
  IF_CASES_TAC >> simp[typed_val_to_w256_def, val_to_w256_def]
  >- (`?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
          eval_operand r sf = SOME (i2w (w2i
            ((word_of_bytes_be (PAD_RIGHT 0w 32 bs):bytes32) >> (8*(32-m)))):bytes32)`
        suffices_by simp[i2w_w2i] >>
      irule scalar_bytes_decimal_run_ok >>
      simp[] >> qexistsl_tac [`bs`,`10000000000`,`x`] >>
      fs[typed_val_to_w256_def, decimal_bits_def]) >>
  irule scalar_bytes_decimal_run_abort >>
  simp[] >> qexistsl_tac [`bs`,`10000000000`,`r`,`x`] >>
  fs[typed_val_to_w256_def]
QED

Theorem scalar_fixed_decimal_all_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT DecimalT) = SOME tout /\ value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m))) (BaseT DecimalT)) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  case convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) v of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 tout out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `m = 0`
  >- (gvs[] >> drule scalar_fixed_zero_value >> strip_tac >> gvs[] >>
      simp[scalar_fixed_zero_signed_result, typed_val_to_w256_def, val_to_w256_def, i2w_def] >>
      irule scalar_fixed_zero_decimal_actual >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `v` >> fs[value_has_type_def] >>
  `eval_operand x (drop_fresh sa ss) =
    SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV l))` by
    simp[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  `0 < m` by decide_tac >>
  drule_all scalar_fixed_decimal_raw_semantic >>
  disch_then (qspec_then `cx` mp_tac) >>
  `compile_type_convert x (ConvBytesToInt m T 168) sa = (r,sb)` by
    (fs[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
        type_bits_def, is_signed_type_def, w2i_i2w,
        SRULE [] scalar_bytes_decimal_eq]) >>
  Cases_on `convert_result cx (BaseT (BytesT (Fixed m))) (BaseT DecimalT) (BytesV l)` >>
  simp[] >> strip_tac >>
  drule scalar_fixed_int_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >> gvs[]
  >- (rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >> conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      irule convert_bytes_int_runtime_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >> simp[]
QED

Theorem scalar_fixed_decimal_compile_eq:
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m))) (BaseT DecimalT)) =
  compile_type_convert x (ConvBytesToInt m T 168)
Proof
  simp[mk_convert_op_def, is_bytestring_type_def, type_bounds_def,
       type_bits_def, is_signed_type_def, w2i_i2w,
       SRULE [] scalar_bytes_decimal_eq]
QED
