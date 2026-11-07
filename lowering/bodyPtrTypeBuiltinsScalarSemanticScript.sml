(* Coverage audit for word-source conversion continuations. *)
Theory bodyPtrTypeBuiltinsScalarSemantic
Ancestors exprSimConvert exprLowering exprLoweringProps exprSimDefs
  vyperTypeSystem vyperValue compileEnv vyperAST exprSimHyps
  vyperTyping vyperValueOperation valueEncoding integer_word venomExecSemantics
  bodyPtrTypeBuiltinsUintClampSemantics venomState fragExec words arithmetic

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
