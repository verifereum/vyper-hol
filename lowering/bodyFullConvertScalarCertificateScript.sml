Theory bodyFullConvertScalarCertificate
Ancestors
  bodyPtrTypeBuiltinsCheckedArithmetic bodyPtrSignedConvertBool
  bodyPtrTypeBuiltinsScalarChecks bodyPtrTypeBuiltinsScalarArithmetic
  fragGasSeqPtr ptrSafetyTransport ptrSafeRun exprLowering exprLoweringProps
  compileEnv ptrDiscipline venomExecSemantics venomState venomInst finite_map list

Theorem scalar_op_fixed_ok[local]:
  (case tc of ConvBytestringToBool => F | ConvBytestringToInt _ _ _ => F
   | ConvBytestringToDecimal _ _ _ _ => F | ConvBytestringToBytesM _ => F
   | ConvBytestringCast _ _ => F | _ => T) /\
  compile_type_convert x tc sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `tc` >> simp[] >> strip_tac
  >- (drule_all convert_bool_fixed_certificate >> simp[])
  >- (drule convert_int_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule convert_bytes_int_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule_all convert_int_bytes_fixed_certificate >> simp[])
  >- (irule convert_decimal_fixed_certificate >> simp[] >> metis_tac[])
  >- (irule convert_decimal_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule_all convert_bool_decimal_fixed_certificate >> metis_tac[])
  >- (drule convert_address_fixed_certificate >> simp[] >> metis_tac[])
  >- (gvs[convert_bytes_address_eq] >>
      drule convert_bytes_int_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule convert_flag_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule convert_bytes_decimal_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule convert_bytesm_fixed_certificate >> simp[] >> metis_tac[]) >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl] >>
  qexistsl [`G`,`tn`] >> simp[inst_seq_ptr_def]
QED

Theorem scalar_op_fixed_abort[local]:
  (case tc of ConvBytestringToBool => F | ConvBytestringToInt _ _ _ => F
   | ConvBytestringToDecimal _ _ _ _ => F | ConvBytestringToBytesM _ => F
   | ConvBytestringCast _ _ => F | _ => T) /\
  compile_type_convert x tc sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?H th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `tc` >> simp[] >> strip_tac
  >- (drule convert_bool_code >> strip_tac >>
      gvs[run_inst_seq_def, AllCaseEqs()] >>
      metis_tac[bodyPtrSignedConvertScalarOpsTheory.scalar_iszero_no_abort])
  >- (drule convert_int_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule convert_bytes_int_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule_all convert_int_bytes_abort_fixed_certificate >> simp[])
  >- (irule convert_decimal_abort_fixed_certificate >> simp[] >> metis_tac[])
  >- (irule convert_decimal_abort_fixed_certificate >> simp[] >> metis_tac[])
  >- (metis_tac[convert_bool_decimal_no_abort])
  >- (drule convert_address_fixed_certificate >> simp[] >> metis_tac[])
  >- (gvs[convert_bytes_address_eq] >>
      drule convert_bytes_int_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule convert_flag_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule convert_bytes_decimal_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule convert_bytesm_fixed_certificate >> simp[] >> metis_tac[]) >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl, run_inst_seq_def]
QED

Theorem scalar_dispatch_op[local]:
  valid_conversion src dst /\ ~is_bytestring_type src ==>
  (case (case dst of FlagT name => ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
     | _ => mk_convert_op src dst) of
     ConvBytestringToBool => F | ConvBytestringToInt _ _ _ => F
   | ConvBytestringToDecimal _ _ _ _ => F | ConvBytestringToBytesM _ => F
   | ConvBytestringCast _ _ => F | _ => T)
Proof
  Cases_on `dst` >>
  simp[mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `b` >> simp[mk_convert_op_def, is_bytestring_type_def] >>
  Cases_on `src` >>
  gvs[vyperTypeSystemTheory.valid_conversion_def, is_bytestring_type_def, mk_convert_op_def] >>
  Cases_on `b` >>
  gvs[vyperTypeSystemTheory.valid_conversion_def, is_bytestring_type_def, mk_convert_op_def] >>
  rpt (FIRST [Cases_on `b'`, Cases_on `b''`] >>
       gvs[vyperTypeSystemTheory.valid_conversion_def, is_bytestring_type_def, mk_convert_op_def]) >>
  simp[type_bounds_def, type_bits_def, is_signed_type_def] >>
  IF_CASES_TAC >> simp[]
QED
