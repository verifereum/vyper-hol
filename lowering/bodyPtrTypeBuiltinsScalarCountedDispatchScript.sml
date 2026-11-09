Theory bodyPtrTypeBuiltinsScalarCountedDispatch
Ancestors
  bodyPtrTypeBuiltinsScalarSemantic bodyPtrTypeBuiltinsCheckedArithmetic
  bodyPtrSignedConvertBool fragGasPathPtr exprLowering compileEnv
  exprLoweringProps venomExecSemantics bodyPtrTypeBuiltinsScalarArithmetic
  bodyPtrTypeBuiltinsScalarChecks arithmetic venomInst

Theorem scalar_convert_counted_success:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  conv = (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) /\
  compile_type_convert x conv sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all scalar_source_dispatch_partition >>
  disch_then (qspec_then `cenv` mp_tac) >>
  qpat_x_assum `conv = _` (assume_tac o SYM) >> simp[] >> strip_tac >>
  Cases_on `conv` >> gvs[]
  >~ [`compile_type_convert x ConvIdentity sa = _`]
  >- (gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl,
          run_inst_seq_def] >> qexistsl_tac [`G`,`tn`] >> simp[] >>
      irule (cj 1 gas_path_ptr_rules) >> simp[])
  >~ [`compile_type_convert x ConvToBool sa = _`]
  >- metis_tac[ADD_COMM, convert_bool_counted_certificate]
  >~ [`compile_type_convert x (ConvIntToInt _ _ _ _) sa = _`]
  >- (drule_all convert_int_counted_certificate >> metis_tac[ADD_COMM])
  >~ [`compile_type_convert x (ConvBytesToInt _ _ _) sa = _`]
  >- metis_tac[ADD_COMM, convert_bytes_int_counted_certificate]
  >~ [`compile_type_convert x (ConvIntToBytesM _ _ _) sa = _`]
  >- metis_tac[ADD_COMM, convert_int_bytes_counted_certificate]
  >~ [`compile_type_convert x (ConvIntToDecimal _ _ _ _ _) sa = _`]
  >- (drule_at (Pos (el 2)) convert_decimal_counted_certificate >>
      simp[] >> metis_tac[ADD_COMM])
  >~ [`compile_type_convert x (ConvDecimalToInt _ _ _ _ _ _) sa = _`]
  >- (drule_at (Pos (el 2)) convert_decimal_counted_certificate >>
      simp[] >> metis_tac[ADD_COMM])
  >~ [`compile_type_convert x (ConvBoolToDecimal _) sa = _`]
  >- metis_tac[ADD_COMM, convert_bool_decimal_counted_certificate]
  >~ [`compile_type_convert x (ConvBytesMToDecimal _ _ _ _) sa = _`]
  >- metis_tac[ADD_COMM, convert_bytes_decimal_counted_certificate]
  >~ [`compile_type_convert x ConvToAddress sa = _`]
  >- (drule_all convert_address_counted_certificate >> metis_tac[ADD_COMM])
  >~ [`compile_type_convert x (ConvBytesToAddress _) sa = _`]
  >- (fs[convert_bytes_address_eq] >> metis_tac[ADD_COMM, convert_bytes_int_counted_certificate])
  >~ [`compile_type_convert x (ConvToFlag _) sa = _`]
  >- (drule_all convert_flag_counted_certificate >> metis_tac[ADD_COMM]) >>
  drule_all convert_bytesm_counted_certificate >> metis_tac[ADD_COMM]
QED

Theorem scalar_convert_counted_abort:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  conv = (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) /\
  compile_type_convert x conv sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th steps j.
    gas_path_ptr D 0 ctx fn PG G tn s steps H th
      (Abort err (t with vs_inst_idx := j))
Proof
  strip_tac >> drule_all scalar_source_dispatch_partition >>
  disch_then (qspec_then `cenv` mp_tac) >>
  qpat_x_assum `conv = _` (assume_tac o SYM) >> simp[] >> strip_tac >>
  Cases_on `conv` >> gvs[]
  >~ [`compile_type_convert x ConvIdentity sa = _`]
  >- gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl, run_inst_seq_def]
  >~ [`compile_type_convert x ConvToBool sa = _`]
  >- (drule convert_bool_code >> strip_tac >>
      fs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
         AllCaseEqs()])
  >~ [`compile_type_convert x (ConvIntToInt _ _ _ _) sa = _`]
  >- (drule_all convert_int_abort_counted_certificate >> metis_tac[])
  >~ [`compile_type_convert x (ConvBytesToInt _ _ _) sa = _`]
  >- (drule_all convert_bytes_int_abort_counted_certificate >> metis_tac[])
  >~ [`compile_type_convert x (ConvIntToBytesM _ _ _) sa = _`]
  >- (drule_all convert_int_bytes_abort_counted_certificate >> metis_tac[])
  >~ [`compile_type_convert x (ConvIntToDecimal _ _ _ _ _) sa = _`]
  >- (drule_at (Pos (el 2)) convert_decimal_abort_counted_certificate >> simp[] >> metis_tac[])
  >~ [`compile_type_convert x (ConvDecimalToInt _ _ _ _ _ _) sa = _`]
  >- (drule_at (Pos (el 2)) convert_decimal_abort_counted_certificate >> simp[] >> metis_tac[])
  >~ [`compile_type_convert x (ConvBoolToDecimal _) sa = _`]
  >- metis_tac[convert_bool_decimal_no_abort]
  >~ [`compile_type_convert x (ConvBytesMToDecimal _ _ _ _) sa = _`]
  >- (drule_all convert_bytes_decimal_abort_counted_certificate >> metis_tac[])
  >~ [`compile_type_convert x ConvToAddress sa = _`]
  >- (drule_all convert_address_abort_counted_certificate >> metis_tac[])
  >~ [`compile_type_convert x (ConvBytesToAddress _) sa = _`]
  >- (fs[convert_bytes_address_eq] >> drule_all convert_bytes_int_abort_counted_certificate >> metis_tac[])
  >~ [`compile_type_convert x (ConvToFlag _) sa = _`]
  >- (drule_all convert_flag_abort_counted_certificate >> metis_tac[]) >>
  drule_all convert_bytesm_abort_counted_certificate >> metis_tac[]
QED

Theorem scalar_convert_runtime_frame:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  conv = (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) /\
  compile_type_convert x conv sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule_all scalar_source_dispatch_partition >>
  disch_then (qspec_then `cenv` mp_tac) >>
  qpat_x_assum `conv = _` (assume_tac o SYM) >> simp[] >> strip_tac >>
  Cases_on `conv` >> gvs[]
  >~ [`compile_type_convert x ConvIdentity sa = _`]
  >- gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl, run_inst_seq_def]
  >~ [`compile_type_convert x ConvToBool sa = _`]
  >- metis_tac[convert_bool_runtime_frame]
  >~ [`compile_type_convert x (ConvIntToInt _ _ _ _) sa = _`]
  >- metis_tac[convert_int_runtime_frame]
  >~ [`compile_type_convert x (ConvBytesToInt _ _ _) sa = _`]
  >- metis_tac[convert_bytes_int_runtime_frame]
  >~ [`compile_type_convert x (ConvIntToBytesM _ _ _) sa = _`]
  >- metis_tac[convert_int_bytes_runtime_frame]
  >~ [`compile_type_convert x (ConvIntToDecimal _ _ _ _ _) sa = _`]
  >- (drule_at (Pos (el 2)) convert_decimal_runtime_frame >> simp[])
  >~ [`compile_type_convert x (ConvDecimalToInt _ _ _ _ _ _) sa = _`]
  >- (drule_at (Pos (el 2)) convert_decimal_runtime_frame >> simp[])
  >~ [`compile_type_convert x (ConvBoolToDecimal _) sa = _`]
  >- metis_tac[convert_bool_decimal_runtime_frame]
  >~ [`compile_type_convert x (ConvBytesMToDecimal _ _ _ _) sa = _`]
  >- metis_tac[convert_bytes_decimal_runtime_frame]
  >~ [`compile_type_convert x ConvToAddress sa = _`]
  >- metis_tac[convert_address_runtime_frame]
  >~ [`compile_type_convert x (ConvBytesToAddress _) sa = _`]
  >- (fs[convert_bytes_address_eq] >> metis_tac[convert_bytes_int_runtime_frame])
  >~ [`compile_type_convert x (ConvToFlag _) sa = _`]
  >- metis_tac[convert_flag_runtime_frame] >>
  metis_tac[convert_bytesm_runtime_frame]
QED
