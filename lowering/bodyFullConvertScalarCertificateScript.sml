Theory bodyFullConvertScalarCertificate
Ancestors
  instSeqPtrUniform
  convertScalarBytesRun
  bodyFullAllocGeneric
  bodyUnopFragMemory
  bodyPtrTypeBuiltinsScalarRawOutcome exprSimBopRestWordLayout[qualified,ignore_grammar] loweringShapeDefs[qualified,ignore_grammar] marker[qualified,ignore_grammar] vyperTypeSystem[qualified,ignore_grammar]
  bodyPtrTypeBuiltinsCheckedArithmetic bodyPtrSignedConvertBool
  bodyPtrTypeBuiltinsScalarChecks bodyPtrTypeBuiltinsScalarArithmetic
  fragGasSeqAbortCursor freshWriteAbortCursor
  fragGasSeqPtr ptrSafetyTransport ptrSafeRun exprLowering exprLoweringProps
  compileEnv ptrDiscipline venomExecSemantics venomState venomInst finite_map list
  freshWrites exprSimConvert convertScalarProps
  fragGasOriginPtr fragGasOrigin memSafeRun gasEvents gasCount fragGasPathPtr fragExec
  codegenRel venomExecProofs venomInstProofs fragExecMem instIdxIndep fragGasFresh

Theorem scalar_op_fixed_ok[local]:
  (case tc of ConvBytestringToBool => F | ConvBytestringToInt _ _ _ => F
   | ConvBytestringToDecimal _ _ _ _ => F | ConvBytestringToBytesM _ => F
   | ConvBytestringCast _ _ => F | _ => T) /\
  compile_type_convert x tc sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_int_fixed_certificate) >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_bytes_int_fixed_certificate) >> metis_tac[])
  >- (drule_all convert_int_bytes_fixed_certificate >> simp[])
  >- (irule convert_decimal_fixed_certificate >> simp[] >> metis_tac[])
  >- (irule convert_decimal_fixed_certificate >> simp[] >> metis_tac[])
  >- (drule_all convert_bool_decimal_fixed_certificate >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_address_fixed_certificate) >> metis_tac[])
  >- (gvs[convertScalarBytesRunTheory.scalar_bytes_address_eq] >>
      drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_bytes_int_fixed_certificate) >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_flag_fixed_certificate) >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_bytes_decimal_fixed_certificate) >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_bytesm_fixed_certificate) >> metis_tac[]) >>
  gvs[compile_type_convert_def, comp_return_def, emitted_insts_refl] >>
  qexistsl [`G`,`tn`] >> simp[inst_seq_ptr_def]
QED

Theorem scalar_op_fixed_abort[local]:
  (case tc of ConvBytestringToBool => F | ConvBytestringToInt _ _ _ => F
   | ConvBytestringToDecimal _ _ _ _ => F | ConvBytestringToBytesM _ => F
   | ConvBytestringCast _ _ => F | _ => T) /\
  compile_type_convert x tc sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_int_fixed_certificate) >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_bytes_int_fixed_certificate) >> metis_tac[])
  >- (drule_all convert_int_bytes_abort_fixed_certificate >> simp[])
  >- (irule convert_decimal_abort_fixed_certificate >> simp[] >> metis_tac[])
  >- (irule convert_decimal_abort_fixed_certificate >> simp[] >> metis_tac[])
  >- (metis_tac[convert_bool_decimal_no_abort])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_address_fixed_certificate) >> metis_tac[])
  >- (gvs[convertScalarBytesRunTheory.scalar_bytes_address_eq] >>
      drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_bytes_int_fixed_certificate) >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_flag_fixed_certificate) >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_bytes_decimal_fixed_certificate) >> metis_tac[])
  >- (drule_all (SRULE [DISJ_IMP_THM, GSYM AND_IMP_INTRO] convert_bytesm_fixed_certificate) >> metis_tac[]) >>
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

Theorem scalar_convert_uniform_ok[local]:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th. (!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all scalar_dispatch_op >>
  disch_then (qspec_then `cenv` assume_tac) >>
  ho_match_mp_tac (SRULE []
    (Q.INST [`entry` |-> `\q:num. s`] (SPEC_ALL inst_seq_ptr_uniformize))) >>
  gen_tac >>
  drule_all scalar_op_fixed_ok >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl [`H`,`th`] >> simp[]
QED

Theorem scalar_convert_uniform_abort[local]:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t ==>
  ?H th. (!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all scalar_dispatch_op >>
  disch_then (qspec_then `cenv` assume_tac) >>
  ho_match_mp_tac (SRULE []
    (Q.INST [`entry` |-> `\q:num. s`] (SPEC_ALL inst_seq_ptr_uniformize))) >>
  gen_tac >>
  drule_all scalar_op_fixed_abort >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl [`H`,`th`] >> simp[]
QED

Theorem scalar_convert_code[local]:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS /\ i.inst_opcode <> DALLOCA) (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule_all scalar_dispatch_op >>
  disch_then (qspec_then `cenv` mp_tac) >>
  qmatch_asmsub_abbrev_tac `compile_type_convert x conv` >> strip_tac >>
  `straight_fresh (compile_type_convert x conv)` by
    (Cases_on `conv` >>
     gvs[straight_fresh_convert, straight_fresh_convert_scalar] >>
     simp[compile_type_convert_def, straight_fresh_return]) >>
  `writes_fresh sa (emitted_insts sa sb)` by
    metis_tac[straight_fresh_def] >>
  conj_tac
  >- (fs[writes_fresh_def, EVERY_MEM] >>
      qx_gen_tac `i` >> disch_tac >>
      first_x_assum (qspec_then `i` mp_tac) >>
      simp[] >> strip_tac >>
      fs[fresh_write_op_def] >> gvs[is_terminator_def]) >>
  metis_tac[writes_fresh_mem_ok]
QED

Theorem scalar_convert_run_origin:
  valid_conversion src dst /\ ~is_bytestring_type src /\
  compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = r /\
  ((?t. r = OK t) \/ (?a t. r = Abort a t)) ==>
  ?H th j.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (exec_result_map (\t. t with vs_inst_idx := j) r,H,th)) /\
    (!a t. r = Abort a t /\ MEM fn ctx.ctx_functions /\
      ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) ==>
      ~oversized_create_abort ctx (Abort a (t with vs_inst_idx := j))) /\
    (!t. r = OK t ==> op_prov H out = NONE /\ op_taint th out = {} /\
      j = s.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  `straight_fresh (compile_type_convert x (case dst of FlagT name =>
    ConvToFlag (cenv.ce_flag_n_members (nsid_to_string name))
    | _ => mk_convert_op src dst))` by metis_tac[bodyPtrTypeBuiltinsScalarRawOutcomeTheory.scalar_dispatch_straight_fresh] >>
  drule_all fragGasFreshTheory.straight_fresh_code_prefix >> strip_tac >>
  drule_all scalar_convert_code >> disch_then (qspec_then `s` strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  Cases_on `r` >> gvs[] >>
  `(ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> gvs[EVERY_APPEND, dalloca_no_wrap_non_dalloca])
  >- (drule_all scalar_convert_uniform_ok >>
      disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
      qexistsl [`H`,`th`] >>
      simp[exec_result_map_def] >> gen_tac >>
      `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by
        (irule bodyFullAllocGenericTheory.inst_seq_ptr_lower_bound_from_alloca_next >> simp[] >> qexists `0` >> simp[]) >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sb)` by fs[EVERY_MEM] >>
      `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
        (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
      `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  drule_all scalar_convert_uniform_abort >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H th` by
    (gen_tac >> irule bodyFullAllocGenericTheory.inst_seq_ptr_lower_bound_from_alloca_next >> simp[] >> qexists `0` >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_abort_origin_ptr_cursor >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  qexistsl [`H`,`th`,`j`] >> simp[exec_result_map_def] >>
  rpt strip_tac >> drule_all fetched_fresh_write_abort_not_oversized >> simp[]
QED
