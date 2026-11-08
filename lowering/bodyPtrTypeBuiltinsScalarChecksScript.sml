Theory bodyPtrTypeBuiltinsScalarChecks
Ancestors
  bodyPtrSignedConvertClamp exprLowering exprLoweringProps fragGasSeqPtr
  compileEnv ptrDiscipline finite_map venomState venomInst list
  venomExecSemantics emitHelperProps ASCIInumbers rich_list
  bodyPtrSignedConvertScalarOps bodyPtrSignedConvertIszero

Theorem convert_address_clamp:
  compile_type_convert x ConvToAddress = compile_int_clamp F 160 x
Proof
  simp[compile_type_convert_def, compile_int_clamp_def]
QED

Theorem convert_address_fixed_certificate:
  compile_type_convert x ConvToAddress sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  rewrite_tac[convert_address_clamp] >>
  MATCH_ACCEPT_TAC int_clamp_unsigned_fixed_certificate
QED

Theorem convert_flag_fixed_certificate:
  compile_type_convert x (ConvToFlag n) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `n < 256`
  >- (simp[compile_type_convert_def] >>
      MATCH_ACCEPT_TAC int_clamp_unsigned_fixed_certificate) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`G`,`tn`] >>
  simp[emitted_insts_def, inst_seq_ptr_def]
QED

Theorem convert_address_runtime_frame:
  compile_type_convert x ConvToAddress sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  rewrite_tac[convert_address_clamp] >> MATCH_ACCEPT_TAC int_clamp_runtime_frame
QED

Theorem convert_flag_runtime_frame:
  compile_type_convert x (ConvToFlag n) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  Cases_on `n < 256`
  >- (simp[compile_type_convert_def] >> MATCH_ACCEPT_TAC int_clamp_runtime_frame) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem convert_address_instruction_filter:
  compile_type_convert x ConvToAddress sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  rewrite_tac[convert_address_clamp] >> MATCH_ACCEPT_TAC int_clamp_instruction_filter
QED

Theorem convert_flag_instruction_filter:
  compile_type_convert x (ConvToFlag n) sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Cases_on `n < 256`
  >- (simp[compile_type_convert_def] >> MATCH_ACCEPT_TAC int_clamp_instruction_filter) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def]
QED

Theorem scalar_checked_pair_prefix:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  (run_inst_seq [mk_inst id opc [x;y] [a];
    mk_inst (id+1) ISZERO [Var a] [b];
    mk_inst (id+2) ASSERT [Var b] []] s = OK t \/
   run_inst_seq [mk_inst id opc [x;y] [a];
    mk_inst (id+1) ISZERO [Var a] [b];
    mk_inst (id+2) ASSERT [Var b] []] s = Abort err t) ==>
  ?u. run_inst_seq [mk_inst id opc [x;y] [a];
    mk_inst (id+1) ISZERO [Var a] [b]] s = OK u
Proof
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >> gvs[]
  >>
  qpat_x_assum `step_inst_base _ _ = Abort _ _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV (REWRITE_CONV
    [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
     instruction_accfupds, combinTheory.K_THM, opcode_case_def]))) >>
  gvs[MEM] >> simp[exec_pure2_def, exec_pure1_def, AllCaseEqs()]
QED

Theorem convert_bytesm_code:
  out_m < in_m /\
  compile_type_convert x (ConvBytesMToBytesM in_m out_m) sa = (out,sb) ==>
  ?a b.
    out = x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id SHL [Lit (n2w (out_m * 8));x] [a];
       mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
       mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
    (!p. not_fresh_at sa p ==> p <> a /\ p <> b) /\
    sb.cs_next_var = sa.cs_next_var+2 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+3
Proof
  strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  gvs[same_blocks_def, not_fresh_at_def, toString_inj] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var+1))`] >> simp[toString_inj]
QED

Theorem scalar_checked_pair_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq [mk_inst id opc [x;y] [a];
    mk_inst (id+1) ISZERO [Var a] [b];
    mk_inst (id+2) ASSERT [Var b] []] s = OK t \/
   run_inst_seq [mk_inst id opc [x;y] [a];
    mk_inst (id+1) ISZERO [Var a] [b];
    mk_inst (id+2) ASSERT [Var b] []] s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id opc [x;y] [a]; mk_inst (id+1) ISZERO [Var a] [b];
       mk_inst (id+2) ASSERT [Var b] []] s H th /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. p <> a /\ p <> b ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> (
  `?u. run_inst_seq [mk_inst id opc [x;y] [a];
    mk_inst (id+1) ISZERO [Var a] [b]] s = OK u` by
    (irule scalar_checked_pair_prefix >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b})`,
    `tn with t_var := tn.t_var |+ (a,{}) |+ (b,{})`] >> conj_tac
  >- (irule (PURE_REWRITE_RULE [APPEND] scalar_iszero_assert_certificate) >>
      simp[] >> goal_assum (drule_at Any)) >>
  conj_tac
  >- (Cases >> simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      rpt IF_CASES_TAC >> simp[]) >>
  simp[op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE])
QED

Theorem convert_bytesm_fixed_certificate:
  compile_type_convert x (ConvBytesMToBytesM in_m out_m) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `out_m < in_m`
  >- (disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all convert_bytesm_code >> strip_tac >> gnvs[] >>
      `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
       op_prov G (Lit (n2w (8 * out_m))) = NONE /\
       op_taint tn (Lit (n2w (8 * out_m))) = {}` by
        simp[op_prov_def, op_taint_def] >>
      drule_all scalar_checked_pair_certificate >>
      disch_then (qspecl_then [`fn`,`PG`,`D`]
        (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
      qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`G`,`tn`] >> simp[emitted_insts_def, inst_seq_ptr_def]
QED

Theorem scalar_checked_pair_runtime_frame:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  run_inst_seq
    [mk_inst id opc [x;y] [a];
     mk_inst (id+1) ISZERO [Var a] [b];
     mk_inst (id+2) ASSERT [Var b] []] s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. p <> a /\ p <> b ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_assum `step_inst_base (mk_inst id opc _ _) _ = _`
    (mp_then Any mp_tac convert_scalar_run_shape) >> simp[] >> strip_tac >> gvs[] >>
  drule iszero_run_shape >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV (REWRITE_CONV
    [step_inst_base_opcode_eqs, mk_inst_def, instruction_accessors,
     instruction_accfupds, combinTheory.K_THM, opcode_case_def]))) >>
  simp[AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem convert_bytesm_runtime_frame:
  compile_type_convert x (ConvBytesMToBytesM in_m out_m) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  Cases_on `out_m < in_m`
  >- (strip_tac >> drule_all convert_bytesm_code >> strip_tac >> gvs[] >>
      `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
      drule_all scalar_checked_pair_runtime_frame >> strip_tac >> simp[]) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem convert_bytesm_instruction_filter:
  compile_type_convert x (ConvBytesMToBytesM in_m out_m) sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Cases_on `out_m < in_m`
  >- (strip_tac >> drule_all convert_bytesm_code >> strip_tac >> gvs[] >>
      simp[mk_inst_def, is_terminator_def]) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def]
QED

Theorem convert_address_counted_certificate:
  compile_type_convert x ConvToAddress sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  rewrite_tac[convert_address_clamp] >> MATCH_ACCEPT_TAC int_clamp_counted_certificate
QED

Theorem convert_address_abort_counted_certificate:
  compile_type_convert x ConvToAddress sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th n j.
    gas_path_ptr D 0 ctx fn PG G tn s n H th (Abort err (t with vs_inst_idx := j)) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  rewrite_tac[convert_address_clamp] >> MATCH_ACCEPT_TAC int_clamp_abort_counted_certificate
QED

Theorem convert_flag_counted_certificate:
  compile_type_convert x (ConvToFlag n) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_flag_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule convert_flag_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem convert_flag_abort_counted_certificate:
  compile_type_convert x (ConvToFlag n) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th steps j.
    gas_path_ptr D 0 ctx fn PG G tn s steps H th (Abort err (t with vs_inst_idx := j)) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_flag_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule convert_flag_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`n'`,`j`] >> simp[]
QED

Theorem convert_bytesm_counted_certificate:
  compile_type_convert x (ConvBytesMToBytesM in_m out_m) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_bytesm_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule convert_bytesm_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem convert_bytesm_abort_counted_certificate:
  compile_type_convert x (ConvBytesMToBytesM in_m out_m) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th n j.
    gas_path_ptr D 0 ctx fn PG G tn s n H th (Abort err (t with vs_inst_idx := j)) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_bytesm_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule convert_bytesm_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`n`,`j`] >> simp[]
QED

Theorem convert_int_signed_narrow_code:
  out_b < in_b /\
  compile_type_convert x (ConvIntToInt T in_b F out_b) sa = (out,sb) ==>
  ?a b c d e.
    out = x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id GT [x;Lit (n2w (2 ** out_b - 1))] [a];
       mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
       mk_inst (sa.cs_next_id+2) SLT [x;Lit 0w] [c];
       mk_inst (sa.cs_next_id+3) ISZERO [Var c] [d];
       mk_inst (sa.cs_next_id+4) AND [Var b;Var d] [e];
       mk_inst (sa.cs_next_id+5) ASSERT [Var e] []] /\
    (!p. not_fresh_at sa p ==> ~MEM p [a;b;c;d;e]) /\
    sb.cs_next_var = sa.cs_next_var+5 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+6
Proof
  strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  gvs[same_blocks_def, not_fresh_at_def, toString_inj] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`,
    `STRING #"%" (toString (sa.cs_next_var+3))`,
    `STRING #"%" (toString (sa.cs_next_var+4))`] >> simp[toString_inj]
QED

Theorem convert_int_signed_narrow_fixed_certificate:
  out_b < in_b /\
  compile_type_convert x (ConvIntToInt T in_b F out_b) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all convert_int_signed_narrow_code >> strip_tac >> gnvs[] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST
    [`opc1` |-> `GT`, `opc2` |-> `SLT`] (SPEC_ALL scalar_double_check_certificate))) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]
QED

Theorem convert_int_unsigned_signed_clamp:
  compile_type_convert x (ConvIntToInt F in_b T out_b) =
  compile_int_clamp F (out_b-1) x
Proof
  simp[compile_type_convert_def, compile_int_clamp_def]
QED

Theorem convert_int_signed_wide_code:
  ~(out_b < in_b) /\
  compile_type_convert x (ConvIntToInt T in_b F out_b) sa = (out,sb) ==>
  ?a b.
    out = x /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id SLT [x;Lit 0w] [a];
       mk_inst (sa.cs_next_id+1) ISZERO [Var a] [b];
       mk_inst (sa.cs_next_id+2) ASSERT [Var b] []] /\
    (!p. not_fresh_at sa p ==> p <> a /\ p <> b) /\
    sb.cs_next_var = sa.cs_next_var+2 /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts+3
Proof
  strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> fs[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  gvs[same_blocks_def, not_fresh_at_def, toString_inj] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var+1))`] >> simp[toString_inj]
QED

Theorem convert_int_signed_wide_fixed_certificate:
  ~(out_b < in_b) /\
  compile_type_convert x (ConvIntToInt T in_b F out_b) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all convert_int_signed_wide_code >> strip_tac >> gnvs[] >>
  `MEM SLT [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
   op_prov G (Lit 0w) = NONE /\ op_taint tn (Lit 0w) = {}` by
    simp[op_prov_def, op_taint_def] >>
  drule_all scalar_checked_pair_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> metis_tac[]
QED

Theorem convert_int_same_sign_fixed_certificate:
  compile_type_convert x (ConvIntToInt signed in_b signed out_b) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `out_b < in_b`
  >- (simp[compile_type_convert_def] >> MATCH_ACCEPT_TAC int_clamp_fixed_certificate) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`G`,`tn`] >> simp[emitted_insts_def, inst_seq_ptr_def]
QED

Theorem convert_int_fixed_certificate:
  compile_type_convert x (ConvIntToInt in_s in_b out_s out_b) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  Cases_on `in_s` >> Cases_on `out_s`
  >~ [`ConvIntToInt T in_b T out_b`]
  >- MATCH_ACCEPT_TAC convert_int_same_sign_fixed_certificate
  >~ [`ConvIntToInt F in_b F out_b`]
  >- MATCH_ACCEPT_TAC convert_int_same_sign_fixed_certificate
  >~ [`ConvIntToInt F in_b T out_b`]
  >- (rewrite_tac[convert_int_unsigned_signed_clamp] >>
      MATCH_ACCEPT_TAC int_clamp_unsigned_fixed_certificate) >>
  Cases_on `out_b < in_b`
  >- (disch_then (map_every assume_tac o CONJUNCTS) >>
      drule_all convert_int_signed_narrow_fixed_certificate >> simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all convert_int_signed_wide_fixed_certificate >> simp[]
QED

Theorem convert_int_same_sign_runtime_frame:
  compile_type_convert x (ConvIntToInt signed in_b signed out_b) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  Cases_on `out_b < in_b`
  >- (simp[compile_type_convert_def] >> MATCH_ACCEPT_TAC int_clamp_runtime_frame) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem convert_int_runtime_frame:
  compile_type_convert x (ConvIntToInt in_s in_b out_s out_b) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  Cases_on `in_s` >> Cases_on `out_s`
  >~ [`ConvIntToInt T in_b T out_b`]
  >- MATCH_ACCEPT_TAC convert_int_same_sign_runtime_frame
  >~ [`ConvIntToInt F in_b F out_b`]
  >- MATCH_ACCEPT_TAC convert_int_same_sign_runtime_frame
  >~ [`ConvIntToInt F in_b T out_b`]
  >- (rewrite_tac[convert_int_unsigned_signed_clamp] >>
      MATCH_ACCEPT_TAC int_clamp_runtime_frame) >>
  Cases_on `out_b < in_b`
  >- (strip_tac >> drule_all convert_int_signed_narrow_code >> strip_tac >> gvs[] >>
      drule (SIMP_RULE (srw_ss()) [] (Q.INST
        [`opc1` |-> `GT`, `opc2` |-> `SLT`] (SPEC_ALL scalar_double_check_runtime_frame))) >>
      strip_tac >> simp[]) >>
  strip_tac >> drule_all convert_int_signed_wide_code >> strip_tac >> gvs[] >>
  drule (SIMP_RULE (srw_ss()) [] (Q.INST
    [`opc` |-> `SLT`] (SPEC_ALL scalar_checked_pair_runtime_frame))) >>
  strip_tac >> simp[]
QED

Theorem convert_int_same_sign_instruction_filter:
  compile_type_convert x (ConvIntToInt signed in_b signed out_b) sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Cases_on `out_b < in_b`
  >- (simp[compile_type_convert_def] >> MATCH_ACCEPT_TAC int_clamp_instruction_filter) >>
  simp[compile_type_convert_def, comp_return_def] >> strip_tac >> gvs[emitted_insts_def]
QED

Theorem convert_int_instruction_filter:
  compile_type_convert x (ConvIntToInt in_s in_b out_s out_b) sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Cases_on `in_s` >> Cases_on `out_s`
  >~ [`ConvIntToInt T in_b T out_b`]
  >- MATCH_ACCEPT_TAC convert_int_same_sign_instruction_filter
  >~ [`ConvIntToInt F in_b F out_b`]
  >- MATCH_ACCEPT_TAC convert_int_same_sign_instruction_filter
  >~ [`ConvIntToInt F in_b T out_b`]
  >- (rewrite_tac[convert_int_unsigned_signed_clamp] >>
      MATCH_ACCEPT_TAC int_clamp_instruction_filter) >>
  Cases_on `out_b < in_b`
  >- (strip_tac >> drule_all convert_int_signed_narrow_code >> strip_tac >> gvs[] >>
      simp[mk_inst_def, is_terminator_def]) >>
  strip_tac >> drule_all convert_int_signed_wide_code >> strip_tac >> gvs[] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem convert_int_counted_certificate:
  compile_type_convert x (ConvIntToInt in_s in_b out_s out_b) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_int_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule convert_int_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem convert_int_abort_counted_certificate:
  compile_type_convert x (ConvIntToInt in_s in_b out_s out_b) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th n j.
    gas_path_ptr D 0 ctx fn PG G tn s n H th (Abort err (t with vs_inst_idx := j)) /\
    out = x /\ op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_int_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule convert_int_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`n`,`j`] >> simp[]
QED
