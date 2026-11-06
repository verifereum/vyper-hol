Theory bodyPtrTypeBuiltinsScalarArithmetic
Ancestors
  bodyPtrTypeBuiltinsScalarChecks bodyPtrTypeBuiltinsClamp
  bodyPtrTypeBuiltinsScalarOps exprLowering exprLoweringProps fragGasSeqPtr
  convertScalarBytesRun arithmeticProps instSeqComposePtr instIdxIndep fragExec
  compileEnv ptrDiscipline finite_map venomState venomInst list
  venomExecSemantics emitHelperProps ASCIInumbers rich_list

Theorem scalar_emit_fixed_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  emit_op opc [x;y] sa = (out,sb) /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` SUBST_ALL_TAC >>
  qpat_x_assum `out = _` SUBST_ALL_TAC >>
  drule_all scalar_clean_frame_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> conj_tac
  >- (first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  gvs[not_fresh_at_def, toString_inj] >> metis_tac[]
QED

Theorem scalar_emit_runtime_frame:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  emit_op opc [x;y] sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` SUBST_ALL_TAC >>
  `step_inst_base (mk_inst sa.cs_next_id opc [x;y]
     [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all convert_scalar_runtime_frame >> strip_tac >> simp[] >>
  gvs[not_fresh_at_def, toString_inj] >> metis_tac[]
QED

Theorem scalar_emit_instruction_filter:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  emit_op opc [x;y] sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[MEM, mk_inst_def, is_terminator_def]
QED

Theorem scalar_emit_no_abort:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  emit_op opc [x;y] sa = (out,sb) ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` SUBST_ALL_TAC >>
  drule convert_scalar_no_abort >>
  disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` assume_tac) >>
  gvs[run_inst_seq_def, AllCaseEqs()]
QED

Theorem scalar_emit_counted_certificate:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  emit_op opc [x;y] sa = (out,sb) /\
  op_prov G x = NONE /\ op_prov G y = NONE /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all scalar_emit_fixed_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule_all scalar_emit_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem convert_bool_decimal_fixed_certificate:
  compile_type_convert x (ConvBoolToDecimal divisor) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  rewrite_tac[compile_type_convert_def] >> strip_tac >>
  irule scalar_emit_fixed_certificate >>
  simp[] >> qexistsl_tac [`MUL`,`x`,`Lit (n2w divisor)`] >>
  simp[op_prov_def, op_taint_def] >> gvs[op_prov_def, op_taint_def]
QED

Theorem convert_bool_decimal_runtime_frame:
  compile_type_convert x (ConvBoolToDecimal divisor) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  rewrite_tac[compile_type_convert_def] >> strip_tac >>
  irule scalar_emit_runtime_frame >> simp[] >>
  qexistsl_tac [`MUL`,`out`,`sb`,`x`,`Lit (n2w divisor)`] >> simp[]
QED

Theorem convert_bool_decimal_no_abort:
  compile_type_convert x (ConvBoolToDecimal divisor) sa = (out,sb) ==>
  run_inst_seq (emitted_insts sa sb) s <> Abort err t
Proof
  rewrite_tac[compile_type_convert_def] >> strip_tac >>
  irule scalar_emit_no_abort >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem convert_bool_decimal_counted_certificate:
  compile_type_convert x (ConvBoolToDecimal divisor) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!op. op_prov G op = NONE /\ op_taint tn op = {} ==>
      op_prov H op = NONE /\ op_taint th op = {}) /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  rewrite_tac[compile_type_convert_def] >> strip_tac >>
  irule scalar_emit_counted_certificate >>
  simp[] >> qexistsl_tac [`MUL`,`x`,`Lit (n2w divisor)`] >>
  simp[op_prov_def, op_taint_def] >> gvs[op_prov_def, op_taint_def]
QED

Theorem int_clamp_emission_extends:
  compile_int_clamp signed bits x sa = (out,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb
Proof
  rewrite_tac[scalar_int_clamp_eq] >>
  MATCH_ACCEPT_TAC clamp_and_return_extends
QED

Theorem convert_bytes_int_decompose:
  compile_type_convert x (ConvBytesToInt m signed bits) sa = (out,sb) ==>
  ?shifted mid.
    emit_op (if signed then SAR else SHR) [Lit (n2w ((32-m)*8));x]
      sa = (shifted,mid) /\
    (if bits < m*8 then compile_int_clamp signed bits shifted mid = (out,sb)
     else out = shifted /\ sb = mid) /\
    emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb /\
    (!p. not_fresh_at sa p ==> not_fresh_at mid p)
Proof
  simp[compile_type_convert_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >>
  rename1 `(if signed then emit_op SAR _ else emit_op SHR _) sa = (shifted,mid)` >>
  `emit_op (if signed then SAR else SHR) [Lit (n2w ((32-m)*8));x]
    sa = (shifted,mid)` by (Cases_on `signed` >> gvs[]) >>
  qexistsl_tac [`shifted`,`mid`] >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >> gvs[] >>
  Cases_on `bits < m*8` >> gvs[comp_return_def]
  >- (conj_tac
      >- (drule int_clamp_emission_extends >> strip_tac >>
          qspecl_then [`sa`,`mid`,`sb`] mp_tac emitted_insts_append >> simp[]) >>
      gvs[not_fresh_at_def] >> rpt strip_tac >> gvs[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[emitted_insts_def, not_fresh_at_def] >> rpt strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem scalar_emit_prefix_run:
  MEM opc [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
  emit_op opc [x;y] sa = (out,sb) /\
  (run_inst_seq (emitted_insts sa sb ++ ys) s = OK t \/
   run_inst_seq (emitted_insts sa sb ++ ys) s = Abort err t) ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    (run_inst_seq ys u = OK t \/ run_inst_seq ys u = Abort err t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` SUBST_ALL_TAC >>
  drule convert_scalar_no_abort >>
  disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` assume_tac) >>
  qpat_x_assum `_ \/ _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem convert_bytes_int_fixed_certificate:
  compile_type_convert x (ConvBytesToInt m signed bits) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  (run_inst_seq (emitted_insts sa sb) s = OK t \/
   run_inst_seq (emitted_insts sa sb) s = Abort err t) ==>
  ?H th.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s H th /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule convert_bytes_int_decompose >> strip_tac >>
  `MEM (if signed then SAR else SHR)
    [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV] /\
    op_prov G (Lit (n2w ((32-m)*8))) = NONE /\
    op_taint tn (Lit (n2w ((32-m)*8))) = {}` by
      (Cases_on `signed` >> simp[op_prov_def, op_taint_def]) >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
  drule_all scalar_emit_prefix_run >>
  disch_then (qx_choose_then `u` (map_every assume_tac o CONJUNCTS)) >>
  drule_all scalar_emit_fixed_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  qpat_x_assum `MEM _ _` kall_tac >>
  Cases_on `bits < m*8` >> gnvs[]
  >- (drule int_clamp_instruction_filter >> strip_tac >>
      `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts mid sb)` by
        (gvs[EVERY_MEM] >> metis_tac[]) >>
      `run_inst_seq (emitted_insts mid sb)
         (u with vs_inst_idx := SUC s.vs_inst_idx) =
         OK (t with vs_inst_idx := SUC s.vs_inst_idx) \/
       run_inst_seq (emitted_insts mid sb)
         (u with vs_inst_idx := SUC s.vs_inst_idx) =
         Abort err (t with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qpat_x_assum `run_inst_seq (emitted_insts mid sb) u = _ \/ _` strip_assume_tac >>
         simp[run_inst_seq_inst_idx, exec_result_map_def]) >>
      qpat_x_assum `run_inst_seq (emitted_insts mid sb) u = _ \/ _` kall_tac >>
      FIRST [drule_all (cj 1 (PURE_REWRITE_RULE
        [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] int_clamp_fixed_certificate)),
        drule_all (cj 2 (PURE_REWRITE_RULE
        [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] int_clamp_fixed_certificate))] >>
      disch_then (qspecl_then [`fn`,`PG`,`D`]
        (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
      qexistsl_tac [`H`,`th`] >>
      (conj_tac
       >- (drule emitted_insts_emit_op >> strip_tac >>
           qpat_x_assum `emitted_insts sa mid = _` SUBST_ALL_TAC >>
           gvs[inst_seq_ptr_def, run_inst_seq_def, AllCaseEqs()])) >>
      simp[] >> metis_tac[]) >>
  `emitted_insts mid mid = []` by simp[emitted_insts_def] >>
  qexistsl_tac [`G1`,`tn1`] >> simp[]
QED

Theorem convert_bytes_int_instruction_filter:
  compile_type_convert x (ConvBytesToInt m signed bits) sa = (out,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> drule convert_bytes_int_decompose >> strip_tac >>
  `MEM (if signed then SAR else SHR)
    [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by
    (Cases_on `signed` >> simp[]) >>
  drule_all scalar_emit_instruction_filter >> strip_tac >>
  qpat_x_assum `MEM _ _` kall_tac >>
  Cases_on `bits < m*8` >> gvs[]
  >- (drule int_clamp_instruction_filter >> strip_tac >> simp[FILTER_APPEND]) >>
  simp[emitted_insts_def] >> gvs[emitted_insts_def]
QED

Theorem convert_bytes_int_runtime_frame:
  compile_type_convert x (ConvBytesToInt m signed bits) sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
Proof
  strip_tac >> drule convert_bytes_int_decompose >> strip_tac >>
  `MEM (if signed then SAR else SHR)
    [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by
    (Cases_on `signed` >> simp[]) >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
  `?u. run_inst_seq (emitted_insts sa mid) s = OK u /\
       run_inst_seq (emitted_insts mid sb) u = OK t` by
    (`?u. run_inst_seq (emitted_insts sa mid) s = OK u /\
       (run_inst_seq (emitted_insts mid sb) u = OK t \/
        run_inst_seq (emitted_insts mid sb) u = Abort Revert_abort t)` by
       (irule scalar_emit_prefix_run >> simp[] >>
        goal_assum (drule_at Any) >> Cases_on `signed` >> simp[]) >>
     qexists_tac `u` >> simp[] >>
     drule run_inst_seq_append >> disch_then (qspec_then `emitted_insts mid sb` mp_tac) >>
     simp[]) >>
  drule_all scalar_emit_runtime_frame >> strip_tac >>
  qpat_x_assum `MEM _ _` kall_tac >>
  Cases_on `bits < m*8` >> gvs[]
  >- (drule_all int_clamp_runtime_frame >> strip_tac >>
      conj_tac
      >- (`(t with vs_vars := s.vs_vars) =
             ((t with vs_vars := u.vs_vars) with vs_vars := s.vs_vars)` by simp[] >>
          metis_tac[]) >> metis_tac[]) >>
  gvs[emitted_insts_def, run_inst_seq_def]
QED

Theorem convert_bytes_int_counted_certificate:
  compile_type_convert x (ConvBytesToInt m signed bits) sa = (out,sb) /\
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
  strip_tac >>
  drule_all (cj 1 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_bytes_int_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >> simp[] >>
  drule convert_bytes_int_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem convert_bytes_int_abort_counted_certificate:
  compile_type_convert x (ConvBytesToInt m signed bits) sa = (out,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = Abort err t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?H th n j.
    gas_path_ptr D 0 ctx fn PG G tn s n H th (Abort err (t with vs_inst_idx := j)) /\
    op_prov H out = NONE /\ op_taint th out = {} /\
    (!p. not_fresh_at sa p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all (cj 2 (PURE_REWRITE_RULE
    [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, DISJ_IMP_THM] convert_bytes_int_fixed_certificate)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule convert_bytes_int_instruction_filter >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`H`,`th`,`n`,`j`] >> simp[]
QED

Theorem convert_bytes_address_eq:
  compile_type_convert x (ConvBytesToAddress m) =
  compile_type_convert x (ConvBytesToInt m F 160)
Proof
  simp[compile_type_convert_def, compile_int_clamp_def]
QED
