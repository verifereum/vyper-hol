Theory exprSimAbiDecodeBuiltinHeader
Ancestors
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests abiBuiltinPrefix
  abiDecoderClampOutcome abiDecoderSequenceReach abiDecoderFiniteControl abiDecoderReentry abiDecoderDynamicLoopSetup
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words list arithmetic

Theorem abi_decode_builtin_eq_guard_revert:
  abi_builtin_eq_guard lhs rhs st = ((),last) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  a <> b /\ last.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t
Proof
  simp_tac bool_ss [abi_builtin_eq_guard_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op EQ [lhs;rhs] st = (valid,middle)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `?t. eval_operand valid t = SOME 0w /\
    abi_builtin_prefix st middle limit_st s t` by
    (irule abi_builtin_emit_binary >> simp[] >>
     qexistsl_tac [`a`, `b`, `lhs`, `EQ`, `rhs`] >> simp[bool_to_word_def]) >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  fs[abi_builtin_prefix_def] >> imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st last) s =
   run_inst_seq (emitted_insts middle last) t` by
    (irule run_inst_seq_emit_extend >> simp[]) >> metis_tac[]
QED

Theorem abi_decode_builtin_bound_test_value:
  abi_builtin_bound_test opc lhs rhs st = (out,last) /\
  ((opc = LT /\ bad = (w2n a < w2n b)) \/
   (opc = GT /\ bad = (w2n a > w2n b))) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME (bool_to_word (~bad)) /\
    abi_builtin_prefix st last limit_st s t
Proof
  simp_tac bool_ss [abi_builtin_bound_test_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  (rename1 `emit_op _ [lhs;rhs] st = (tmp,middle)` >>
   imp_res_tac emitted_insts_emit_op >>
   `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
   qmatch_goalsub_abbrev_tac `bool_to_word (~test)` >>
   `?t. eval_operand tmp t = SOME (bool_to_word test) /\
        abi_builtin_prefix st middle limit_st s t` by
     (irule abi_builtin_emit_binary >> simp[Abbr `test`] >> metis_tac[]) >>
   rename1 `abi_builtin_prefix st middle limit_st s prepared` >>
   `fresh_vars_wrt limit_st prepared` by fs[abi_builtin_prefix_def] >>
   drule_all abi_builtin_emit_iszero >> strip_tac >>
   `st.cs_next_var <= middle.cs_next_var` by decide_tac >>
   drule_all abi_builtin_prefix_chain >> strip_tac >>
   qexists_tac `t` >> Cases_on `test` >> gvs[bool_to_word_def])
QED

Theorem abi_decode_builtin_interval_guard_revert:
  abi_builtin_interval_guard len lo hi st = ((),last) /\
  eval_operand len s = SOME(n2w cnt) /\
  lo < dimword(:256) /\ hi < dimword(:256) /\ cnt < dimword(:256) /\
  ~(lo <= cnt /\ cnt <= hi) /\
  abi_decoder_operand_live st.cs_next_var len /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t
Proof
  simp_tac bool_ss [abi_builtin_interval_guard_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_bound_test LT len (Lit (n2w lo)) st = (ge,c1)` >>
  rename1 `abi_builtin_bound_test GT len (Lit (n2w hi)) c1 = (le,c2)` >>
  rename1 `emit_op AND [ge;le] c2 = (valid,c3)` >>
  imp_res_tac abi_builtin_bound_test_shape >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `c1.cs_next_var <= limit_st.cs_next_var /\
   c2.cs_next_var <= limit_st.cs_next_var /\
   c3.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   st.cs_next_var <= c2.cs_next_var` by decide_tac >>
  `?s1. eval_operand ge s1 = SOME(bool_to_word (~(cnt < lo))) /\
    abi_builtin_prefix st c1 limit_st s s1` by
    (irule abi_decode_builtin_bound_test_value >> simp[] >>
     qexistsl_tac [`n2w cnt`, `n2w lo`, `len`, `LT`, `Lit (n2w lo)`] >>
     simp[eval_operand_def, w2n_n2w]) >>
  `eval_operand len s1 = SOME(n2w cnt) /\ fresh_vars_wrt limit_st s1` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  `?s2. eval_operand le s2 = SOME(bool_to_word (~(cnt > hi))) /\
    abi_builtin_prefix c1 c2 limit_st s1 s2` by
    (irule abi_decode_builtin_bound_test_value >> simp[] >>
     qexistsl_tac [`n2w cnt`, `n2w hi`, `len`, `GT`, `Lit (n2w hi)`] >>
     simp[eval_operand_def, w2n_n2w]) >>
  `eval_operand ge s2 = SOME(bool_to_word (~(cnt < lo))) /\
    fresh_vars_wrt limit_st s2` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  `?s3. eval_operand valid s3 = SOME 0w /\
    abi_builtin_prefix c2 c3 limit_st s2 s3` by
    (irule abi_builtin_emit_binary >> simp[] >>
     qexistsl_tac [`bool_to_word (~(cnt < lo)):bytes32`,
       `bool_to_word (~(cnt > hi)):bytes32`, `ge`, `AND`, `le`] >>
     simp[] >> Cases_on `cnt < lo` >> Cases_on `cnt > hi` >>
     gvs[bool_to_word_def, WORD_AND_CLAUSES, WORD_AND_IDEM]) >>
  `abi_builtin_prefix st c2 limit_st s s2` by metis_tac[abi_builtin_prefix_chain] >>
  `abi_builtin_prefix st c3 limit_st s s3` by metis_tac[abi_builtin_prefix_chain] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  fs[abi_builtin_prefix_def] >>
  imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st last) s =
   run_inst_seq (emitted_insts c3 last) s3` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  metis_tac[]
QED

Theorem abi_decode_builtin_length_guard_revert:
  abi_builtin_length_guard len lo hi st = ((),last) /\
  eval_operand len s = SOME(n2w cnt) /\
  lo < dimword(:256) /\ hi < dimword(:256) /\ cnt < dimword(:256) /\
  ~(lo <= cnt /\ cnt <= hi) /\
  abi_decoder_operand_live st.cs_next_var len /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t
Proof
  Cases_on `lo = hi`
  >- (gvs[abi_builtin_length_guard_def] >> strip_tac >>
      irule abi_decode_builtin_eq_guard_revert >>
      (reverse conj_tac >- (qexists_tac `limit_st` >> simp[])) >>
      qexistsl_tac [`n2w cnt`, `n2w hi`, `len`, `Lit (n2w hi)`] >>
      simp[eval_operand_def, n2w_11] >> decide_tac) >>
  simp[abi_builtin_length_guard_def] >> strip_tac >>
  irule abi_decode_builtin_interval_guard_revert >> metis_tac[]
QED

Theorem abi_decode_builtin_header_revert:
  abi_builtin_decode_header data lo hi st = (inputs,last) /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  lo < dimword(:256) /\ hi < dimword(:256) /\ cnt < dimword(:256) /\
  ~(lo <= cnt /\ cnt <= hi) /\
  abi_decoder_operand_live st.cs_next_var data /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t
Proof
  simp_tac bool_ss [abi_builtin_decode_header_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op MLOAD [data] st = (len,c1)` >>
  rename1 `emit_op ADD [data;Lit 32w] c1 = (src,c2)` >>
  rename1 `abi_builtin_length_guard len lo hi c2 = ((),last)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  drule abi_builtin_length_guard_shape >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= c1.cs_next_var` by decide_tac >>
  drule_all abi_builtin_emit_load >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s s1` >>
  `eval_operand data s1 = SOME p /\ fresh_vars_wrt limit_st s1` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  `?s2. eval_operand src s2 = SOME(p+32w) /\
    abi_builtin_prefix c1 c2 limit_st s1 s2` by
    (irule abi_builtin_emit_add >> simp[] >>
     qexistsl_tac [`data`, `Lit 32w`] >> simp[eval_operand_def]) >>
  `eval_operand len s2 = SOME(n2w cnt) /\ fresh_vars_wrt limit_st s2` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  `abi_builtin_prefix st c2 limit_st s s2` by metis_tac[abi_builtin_prefix_chain] >>
  `abi_decoder_operand_live c2.cs_next_var len` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `c1.cs_next_var` >> simp[]) >>
  `?t. run_inst_seq (emitted_insts c2 last) s2 = Abort Revert_abort t` by
    (irule abi_decode_builtin_length_guard_revert >>
     (reverse conj_tac >- (qexists_tac `limit_st` >> simp[])) >>
     qexistsl_tac [`cnt`, `hi`, `len`, `lo`] >> simp[] >> decide_tac) >>
  fs[abi_builtin_prefix_def] >>
  `run_inst_seq (emitted_insts st last) s =
   run_inst_seq (emitted_insts c2 last) s2` by
    (irule run_inst_seq_emit_extend >> simp[]) >> metis_tac[]
QED

Theorem abi_decode_builtin_header_abort:
  abi_builtin_decode_header data lo hi st = (inputs,last) /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  lo < dimword(:256) /\ hi < dimword(:256) /\ cnt < dimword(:256) /\
  ~(lo <= cnt /\ cnt <= hi) /\
  abi_decoder_operand_live st.cs_next_var data /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st last fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. Dabort ctx fn s Revert_abort t
Proof
  strip_tac >> drule_all abi_decode_builtin_header_revert >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st last)` by fs[EVERY_MEM] >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  simp[Dabort_def] >> metis_tac[]
QED
