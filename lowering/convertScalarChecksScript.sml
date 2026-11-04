Theory convertScalarChecks
Ancestors
  convertScalarDecimal exprSimConvert exprLoweringProps emitHelperProps
  arithmeticProps emitHelper exprLowering venomInst venomState
  venomExecSemantics words integer integer_word

Theorem scalar_run_suffix:
  !st0 st1 st2 ss mid result.
    st1.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 st1 /\
    st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2 /\
    run_inst_seq (emitted_insts st0 st1) ss = OK mid /\
    run_inst_seq (emitted_insts st1 st2) mid = result ==>
    run_inst_seq (emitted_insts st0 st2) ss = result
Proof
  metis_tac[run_inst_seq_chain]
QED

Theorem scalar_assert_zero_extends:
  !x st0 ok st1 st2.
    emit_op ISZERO [x] st0 = (ok,st1) /\
    emit_void ASSERT [ok] st1 = ((),st2) ==>
    st2.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 st2
Proof
  rpt strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `emitted_insts st0 st2 = emitted_insts st0 st1 ++ emitted_insts st1 st2` by
    (irule emitted_insts_append >> simp[]) >>
  simp[]
QED

Theorem scalar_assert_zero_ok:
  !x st0 ok st1 st2 ss.
    emit_op ISZERO [x] st0 = (ok,st1) /\
    emit_void ASSERT [ok] st1 = ((),st2) /\
    eval_operand x ss = SOME 0w /\ fresh_vars_wrt st0 ss ==>
    ?ss'. run_inst_seq (emitted_insts st0 st2) ss = OK ss' /\
      fresh_vars_wrt st2 ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st0 st2
Proof
  rpt strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `eval_operand ok s_checked = SOME _` >>
  imp_res_tac emit_op_extends >>
  `eval_operand ok s_checked = SOME 1w` by gvs[] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok >> strip_tac >>
  imp_res_tac emit_void_extends >>
  imp_res_tac fresh_vars_wrt_emit_void >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[] >>
  metis_tac[same_blocks_def]
QED

Theorem scalar_assert_zero_abort:
  !x w st0 ok st1 st2 ss.
    emit_op ISZERO [x] st0 = (ok,st1) /\
    emit_void ASSERT [ok] st1 = ((),st2) /\
    eval_operand x ss = SOME w /\ w <> 0w /\ fresh_vars_wrt st0 ss ==>
    ?ss'. run_inst_seq (emitted_insts st0 st2) ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `eval_operand ok s_checked = SOME _` >>
  imp_res_tac emit_op_extends >>
  `eval_operand ok s_checked = SOME 0w` by gvs[] >>
  drule_all emit_void_ASSERT_revert >> strip_tac >>
  imp_res_tac emit_void_extends >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem scalar_signed_lower_ok:
  !x c w st0 bad st1 ok st2 st3 ss.
    emit_op SLT [x; Lit c] st0 = (bad,st1) /\
    emit_op ISZERO [bad] st1 = (ok,st2) /\
    emit_void ASSERT [ok] st2 = ((),st3) /\
    eval_operand x ss = SOME w /\ ~word_lt w c /\
    fresh_vars_wrt st0 ss ==>
    ?ss'. run_inst_seq (emitted_insts st0 st3) ss = OK ss' /\
      fresh_vars_wrt st3 ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st0 st3
Proof
  rpt strip_tac >>
  `eval_operand (Lit c) ss = SOME c` by simp[eval_operand_def] >>
  drule_all emit_op_SLT_correct >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `eval_operand ok s_checked = SOME _` >>
  imp_res_tac emit_op_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `run_inst_seq (emitted_insts st0 st2) ss = OK s_checked` by gvs[] >>
  `eval_operand ok s_checked = SOME 1w` by gvs[] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok >> strip_tac >>
  imp_res_tac emit_void_extends >>
  imp_res_tac fresh_vars_wrt_emit_void >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[] >>
  metis_tac[same_blocks_def]
QED

Theorem scalar_signed_lower_abort:
  !x c w st0 bad st1 ok st2 st3 ss.
    emit_op SLT [x; Lit c] st0 = (bad,st1) /\
    emit_op ISZERO [bad] st1 = (ok,st2) /\
    emit_void ASSERT [ok] st2 = ((),st3) /\
    eval_operand x ss = SOME w /\ word_lt w c /\
    fresh_vars_wrt st0 ss ==>
    ?ss'. run_inst_seq (emitted_insts st0 st3) ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `eval_operand (Lit c) ss = SOME c` by simp[eval_operand_def] >>
  drule_all emit_op_SLT_correct >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `eval_operand ok s_checked = SOME _` >>
  imp_res_tac emit_op_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `run_inst_seq (emitted_insts st0 st2) ss = OK s_checked` by gvs[] >>
  `eval_operand ok s_checked = SOME 0w` by gvs[] >>
  drule_all emit_void_ASSERT_revert >> strip_tac >>
  imp_res_tac emit_void_extends >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem scalar_signed_upper_ok:
  !x c w st0 bad st1 ok st2 st3 ss.
    emit_op SGT [x; Lit c] st0 = (bad,st1) /\
    emit_op ISZERO [bad] st1 = (ok,st2) /\
    emit_void ASSERT [ok] st2 = ((),st3) /\
    eval_operand x ss = SOME w /\ ~word_gt w c /\
    fresh_vars_wrt st0 ss ==>
    ?ss'. run_inst_seq (emitted_insts st0 st3) ss = OK ss' /\
      fresh_vars_wrt st3 ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st0 st3
Proof
  rpt strip_tac >>
  `eval_operand (Lit c) ss = SOME c` by simp[eval_operand_def] >>
  drule_all emit_op_SGT_correct >> strip_tac >>
  rename1 `eval_operand bad s_compared = SOME _` >>
  `eval_operand bad s_compared = SOME 0w` by gvs[] >>
  drule_all scalar_assert_zero_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st3) mid = OK final` >>
  drule_all scalar_assert_zero_extends >> strip_tac >>
  qpat_assum `emit_op SGT _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qexists_tac `final` >> conj_tac
  >- (irule scalar_run_suffix >> qexistsl_tac [`mid`, `st1`] >> simp[]) >>
  simp[] >> gvs[same_blocks_def]
QED

Theorem scalar_signed_upper_abort:
  !x c w st0 bad st1 ok st2 st3 ss.
    emit_op SGT [x; Lit c] st0 = (bad,st1) /\
    emit_op ISZERO [bad] st1 = (ok,st2) /\
    emit_void ASSERT [ok] st2 = ((),st3) /\
    eval_operand x ss = SOME w /\ word_gt w c /\
    fresh_vars_wrt st0 ss ==>
    ?ss'. run_inst_seq (emitted_insts st0 st3) ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `eval_operand (Lit c) ss = SOME c` by simp[eval_operand_def] >>
  drule_all emit_op_SGT_correct >> strip_tac >>
  rename1 `eval_operand bad s_compared = SOME _` >>
  `eval_operand bad s_compared = SOME 1w` by gvs[] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all scalar_assert_zero_abort >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st3) mid = Abort Revert_abort final` >>
  drule_all scalar_assert_zero_extends >> strip_tac >>
  qpat_assum `emit_op SGT _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qexists_tac `final` >>
  irule scalar_run_suffix >> qexistsl_tac [`mid`, `st1`] >> simp[]
QED

Theorem scalar_unsigned_upper_ok:
  !x c w st0 bad st1 ok st2 st3 ss.
    emit_op GT [x; Lit c] st0 = (bad,st1) /\
    emit_op ISZERO [bad] st1 = (ok,st2) /\
    emit_void ASSERT [ok] st2 = ((),st3) /\
    eval_operand x ss = SOME w /\ w2n w <= w2n c /\
    fresh_vars_wrt st0 ss ==>
    ?ss'. run_inst_seq (emitted_insts st0 st3) ss = OK ss' /\
      fresh_vars_wrt st3 ss' /\
      (!op v. eval_operand op ss = SOME v ==> eval_operand op ss' = SOME v) /\
      same_blocks st0 st3
Proof
  rpt strip_tac >>
  `eval_operand (Lit c) ss = SOME c` by simp[eval_operand_def] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `eval_operand bad s_compared = SOME _` >>
  `eval_operand bad s_compared = SOME 0w` by gvs[] >>
  drule_all scalar_assert_zero_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st3) mid = OK final` >>
  drule_all scalar_assert_zero_extends >> strip_tac >>
  qpat_assum `emit_op GT _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qexists_tac `final` >> conj_tac
  >- (irule scalar_run_suffix >> qexistsl_tac [`mid`, `st1`] >> simp[]) >>
  simp[] >> gvs[same_blocks_def]
QED

Theorem scalar_unsigned_upper_abort:
  !x c w st0 bad st1 ok st2 st3 ss.
    emit_op GT [x; Lit c] st0 = (bad,st1) /\
    emit_op ISZERO [bad] st1 = (ok,st2) /\
    emit_void ASSERT [ok] st2 = ((),st3) /\
    eval_operand x ss = SOME w /\ w2n c < w2n w /\
    fresh_vars_wrt st0 ss ==>
    ?ss'. run_inst_seq (emitted_insts st0 st3) ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `eval_operand (Lit c) ss = SOME c` by simp[eval_operand_def] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `eval_operand bad s_compared = SOME _` >>
  `eval_operand bad s_compared = SOME 1w` by gvs[] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all scalar_assert_zero_abort >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st3) mid = Abort Revert_abort final` >>
  drule_all scalar_assert_zero_extends >> strip_tac >>
  qpat_assum `emit_op GT _ _ = _` (mp_then Any strip_assume_tac emit_op_extends) >>
  qexists_tac `final` >>
  irule scalar_run_suffix >> qexistsl_tac [`mid`, `st1`] >> simp[]
QED
