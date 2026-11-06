Theory abiDecoderRange
Ancestors
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomExecProofs venomInst venomState words arithmetic list rich_list

Theorem abi_decode_pure_emit_frame:
  emit_op opc ops st = (v,st') /\
  (opc = ADD \/ opc = MUL \/ opc = GT \/ opc = LT \/ opc = ISZERO) /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  qpat_x_assum `emit_op _ _ _ = _` kall_tac >>
  qpat_x_assum `st'.cs_current_insts = _` kall_tac >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` SUBST1_TAC) >>
  simp[run_inst_seq_def, mk_inst_def]
  >- (simp[Once step_inst_base_def] >>
      simp[exec_pure2_def, AllCaseEqs(), update_var_def] >> rw[] >> simp[])
  >- (simp[Once step_inst_base_def] >>
      simp[exec_pure2_def, AllCaseEqs(), update_var_def] >> rw[] >> simp[])
  >- (simp[Once step_inst_base_def] >>
      simp[exec_pure2_def, AllCaseEqs(), update_var_def] >> rw[] >> simp[])
  >- (simp[Once step_inst_base_def] >>
      simp[exec_pure2_def, AllCaseEqs(), update_var_def] >> rw[] >> simp[])
  >> simp[Once step_inst_base_def] >>
  simp[exec_pure1_def, AllCaseEqs(), update_var_def] >> rw[] >> simp[]
QED

Theorem abi_decode_AND_emit_frame:
  emit_op AND ops st = (v,st') /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  qpat_x_assum `emit_op _ _ _ = _` kall_tac >>
  qpat_x_assum `st'.cs_current_insts = _` kall_tac >>
  rpt (qpat_x_assum `emitted_insts _ _ = _` SUBST1_TAC) >>
  simp[run_inst_seq_def, mk_inst_def, Once step_inst_base_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >> rw[] >> simp[]
QED

Theorem abi_decode_sequence_chain:
  inst_extends st st1 /\ inst_extends st1 st2 /\
  run_inst_seq (emitted_insts st st1) s = OK s1 /\
  run_inst_seq (emitted_insts st1 st2) s1 = OK s2 ==>
  run_inst_seq (emitted_insts st st2) s = OK s2 /\ inst_extends st st2
Proof
  strip_tac >> conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`s1`, `st1`] >> simp[]) >>
  metis_tac[inst_extends_trans]
QED

Theorem compile_abi_decode_range_check_shape:
  compile_abi_decode_range_check src e hi st = ((),st') ==> inst_extends st st'
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  metis_tac[inst_extends_trans]
QED

Theorem compile_abi_decode_range_check_sequence:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h /\
  w2n p <= w2n q /\ w2n q <= w2n h ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op LT [e;src] st = (wrapped,c1)` >>
  rename1 `emit_op ISZERO [wrapped] c1 = (no_wrap,c2)` >>
  rename1 `emit_op GT [e;hi] c2 = (oob,c3)` >>
  rename1 `emit_op ISZERO [oob] c3 = (in_bounds,c4)` >>
  rename1 `emit_op AND [no_wrap;in_bounds] c4 = (ok,c5)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >>
  `eval_operand e s2 = SOME q /\ eval_operand hi s2 = SOME h` by metis_tac[] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  gvs[bool_to_word_def] >>
  `eval_operand no_wrap s4 = SOME 1w` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  gvs[WORD_AND_IDEM] >> `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> simp[] >> strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `LT`] abi_decode_pure_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `GT`] abi_decode_pure_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ISZERO`, `st` |-> `c1`] abi_decode_pure_emit_frame)) >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ISZERO`, `st` |-> `c3`] abi_decode_pure_emit_frame)) >> strip_tac >>
  `s2.vs_data_section = s1.vs_data_section` by
    (irule (cj 3 abi_decode_pure_emit_frame) >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_decode_AND_emit_frame >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  ntac 5 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  qexists_tac `s5` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!x v. eval_operand x s4 = SOME v ==> _` irule >>
  qpat_x_assum `!x v. eval_operand x s3 = SOME v ==> _` irule >>
  qpat_x_assum `!x v. eval_operand x s2 = SOME v ==> _` irule >>
  qpat_x_assum `!x v. eval_operand x s1 = SOME v ==> _` irule >>
  metis_tac[]
QED

Theorem compile_abi_decode_range_check_fragment_shape:
  compile_abi_decode_range_check src e hi st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\ inst_extends st st'
Proof
  strip_tac >> drule compile_abi_decode_range_check_shape >> strip_tac >>
  gvs[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def,
      rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

(* Position guards precede this address formation; word addition itself is
   valid independently of the nonwrapping interval facts used by consumers. *)
Theorem compile_abi_dec_addr_zero:
  compile_abi_dec_addr (Lit 0w) pos st = (pos,st)
Proof
  simp[compile_abi_dec_addr_def, comp_return_def]
QED

Theorem compile_abi_dec_addr_sequence:
  compile_abi_dec_addr base_op pos st = (out,st') /\
  fresh_vars_wrt st s /\ eval_operand base_op s = SOME (n2w B) /\
  eval_operand pos s = SOME (n2w q) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (n2w (B+q)) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section
Proof
  Cases_on `base_op = Lit 0w`
  >- (strip_tac >> gvs[compile_abi_dec_addr_zero] >>
      `n2w B = (0w:bytes32)` by metis_tac[eval_operand_def, optionTheory.SOME_11] >>
      qexists_tac `s` >>
      rewrite_tac[GSYM word_add_n2w] >>
      asm_simp_tac (srw_ss()) [WORD_ADD_0, emitted_insts_def, run_inst_seq_def]) >>
  simp[compile_abi_dec_addr_def] >> strip_tac >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decode_pure_emit_frame)) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[word_add_n2w]
QED
