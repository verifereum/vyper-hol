Theory abiDecodePtrRejectChecks
Ancestors
  abiDecoderRange abiDecoderVarSequence entryDecodeProps abiEncoder emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst words arithmetic list rich_list

Definition abi_decode_reject_witness_def:
  abi_decode_reject_witness insts s u <=>
    ?pre bad post r.
      insts = pre ++ bad::post /\ run_inst_seq pre s = OK r /\
      EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) pre /\
      abi_decoder_reentry_opcode bad.inst_opcode /\
      abi_decoder_inputs_defined bad r /\
      step_inst_base bad r = Abort Revert_abort u
End

Theorem abi_decode_reject_witness_run:
  abi_decode_reject_witness insts s u ==>
  run_inst_seq insts s = Abort Revert_abort u
Proof
  rw[abi_decode_reject_witness_def] >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `bad::post` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[run_inst_seq_def]
QED

Theorem abi_decode_reject_witness_prefix:
  run_inst_seq pre s = OK r /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) pre /\
  abi_decode_reject_witness rest r u ==>
  abi_decode_reject_witness (pre ++ rest) s u
Proof
  rw[abi_decode_reject_witness_def] >>
  rename1 `run_inst_seq tail r = OK reached` >>
  qexistsl_tac [`pre ++ tail`, `bad`, `post`, `reached`] >>
  simp[APPEND_ASSOC, EVERY_APPEND] >>
  metis_tac[run_inst_seq_append]
QED

Theorem abi_decode_ASSERT_reject_witness:
  emit_void ASSERT [op] st = ((),st') /\ eval_operand op s = SOME 0w ==>
  abi_decode_reject_witness (emitted_insts st st') s
    (revert_state (set_returndata [] s))
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[abi_decode_reject_witness_def] >>
  qexistsl_tac [`[]`, `mk_inst st.cs_next_id ASSERT [op] []`, `[]`, `s`] >>
  simp[run_inst_seq_def, mk_inst_def, abi_decoder_reentry_opcode_def] >>
  conj_tac
  >- (Cases_on `op` >> gvs[abi_decoder_inputs_defined_def, mk_inst_def,
                           eval_operand_def]) >>
  drule step_ASSERT_revert >> simp[mk_inst_def]
QED

Theorem abi_decode_emit_reject_chain:
  inst_extends st mid /\ inst_extends mid last /\
  run_inst_seq (emitted_insts st mid) s = OK r /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st mid) /\
  abi_decode_reject_witness (emitted_insts mid last) r u ==>
  abi_decode_reject_witness (emitted_insts st last) s u
Proof
  strip_tac >>
  `emitted_insts st last = emitted_insts st mid ++ emitted_insts mid last` by
    (fs[inst_extends_def] >>
     qpat_assum `last.cs_current_insts = _` (fn th =>
       once_rewrite_tac[emitted_insts_def, th]) >>
     qpat_assum `mid.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp_tac bool_ss [GSYM LENGTH_APPEND, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp[rich_listTheory.DROP_APPEND1]) >>
  simp[] >> irule abi_decode_reject_witness_prefix >> metis_tac[]
QED

Theorem abi_decode_emit_op_reject_chain:
  emit_op opc ops st = (v,mid) /\ inst_extends mid last /\
  abi_decoder_reentry_opcode opc /\
  run_inst_seq (emitted_insts st mid) s = OK r /\
  abi_decode_reject_witness (emitted_insts mid last) r u ==>
  abi_decode_reject_witness (emitted_insts st last) s u
Proof
  strip_tac >> irule abi_decode_emit_reject_chain >>
  qexistsl_tac [`mid`, `r`] >> simp[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> simp[mk_inst_def]
QED

Theorem abi_decode_range_reject_witness:
  compile_abi_decode_range_check src e hi st = ((),last) /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h /\
  ~(w2n p <= w2n q /\ w2n q <= w2n h) ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op LT [e;src] st = (wrapped,c1)` >>
  rename1 `emit_op ISZERO [wrapped] c1 = (no_wrap,c2)` >>
  rename1 `emit_op GT [e;hi] c2 = (oob,c3)` >>
  rename1 `emit_op ISZERO [oob] c3 = (in_bounds,c4)` >>
  rename1 `emit_op AND [no_wrap;in_bounds] c4 = (ok,c5)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand e s2 = SOME q /\ eval_operand hi s2 = SOME h` by metis_tac[] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand no_wrap s4 = SOME
    (bool_to_word (bool_to_word (w2n q < w2n p) = 0w))` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  `eval_operand ok s5 = SOME 0w` by
    (Cases_on `w2n q < w2n p` >> Cases_on `w2n h < w2n q` >>
     gvs[bool_to_word_def, WORD_AND_CLAUSES]) >>
  drule_all abi_decode_ASSERT_reject_witness >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  imp_res_tac inst_extends_trans >>
  `abi_decoder_reentry_opcode LT /\ abi_decoder_reentry_opcode ISZERO /\
   abi_decoder_reentry_opcode GT /\ abi_decoder_reentry_opcode AND` by
    simp[abi_decoder_reentry_opcode_def] >>
  `inst_extends c1 last /\ inst_extends c2 last` by
    metis_tac[inst_extends_trans] >>
  imp_res_tac emitted_insts_emit_op >>
  qexists_tac `revert_state (set_returndata [] s5)` >>
  irule abi_decode_emit_reject_chain >> qexistsl_tac [`c1`, `s1`] >>
  simp[emitted_insts_emit_op, mk_inst_def] >>
  irule abi_decode_emit_reject_chain >> qexistsl_tac [`c2`, `s2`] >>
  simp[emitted_insts_emit_op, mk_inst_def] >>
  irule abi_decode_emit_reject_chain >> qexistsl_tac [`c3`, `s3`] >>
  simp[emitted_insts_emit_op, mk_inst_def] >>
  irule abi_decode_emit_reject_chain >> qexistsl_tac [`c4`, `s4`] >>
  simp[emitted_insts_emit_op, mk_inst_def] >>
  irule abi_decode_emit_reject_chain >> qexistsl_tac [`c5`, `s5`] >>
  simp[emitted_insts_emit_op, mk_inst_def]
QED

Theorem abi_decode_zero_test_reject_witness:
  emit_op ISZERO [op] st = (ok,mid) /\
  emit_void ASSERT [ok] mid = ((),last) /\
  eval_operand op s = SOME w /\ w <> 0w /\ fresh_vars_wrt st s ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u
Proof
  strip_tac >> drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK reached` >>
  gvs[bool_to_word_def] >>
  drule_all abi_decode_ASSERT_reject_witness >> strip_tac >>
  imp_res_tac inst_extends_emit_void >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac emitted_insts_emit_op >>
  qexists_tac `revert_state (set_returndata [] reached)` >>
  irule abi_decode_emit_reject_chain >>
  qexistsl_tac [`mid`, `reached`] >>
  simp[mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_unsigned_clamp_reject_witness:
  compile_abi_int_clamp op bits F st = ((),last) /\
  eval_operand op s = SOME w /\
  w >>> w2n (n2w bits : bytes32) <> 0w /\ fresh_vars_wrt st s ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u
Proof
  simp_tac bool_ss [compile_abi_int_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SHR [Lit (n2w bits); op] st = (shifted,c1)` >>
  `eval_operand (Lit (n2w bits)) s = SOME (n2w bits)` by simp[eval_operand_def] >>
  drule_all emit_op_SHR_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK reached` >>
  fs[] >> drule_all abi_decode_zero_test_reject_witness >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  imp_res_tac emitted_insts_emit_op >>
  `inst_extends c1 last` by metis_tac[inst_extends_trans] >>
  qexists_tac `u` >> irule abi_decode_emit_reject_chain >>
  qexistsl_tac [`c1`, `reached`] >>
  simp[mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_bytes_clamp_reject_witness:
  compile_abi_bytes_clamp op m st = ((),last) /\
  eval_operand op s = SOME w /\
  w << w2n (n2w (8 * m) : bytes32) <> 0w /\ fresh_vars_wrt st s ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u
Proof
  simp_tac bool_ss [compile_abi_bytes_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SHL [Lit (n2w (8 * m)); op] st = (shifted,c1)` >>
  `step_inst_base (mk_inst st.cs_next_id SHL [Lit (n2w (8 * m)); op]
      [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (w << w2n (n2w (8 * m) : bytes32)) s)` by
    (irule step_SHL >> simp[mk_inst_def, eval_operand_def]) >>
  drule_all decode_emit_update_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK reached` >>
  fs[] >> drule_all abi_decode_zero_test_reject_witness >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  imp_res_tac emitted_insts_emit_op >>
  `inst_extends c1 last` by metis_tac[inst_extends_trans] >>
  qexists_tac `u` >> irule abi_decode_emit_reject_chain >>
  qexistsl_tac [`c1`, `reached`] >>
  simp[mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_signed_clamp_reject_witness:
  compile_abi_int_clamp op bits T st = ((),last) /\
  eval_operand op s = SOME w /\
  sign_extend (n2w (bits DIV 8 - 1)) w <> w /\ fresh_vars_wrt st s ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u
Proof
  simp_tac bool_ss [compile_abi_int_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SIGNEXTEND [Lit (n2w (bits DIV 8 - 1)); op] st = (canon,c1)` >>
  rename1 `emit_op EQ [op;canon] c1 = (ok,c2)` >>
  `step_inst_base (mk_inst st.cs_next_id SIGNEXTEND
      [Lit (n2w (bits DIV 8 - 1)); op]
      [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (sign_extend (n2w (bits DIV 8 - 1)) w) s)` by
    (irule step_SIGNEXTEND >> simp[mk_inst_def, eval_operand_def]) >>
  drule_all decode_emit_update_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand op s1 = SOME w` by metis_tac[] >>
  drule_all emit_op_EQ_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand ok s2 = SOME 0w` by gvs[bool_to_word_def] >>
  drule_all abi_decode_ASSERT_reject_witness >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  imp_res_tac emitted_insts_emit_op >>
  `inst_extends c1 last /\ inst_extends c2 last` by metis_tac[inst_extends_trans] >>
  qexists_tac `revert_state (set_returndata [] s2)` >>
  irule abi_decode_emit_reject_chain >> qexistsl_tac [`c1`, `s1`] >>
  simp[mk_inst_def, abi_decoder_reentry_opcode_def] >>
  irule abi_decode_emit_reject_chain >> qexistsl_tac [`c2`, `s2`] >>
  simp[mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_clamp_reject_witness:
  compile_abi_clamp_basetype op clamp st = ((),last) /\
  eval_operand op s = SOME w /\ ~abi_clamp_ok clamp w /\ fresh_vars_wrt st s ==>
  ?u. abi_decode_reject_witness (emitted_insts st last) s u
Proof
  Cases_on `clamp`
  >- simp[abi_clamp_ok_def]
  >- (rename1 `IntClamp bits signed` >> Cases_on `signed` >>
      simp[compile_abi_clamp_basetype_def, abi_clamp_ok_def] >> strip_tac
      >- (drule_all abi_decode_signed_clamp_reject_witness >> simp[]) >>
      drule_all (SIMP_RULE (srw_ss()) [] abi_decode_unsigned_clamp_reject_witness) >> simp[])
  >- (simp[compile_abi_clamp_basetype_def, abi_clamp_ok_def] >>
      strip_tac >> irule abi_decode_bytes_clamp_reject_witness >>
      simp[] >> qexistsl_tac [`n`, `op`, `w`] >> simp[]) >>
  simp[compile_abi_clamp_basetype_def, abi_clamp_ok_def] >> strip_tac >>
  irule abi_decode_unsigned_clamp_reject_witness >>
  simp[] >> qexistsl_tac [`1`, `op`, `w`] >> simp[compile_abi_int_clamp_def]
QED
