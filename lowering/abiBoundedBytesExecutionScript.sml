(* Total execution for arbitrary bounded memory bytestring payloads. *)
Theory abiBoundedBytesExecution
Ancestors
  abiBoundedLeafExecution abiDecoderBytesBound abiDecoderRange abiDecoderGuard
  abiDecoderGuards abiDecoderContract abiDecoderBytesPrefix abiDecoderBytesRuntime
  abiDecoderBytesPhases abiEncoder emitHelper emitHelperProps exprLoweringProps
  compileEnv venomExecSemantics venomState words arithmetic arithmeticProps

Theorem compile_abi_decode_bad_range_reverts:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand e s = SOME q /\
  eval_operand hi s = SOME h /\ fresh_vars_wrt st s /\
  (w2n q < w2n p \/ w2n h < w2n q) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op LT [e;src] st = (wrapped,c1)` >>
  rename1 `emit_op ISZERO [wrapped] c1 = (no_wrap,c2)` >>
  rename1 `emit_op GT [e;hi] c2 = (oob,c3)` >>
  rename1 `emit_op ISZERO [oob] c3 = (in_bounds,c4)` >>
  rename1 `emit_op AND [no_wrap;in_bounds] c4 = (ok,c5)` >>
  Cases_on `w2n q < w2n p` >> Cases_on `w2n h < w2n q` >> gvs[] >>
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
  `eval_operand no_wrap s4 = SOME (if w2n q < w2n p then 0w else 1w)` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  gvs[WORD_AND_CLAUSES] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  ntac 4 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

Theorem abi_decode_bytes_head_reverts:
  abi_decode_bytes_head src hi st = (head,st') /\ hi <> Lit 0w /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  fresh_vars_wrt st s /\
  (w2n (p + 32w) < w2n p \/ w2n h < w2n (p + 32w)) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  Cases_on `hi = Lit 0w` >- simp[] >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit 32w] st = (end_op,c1)` >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand hi s1 = SOME h` by metis_tac[] >>
  `?t. run_inst_seq (emitted_insts c1 cs'') s1 = Abort Revert_abort t` by
    (drule (Q.INST [`s` |-> `s1`] (SPEC_ALL compile_abi_decode_bad_range_reverts)) >>
     simp[]) >>
  drule compile_abi_decode_range_check_shape >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_le_guard_reverts:
  abi_decode_le_guard a b st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n vb < w2n va /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_le_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [a;b] st = (oob,c1)` >>
  rename1 `emit_op ISZERO [oob] c1 = (ok,c2)` >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem compile_abi_decode_range_check_total:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n p <= w2n q /\ w2n q <= w2n h /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  strip_tac >> Cases_on `w2n p <= w2n q /\ w2n q <= w2n h`
  >- (disj2_tac >> gvs[] >> drule_all compile_abi_decode_range_check_sequence >> simp[]) >>
  disj1_tac >>
  drule compile_abi_decode_bad_range_reverts >>
  disch_then (qspec_then `s` mp_tac) >> simp[]
QED

Theorem abi_decode_bytes_head_total:
  abi_decode_bytes_head src hi st = (head,st') /\ hi <> Lit 0w /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n p + 32 <= w2n h /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     eval_operand head t = SOME (n2w (w2n p + 32)) /\ fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section /\ inst_extends st st')
Proof
  strip_tac >> Cases_on `w2n p + 32 <= w2n h`
  >- (disj2_tac >> simp[] >>
      drule abi_decode_bytes_head_sequence >>
      disch_then (qspecl_then [`w2n p`, `s`, `w2n h`] mp_tac) >> simp[w2n_lt]) >>
  disj1_tac >>
  drule abi_decode_bytes_head_reverts >>
  disch_then (qspec_then `s` mp_tac) >> simp[] >>
  Cases_on `w2n p + 32 < dimword (:256)`
  >- simp[word_add_def, w2n_n2w] >>
  `w2n (p + 32w) < w2n p` by
    (irule w2n_add_overflow >> gvs[dimword_def]) >> simp[]
QED

Theorem abi_decode_count_guard_reverts:
  abi_decode_count_guard opc src limit st = (count_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  limit < w2n (abi_decode_load opc p s) /\ limit < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op opc [src] st = (count_op,c1)` >>
  rename1 `emit_void ASSERT [ok] c3 = ((),last)` >>
  `abi_decode_le_guard count_op (Lit (n2w limit)) c1 = ((),last)` by
    simp[abi_decode_le_guard_def, comp_bind_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  `?t. run_inst_seq (emitted_insts c1 last) s1 = Abort Revert_abort t` by
    (drule abi_decode_le_guard_reverts >>
     disch_then (qspecl_then [`n2w limit`, `abi_decode_load opc p s`, `s1`] mp_tac) >>
     simp[w2n_n2w]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_decode_le_guard_shape >> strip_tac >>
  `inst_extends st c1` by metis_tac[inst_extends_emit_op] >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_count_guard_total:
  abi_decode_count_guard opc src limit st = (count_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  limit < dimword (:256) /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n (abi_decode_load opc p s) <= limit /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     eval_operand count_op t = SOME (abi_decode_load opc p s) /\
     fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  strip_tac >> Cases_on `w2n (abi_decode_load opc p s) <= limit`
  >- (disj2_tac >> simp[] >>
      drule abi_decode_count_guard_sequence >>
      disch_then (qspecl_then [`s`, `p`, `w2n (abi_decode_load opc p s)`] mp_tac) >>
      simp[]) >>
  disj1_tac >> drule abi_decode_count_guard_reverts >>
  disch_then (qspecl_then [`s`, `p`] mp_tac) >> simp[]
QED

Theorem abi_decode_bytes_payload_guard_total:
  abi_decode_bytes_payload_guard head len hi st = ((),st') /\ hi <> Lit 0w /\
  eval_operand head s = SOME p /\ eval_operand len s = SOME n /\
  eval_operand hi s = SOME h /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n p + w2n n <= w2n h /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  Cases_on `hi = Lit 0w` >- simp[] >>
  simp[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [head;len] st = (e,c1)` >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand head s1 = SOME p /\ eval_operand hi s1 = SOME h` by metis_tac[] >>
  drule_all compile_abi_decode_range_check_total >> strip_tac
  >- (disj1_tac >>
      drule compile_abi_decode_range_check_shape >> strip_tac >>
      drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >> metis_tac[]) >>
  disj2_tac >>
  `w2n p + w2n n < dimword (:256)` by
    (spose_not_then assume_tac >>
     `w2n (p + n) < w2n p` by (irule w2n_add_overflow >> simp[]) >>
     decide_tac) >>
  `w2n p + w2n n <= w2n h` by gvs[word_add_def, w2n_n2w] >>
  simp[] >>
  drule compile_abi_decode_range_check_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem abi_decode_bytes_position_prefix_total:
  abi_decode_bytes_position_prefix pos opc base_op hi n st = ((addr,cnt),st') /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\ n < dimword (:256) /\
  eval_operand pos s = SOME (n2w p) /\ p < dimword (:256) /\
  eval_operand base_op s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\ h < dimword (:256) /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (?c t. c <= n /\ p + 32 + c <= h /\
    abi_decode_load opc (n2w (b+p) : bytes32) s = n2w c /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand addr t = SOME (n2w (b+p)) /\
    eval_operand cnt t = SOME (n2w c) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st')
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_position_prefix _ _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[abi_decode_bytes_position_prefix_trace] >> strip_tac >>
  drule_all abi_decode_bytes_head_total >> strip_tac
  >- suspend "head_abort" >>
  rename1 `run_inst_seq (emitted_insts st head_st) s = OK s1` >>
  gvs[w2n_n2w, LESS_MOD] >>
  `eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand pos s1 = SOME (n2w p)` by metis_tac[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts head_st addr_st) s1 = OK s2` >>
  `inst_extends head_st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  `run_inst_seq (emitted_insts st addr_st) s = OK s2 /\
   inst_extends st addr_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `head_st`] >> simp[]) >>
  drule_all abi_decode_count_guard_total >> strip_tac
  >- suspend "count_abort" >>
  rename1 `run_inst_seq (emitted_insts addr_st count_st) s2 = OK s3` >>
  `eval_operand head s3 = SOME (n2w (p+32)) /\
   eval_operand hi s3 = SOME (n2w h)` by metis_tac[] >>
  drule_all abi_decode_bytes_payload_guard_total >> strip_tac
  >- suspend "payload_abort" >>
  suspend "success"
QED

Resume abi_decode_bytes_position_prefix_total[head_abort]:
  disj1_tac >> drule abi_decode_bytes_head_shape >> strip_tac >>
  `inst_extends head_st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  `inst_extends head_st st'` by metis_tac[inst_extends_trans] >>
  drule_all run_inst_seq_abort_extends >> simp[] >> metis_tac[]
QED

Resume abi_decode_bytes_position_prefix_total[count_abort]:
  disj1_tac >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >>
  `inst_extends st count_st` by metis_tac[inst_extends_trans] >>
  drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  irule_at Any run_inst_seq_abort_extends >>
  qexists_tac `count_st` >> simp[]
QED

Resume abi_decode_bytes_position_prefix_total[payload_abort]:
  disj1_tac >> drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

Resume abi_decode_bytes_position_prefix_total[success]:
  disj2_tac >>
  `p+32 < dimword (:256)` by decide_tac >>
  `abi_decode_load opc (n2w (b+p) : bytes32) s2 = abi_decode_load opc (n2w (b+p) : bytes32) s` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  gvs[w2n_n2w, LESS_MOD] >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  `run_inst_seq (emitted_insts st count_st) s = OK s3 /\
   inst_extends st count_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `addr_st`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`, `count_st`] >> simp[]) >>
  qexistsl_tac [`w2n (abi_decode_load opc (n2w (b+p) : bytes32) s)`, `t`] >>
  simp[] >> metis_tac[]
QED

Finalise abi_decode_bytes_position_prefix_total

Theorem abi_decode_bounded_memory_bytes_total:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ p < dimword (:256) /\
  eval_operand base_op s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\
  eval_operand dst s = SOME (n2w d) /\
  b+h < dimword (:256) /\ n+32 < dimword (:256) /\
  d+(32+32*((n+31) DIV 32)) < dimword (:256) /\
  (b+h <= d \/ d+(32+32*((n+31) DIV 32)) <= b) /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (?c t. c <= n /\ p+32+c <= h /\
    abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
    run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
    mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at (b+p) (32+c) s.vs_memory /\
    mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
      REPLICATE (32*((c+31) DIV 32)-c) 0w /\
    abi_decode_frame d (32+32*((n+31) DIV 32)) s t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_prefix_phases, abi_decode_source_opcode_def] >>
  simp_tac bool_ss [comp_bind_def, LET_THM] >> pairarg_tac >>
  disch_tac >> gnvs[] >>
  PairCases_on `ac` >> gnvs[] >>
  `h < dimword (:256) /\ n < dimword (:256)` by decide_tac >>
  drule_all abi_decode_bytes_position_prefix_total >> strip_tac
  >- (disj1_tac >>
      drule_all abi_decode_bytes_position_prefix_shape >> strip_tac >>
      drule abi_decode_bytes_runtime_tail_shape >> strip_tac >>
      drule_all run_inst_seq_abort_extends >> simp[] >> metis_tac[]) >>
  disj2_tac >>
  rename1 `run_inst_seq (emitted_insts st cs') s = OK s1` >>
  `eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `c+31 < dimword (:256) /\ b+p < dimword (:256)` by decide_tac >>
  drule abi_decode_bytes_runtime_tail_memory >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspec_then `n` mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs' st') s1 = OK t` >>
  drule abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_bytes_position_allocation_frame >> strip_tac >>
  qexistsl_tac [`c`, `t`] >>
  FULL_SIMP_TAC std_ss [ADD_ASSOC, ADD_COMM] >>
  qpat_x_assum `abi_decode_frame _ _ s1 t` mp_tac >>
  asm_simp_tac std_ss [abi_decode_frame_def] >> strip_tac >> simp[]
QED
