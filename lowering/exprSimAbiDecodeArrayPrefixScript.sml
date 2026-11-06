(* Arbitrary-input array prefix rejection boundaries. *)
Theory exprSimAbiDecodeArrayPrefix
Ancestors
  abiEncoder abiDecoderDynarrayPrefix abiDecoderBytestringOutcome abiDecoderDynarrayBound
  abiDecoderBytesBound abiDecoderGuards abiDecoderRange abiDecoderGuard abiDecoderContract
  compileEnv emitHelper emitHelperProps exprLoweringProps venomExecSemantics venomState words list

Theorem abi_decode_dynarray_payload_guard_revert:
  abi_decode_dynarray_payload_guard head cnt abi_sz hi st = ((),st') /\
  hi <> Lit 0w /\ eval_operand head s = SOME(n2w a) /\
  eval_operand cnt s = SOME(n2w n) /\ eval_operand hi s = SOME(n2w h) /\
  a < dimword(:256) /\ h < dimword(:256) /\
  n * abi_sz < dimword(:256) /\ h < a + n * abi_sz /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_dynarray_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w abi_sz)] st = (payload,c1)` >>
  rename1 `emit_op ADD [head; payload] c1 = (e,c2)` >>
  `eval_operand (Lit (n2w abi_sz)) s = SOME (n2w abi_sz)` by
    simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[word_mul_n2w] >>
  `eval_operand head s1 = SOME (n2w a)` by metis_tac[] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand head s2 = SOME(n2w a) /\
   eval_operand hi s2 = SOME(n2w h)` by metis_tac[] >>
  `w2n ((n2w a:bytes32) + n2w (n*abi_sz)) < a \/
   h < w2n ((n2w a:bytes32) + n2w (n*abi_sz))` by
    (mp_tac (Q.INST [`a` |-> `a`, `b` |-> `n*abi_sz`, `h` |-> `h`] abi_decode_add_range_iff) >>
     simp[arithmeticTheory.MULT_COMM] >> decide_tac) >>
  `?t. run_inst_seq (emitted_insts c2 st') s2 = Abort Revert_abort t` by
    (drule abi_decode_range_check_revert >>
     disch_then (qspec_then `s2` mp_tac) >>
     simp[w2n_n2w, arithmeticTheory.MULT_COMM]) >>
  `inst_extends c2 st'` by metis_tac[compile_abi_decode_range_check_shape] >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts c1 st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 =
   run_inst_seq (emitted_insts c2 st') s2` by
    (irule run_inst_seq_emit_extend >> simp[]) >> metis_tac[]
QED

Theorem abi_decode_dynarray_position_prefix_revert:
  abi_decode_dynarray_position_prefix src opc base_op hi maxn abi_sz st = (addr,st') /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\
  eval_operand base_op s = SOME(n2w b) /\
  eval_operand hi s = SOME(n2w h) /\
  abi_decode_load opc (n2w (b+p):bytes32) s = n2w n /\
  p < dimword(:256) /\ h < dimword(:256) /\
  n < dimword(:256) /\ maxn < dimword(:256) /\
  (n <= maxn ==> n * abi_sz < dimword(:256)) /\
  (h < p+32 \/ maxn < n \/ h < p+32+n*abi_sz) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[abi_decode_dynarray_position_prefix_trace] >> strip_tac >>
  `inst_extends head_st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule abi_decode_dynarray_payload_guard_shape >> strip_tac >>
  `inst_extends head_st st' /\ inst_extends addr_st st'` by
    metis_tac[inst_extends_trans] >>
  Cases_on `h < p+32`
  >- (drule_all abi_decode_bytes_head_revert >> strip_tac >>
      drule abi_decode_bytes_head_shape >> strip_tac >>
      metis_tac[run_inst_seq_abort_extends]) >>
  `p+32 <= h` by decide_tac >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st head_st) s = OK s1` >>
  `eval_operand base_op s1 = SOME(n2w b) /\
   eval_operand src s1 = SOME(n2w p)` by metis_tac[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts head_st addr_st) s1 = OK s2` >>
  `abi_decode_load opc (n2w (b+p):bytes32) s2 = n2w n` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  Cases_on `maxn < n`
  >- suspend "count"
  >> suspend "payload"
QED

Resume abi_decode_dynarray_position_prefix_revert[count]:
  drule_all abi_decode_count_guard_revert >> strip_tac >>
  `?t. run_inst_seq (emitted_insts addr_st st') s2 = Abort Revert_abort t` by
    metis_tac[run_inst_seq_abort_extends] >>
  `run_inst_seq (emitted_insts head_st st') s1 =
   run_inst_seq (emitted_insts addr_st st') s2` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts head_st st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >> metis_tac[]
QED

Resume abi_decode_dynarray_position_prefix_revert[payload]:
  `n <= maxn /\ h < p+32+n*abi_sz` by decide_tac >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts addr_st count_st) s2 = OK s3` >>
  `eval_operand head s3 = SOME(n2w (p+32)) /\
   eval_operand hi s3 = SOME(n2w h)` by metis_tac[] >>
  `p+32 < dimword(:256)` by decide_tac >>
  `n * abi_sz < dimword(:256)` by metis_tac[] >>
  drule_all abi_decode_dynarray_payload_guard_revert >> strip_tac >>
  `run_inst_seq (emitted_insts addr_st st') s2 =
   run_inst_seq (emitted_insts count_st st') s3` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts head_st st') s1 =
   run_inst_seq (emitted_insts addr_st st') s2` by
    (irule run_inst_seq_emit_extend >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s =
   run_inst_seq (emitted_insts head_st st') s1` by
    (irule run_inst_seq_emit_extend >> simp[]) >> metis_tac[]
QED

Finalise abi_decode_dynarray_position_prefix_revert

Theorem abi_decode_dynarray_position_prefix_outcome:
  abi_decode_dynarray_position_prefix src opc base_op hi maxn abi_sz st = (addr,st') /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w p) /\
  eval_operand base_op s = SOME(n2w b) /\
  eval_operand hi s = SOME(n2w h) /\
  abi_decode_load opc (n2w (b+p):bytes32) s = n2w n /\
  p < dimword(:256) /\ h < dimword(:256) /\
  n < dimword(:256) /\ maxn < dimword(:256) /\
  (n <= maxn ==> n * abi_sz < dimword(:256)) /\
  fresh_vars_wrt st s ==>
  (n <= maxn /\ p+32+n*abi_sz <= h /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
       eval_operand addr t = SOME(n2w (b+p)) /\ fresh_vars_wrt st' t /\
       (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
       t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
       t.vs_data_section = s.vs_data_section /\ inst_extends st st') \/
  ((h < p+32 \/ maxn < n \/ h < p+32+n*abi_sz) /\
   ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t)
Proof
  strip_tac >> Cases_on `n <= maxn /\ p+32+n*abi_sz <= h`
  >- (disj1_tac >> simp[] >>
      irule abi_decode_dynarray_position_prefix_sequence >>
      goal_assum (drule_at Any) >>
      metis_tac[arithmeticTheory.MULT_COMM, arithmeticTheory.ADD_ASSOC]) >>
  disj2_tac >>
  `h < p+32+n*abi_sz \/ maxn < n` by decide_tac >>
  conj_tac >- simp[] >>
  mp_tac abi_decode_dynarray_position_prefix_revert >> simp[]
QED
