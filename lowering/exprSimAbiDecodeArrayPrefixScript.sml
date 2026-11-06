(* Arbitrary-input array prefix rejection boundaries. *)
Theory exprSimAbiDecodeArrayPrefix
Ancestors
  abiDecoderDynarrayPrefix abiDecoderBytestringOutcome abiDecoderDynarrayBound
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
