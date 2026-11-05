(* Arbitrary-position execution of the composite decoder head guard. *)
Theory exprSimAbiDecodeCompositePrefix
Ancestors
  abiDecoderComplexGuard abiDecoderSequenceReach abiDecoderReservation
  abiDecoderDynamicLoopSetup
  abiDecoderBytesBound abiDecoderGuard abiDecoderRange instIdxIndep
  abiDecoderComplexHead compileEnv venomState emitHelperProps exprLoweringProps
  venomExecSemantics venomExecProofs venomInstProofs words arithmetic rich_list list

Theorem abi_decode_complex_head_guard_revert:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w p) /\
  eval_operand hi s = SOME (n2w H) /\
  p < dimword(:256) /\ k < dimword(:256) /\ H < dimword(:256) /\
  H < p+k /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  Cases_on `hi = Lit 0w` >- simp[] >>
  simp[abi_decode_complex_head_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w k)] st = (e,c1)` >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w p) /\
   eval_operand hi s1 = SOME (n2w H)` by metis_tac[] >>
  `w2n (n2w (p+k) : bytes32) < w2n (n2w p : bytes32) \/
   w2n (n2w H : bytes32) < w2n (n2w (p+k) : bytes32)` by
    (Cases_on `p+k < dimword(:256)` >> simp[w2n_n2w] >>
     `p+k < 2 * dimword(:256)` by decide_tac >>
     ` (k+p) MOD dimword(:256) = k+p-dimword(:256)` by
       (irule MOD_UNIQUE >> qexists_tac `1` >> decide_tac) >>
     simp[Once ADD_COMM] >> decide_tac) >>
  rule_assum_tac (REWRITE_RULE [word_add_n2w]) >>
  `?t. run_inst_seq (emitted_insts c1 st') s1 = Abort Revert_abort t` by
    (irule abi_decode_range_check_revert >>
     simp[] >> qexistsl_tac [`e`, `n2w H`, `hi`, `n2w p`, `n2w (p+k)`, `src`] >> simp[]) >>
  drule compile_abi_decode_range_check_shape >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[]
QED

Theorem abi_decode_complex_head_guard_prefix_shape:
  abi_decode_complex_head_guard src hi k st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `inst_extends st st'` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  simp[] >> fs[EVERY_MEM]
QED

Theorem composite_prefix_halted[local]:
  !is s t. EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
  run_inst_seq is s = OK t ==> t.vs_halted = s.vs_halted
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  metis_tac[step_preserves_halted, step_inst_non_invoke]
QED

Theorem abi_decode_complex_head_guard_fetched_outcome:
  abi_decode_complex_head_guard src hi k st = ((),st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w p) /\
  eval_operand hi s = SOME (n2w H) /\
  p < dimword(:256) /\ k < dimword(:256) /\ H < dimword(:256) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (p+k <= H /\ ?t. decoder_straight_prefix func s t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decoder_address_frame st.cs_next_var s t) \/
  (H < p+k /\ ?encoded ix.
    run_inst_seq (emitted_insts st st') s = Abort Revert_abort encoded /\
    run_from 0 ctx func s = Abort Revert_abort (encoded with vs_inst_idx := ix))
Proof
  strip_tac >> drule abi_decode_complex_head_guard_prefix_shape >> strip_tac >>
  Cases_on `p+k <= H`
  >- (disj1_tac >> simp[] >>
      `?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
        (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
        t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
        t.vs_data_section = s.vs_data_section /\ inst_extends st st'` by
        (irule abi_decode_complex_head_guard_sequence >>
         simp[] >> qexistsl_tac [`k`, `hi`, `p`, `src`] >> simp[] >>
         qexists_tac `H` >> simp[]) >>
      drule abi_decode_complex_head_guard_shape >> strip_tac >>
      drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
      drule_all composite_prefix_halted >> strip_tac >>
      drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      qexists_tac `t'` >>
      gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]) >>
  disj2_tac >> `H < p+k` by decide_tac >> simp[] >>
  drule_all abi_decode_complex_head_guard_revert >> strip_tac >>
  drule_all abi_decoder_run_sequence_abort >> strip_tac >>
  metis_tac[]
QED
