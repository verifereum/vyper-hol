(* Finite bytestring execution and replay in states with stale temporaries. *)
Theory abiDecodeMemBytesReentry
Ancestors
  abiDecodeMemFiniteGuards abiDecodeMemBytes abiDecodeMemBytesGuards abiDecodeMemRange arithmeticProps
  abiDecoderBytesFrame abiDecoderBytesPhases abiDecoderBytesPrefix
  abiDecoderBytesBound abiDecoderBytesRuntime abiDecoderBytesEdges
  abiDecoderBytes abiDecoderRange abiDecoderGuards abiDecoderContract
  abiDecodeMemSequenceReentry abiDecoderReentry
  abiDecoderVarSequence abiDecoderVarExtend abiDecoderFrame abiDecoderFrameCompose
  freshWrites instMemFrontier memSafeRun fragExecMem
  entryDecoderSetupEndpoint
  abiEncoder emitHelperProps exprLoweringProps loweringStateRelDefs compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_bytes_finite_mem:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\ eval_operand hi s = SOME (n2w h) /\
  p < dimword (:256) /\ b+h < dimword (:256) /\ b+h <= s.vs_alloca_next /\
  d+32+32*((n+31) DIV 32) < dimword (:256) /\
  d+32+32*((n+31) DIV 32) <= s.vs_alloca_next /\
  fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\
  ((?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
   (?t. run_inst_seq (emitted_insts st en) s = OK t /\
      fresh_vars_wrt en t /\ abi_decode_frame d (32+32*((n+31) DIV 32)) s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next))
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_position_phases, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_bytes_head pos hi st = (head,c1)` >>
  rename1 `compile_abi_dec_addr base_op pos c1 = (addr,c2)` >>
  rename1 `abi_decode_count_guard MLOAD addr n c2 = (cnt,c3)` >>
  rename1 `abi_decode_bytes_payload_guard head cnt hi c3 = ((),c4)` >>
  `emit_op ADD [base_op;pos] c1 = (addr,c2)` by gvs[compile_abi_dec_addr_def] >>
  drule abi_decode_bytes_head_shape >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  drule_all abi_decode_count_guard_shape >> strip_tac >>
  drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  drule abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  `inst_extends c1 en /\ inst_extends c2 en /\ inst_extends c3 en /\
   inst_extends st c2 /\ inst_extends st c3 /\ inst_extends st c4` by
    metis_tac[inst_extends_trans] >>
  drule_all abi_decode_bytes_head_sequence_mem >> strip_tac >>
  Cases_on `w2n (n2w p : bytes32) <= w2n (n2w p+32w : bytes32) /\
    w2n (n2w p+32w : bytes32) <= w2n (n2w h : bytes32)`
  >- suspend "head_accept" >>
  suspend "head_reject"
QED
Resume abi_decode_bytes_finite_mem[head_reject]:
  `?t. run_inst_seq (emitted_insts st c1) s = Abort Revert_abort t` by metis_tac[] >>
  `emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 en` by
    (irule emitted_insts_append >> fs[inst_extends_def, APPEND_ASSOC] >> metis_tac[APPEND_ASSOC, APPEND_11]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  disj1_tac >> metis_tac[run_inst_seq_abort_extends]
QED
Resume abi_decode_bytes_finite_mem[head_accept]:
  `p+32 < dimword (:256)` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPECL [`n2w p`, `32w`] w2n_add_overflow) >> gvs[w2n_n2w]) >>
  `h < dimword (:256) /\ p+32 <= h` by gvs[word_add_n2w, w2n_n2w] >>
  gvs[word_add_n2w, w2n_n2w] >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand base_op s1 = SOME (n2w b) /\ eval_operand pos s1 = SOME (n2w p)`
    by metis_tac[] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `s2.vs_allocas = s1.vs_allocas /\ s2.vs_alloca_next = s1.vs_alloca_next` by
    (qpat_x_assum `emit_op ADD [base_op;pos] _ = _`
      (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, update_var_def, eval_operand_def] >> strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts c1 c2) s1` by
    (drule emitted_insts_emit_op >> strip_tac >>
     irule run_inst_seq_mem_ok_every >>
     simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def,
       is_alloca_op_def]) >>
  `b+p < dimword (:256) /\ w2n (n2w (b+p):bytes32)+32 <= s2.vs_alloca_next`
    by (simp[w2n_n2w] >> decide_tac) >>
  `eval_operand addr s2 = SOME (n2w (b+p))` by gvs[word_add_n2w] >>
  `n < dimword (:256)` by
    (mp_tac (Q.INST [`c` |-> `n`] abi_decode_bytes_round_bounds) >> decide_tac) >>
  drule_all abi_decode_mload_count_sequence_mem >> strip_tac >>
  `run_inst_seq (emitted_insts st c2) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st c2) s` by
    (`emitted_insts st c2 = emitted_insts st c1 ++ emitted_insts c1 c2` by
       (irule emitted_insts_append >> fs[inst_extends_def, APPEND_ASSOC] >> metis_tac[APPEND_ASSOC, APPEND_11]) >>
     asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  Cases_on `w2n (abi_decode_load MLOAD (n2w (b+p):bytes32) s2) <= n`
  >- suspend "count_accept" >>
  `n < w2n (abi_decode_load MLOAD (n2w (b+p):bytes32) s2)` by decide_tac >>
  gvs[] >> suspend "count_reject"
QED
Resume abi_decode_bytes_finite_mem[count_reject]:
  `run_inst_seq (emitted_insts st c3) s = Abort Revert_abort t` by
    metis_tac[run_inst_seq_emit_extend] >>
  `emitted_insts st en = emitted_insts st c2 ++ emitted_insts c2 en /\
   emitted_insts c2 en = emitted_insts c2 c3 ++ emitted_insts c3 en` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def, APPEND_ASSOC] >> metis_tac[APPEND_ASSOC, APPEND_11]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
      irule run_inst_seq_mem_ok_append >> simp[]) >>
  disj1_tac >> metis_tac[run_inst_seq_abort_extends]
QED
Resume abi_decode_bytes_finite_mem[count_accept]:
  gvs[GSYM word_add_n2w] >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `abi_decode_load MLOAD (n2w (b+p):bytes32) s2 =
   abi_decode_load MLOAD (n2w (b+p):bytes32) s` by
    simp[abi_decode_load_def, mload_def] >>
  qmatch_asmsub_abbrev_tac `~(n < w2n cw)` >>
  `w2n cw <= n` by decide_tac >>
  `cw = n2w (w2n cw)` by simp[] >>
  `eval_operand head s3 = SOME (n2w (p+32)) /\
   eval_operand hi s3 = SOME (n2w h)` by (simp[word_add_n2w] >> metis_tac[]) >>
  drule_all abi_decode_bytes_payload_sequence_mem >> strip_tac >>
  `run_inst_seq (emitted_insts st c3) s = OK s3` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st c3) s` by
    (`emitted_insts st c3 = emitted_insts st c2 ++ emitted_insts c2 c3` by
       (irule emitted_insts_append >> fs[inst_extends_def, APPEND_ASSOC] >> metis_tac[APPEND_ASSOC, APPEND_11]) >>
     asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  Cases_on `w2n (n2w (p+32):bytes32) <= w2n ((n2w (p+32):bytes32)+cw) /\
    w2n ((n2w (p+32):bytes32)+cw) <= w2n (n2w h:bytes32)`
  >- suspend "payload_accept" >>
  suspend "payload_reject"
QED
Resume abi_decode_bytes_finite_mem[payload_reject]:
  `?t. run_inst_seq (emitted_insts c3 c4) s3 = Abort Revert_abort t` by metis_tac[] >>
  `run_inst_seq (emitted_insts st c4) s = Abort Revert_abort t` by
    metis_tac[run_inst_seq_emit_extend] >>
  `emitted_insts st en = emitted_insts st c3 ++ emitted_insts c3 en /\
   emitted_insts c3 en = emitted_insts c3 c4 ++ emitted_insts c4 en` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def, APPEND_ASSOC] >> metis_tac[APPEND_ASSOC, APPEND_11]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
      irule run_inst_seq_mem_ok_append >> simp[]) >>
  disj1_tac >> metis_tac[run_inst_seq_abort_extends]
QED
Resume abi_decode_bytes_finite_mem[payload_accept]:
  `h < dimword (:256)` by decide_tac >>
  `p+32+w2n cw < dimword (:256)` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPECL [`n2w (p+32)`, `cw`] w2n_add_overflow) >> gvs[w2n_n2w]) >>
  `p+32+w2n cw <= h` by fs[w2n_add_2, w2n_n2w] >>
  gvs[w2n_add_2, w2n_n2w] >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand dst s4 = SOME (n2w d) /\
   eval_operand addr s4 = SOME (n2w (b+p)) /\
   eval_operand cnt s4 = SOME (n2w (w2n cw))` by
    (simp[word_add_n2w] >> metis_tac[]) >>
  `w2n cw+31 < dimword (:256) /\ b+p < dimword (:256) /\
   b+p+32+w2n cw <= s4.vs_alloca_next /\
   d+32+32*((n+31) DIV 32) <= s4.vs_alloca_next` by
    (mp_tac (Q.INST [`c` |-> `n`] abi_decode_bytes_round_bounds) >> decide_tac) >>
  mp_tac (Q.INST [`c` |-> `w2n (cw:bytes32)`, `a` |-> `b+p`, `d` |-> `d`,
    `n` |-> `n`, `s` |-> `s4`, `st` |-> `c4`, `st'` |-> `en`]
    abi_decode_bytes_runtime_tail_mem_ok) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `run_inst_seq (emitted_insts st c4) s = OK s4` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s3`, `c3`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st c4) s` by
    (`emitted_insts st c4 = emitted_insts st c3 ++ emitted_insts c3 c4` by
       (irule emitted_insts_append >> fs[inst_extends_def, APPEND_ASSOC] >> metis_tac[APPEND_ASSOC, APPEND_11]) >>
     asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  conj_tac
  >- (`emitted_insts st en = emitted_insts st c4 ++ emitted_insts c4 en` by
        (irule emitted_insts_append >> fs[inst_extends_def, APPEND_ASSOC] >> metis_tac[APPEND_ASSOC, APPEND_11]) >>
      asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  suspend "success"
QED
Resume abi_decode_bytes_finite_mem[success]:
  disj2_tac >>
  `32*((w2n cw+31) DIV 32)+32 <= 32+32*((n+31) DIV 32)` by
    (irule abi_decode_bytes_round_capacity >> simp[]) >>
  mp_tac (Q.INST [`dst` |-> `dst`, `addr` |-> `addr`, `cnt` |-> `cnt`,
    `st` |-> `c4`, `st'` |-> `en`, `s` |-> `s4`, `d` |-> `d`,
    `a` |-> `b+p`, `c` |-> `w2n (cw:bytes32)`]
    abi_decode_bytes_runtime_tail_sequence) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  `run_inst_seq (emitted_insts st en) s = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s4`, `c4`] >> simp[]) >>
  drule_all abi_decode_bytes_runtime_tail_allocation_frame >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  mp_tac (Q.INST [`d` |-> `d`, `a` |-> `b+p`, `c` |-> `w2n (cw:bytes32)`,
    `n` |-> `n`, `s` |-> `s4`] abi_decode_bytes_rounded_capacity_frame) >>
  simp[abi_decode_bytes_copy_size_def, abi_decode_frame_def] >>
  metis_tac[]
QED
Finalise abi_decode_bytes_finite_mem

Theorem abi_decode_bytes_outputs:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\ not_fresh_at st x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st en)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_position_phases] >>
  simp[abi_decode_bytes_head_def, compile_abi_dec_addr_def,
      abi_decode_count_guard_def, abi_decode_bytes_payload_guard_def,
      abi_decode_bytes_runtime_tail_def, compile_abi_decode_range_check_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem abi_decode_bytes_live_frame:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  !op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (emitted_insts st en)` by fs[EVERY_MEM] >>
  drule_all entry_sequence_nonterminator_labels >> strip_tac >>
  Cases >> simp[abi_decoder_operand_live_def, eval_operand_def] >> strip_tac >>
  rename1 `x IN abi_decoder_older_vars st.cs_next_var` >>
  `not_fresh_at st x` by fs[abi_decoder_older_vars_def, not_fresh_at_def] >>
  `EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st en)` by
    (irule abi_decode_bytes_outputs >> metis_tac[]) >>
  `lookup_var x t = lookup_var x s` by
    (irule entry_sequence_nonoutput_lookup >>
     qexists_tac `emitted_insts st en` >> simp[] >> fs[EVERY_MEM]) >>
  fs[lookup_var_def]
QED

Theorem abi_decode_bytes_reentry_sequence_mem:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),en) /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var pos /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\ eval_operand hi s = SOME (n2w h) /\
  p < dimword (:256) /\ b+h < dimword (:256) /\ b+h <= s.vs_alloca_next /\
  d+32+32*((n+31) DIV 32) < dimword (:256) /\
  d+32+32*((n+31) DIV 32) <= s.vs_alloca_next /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\
  ((?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
   (?t. run_inst_seq (emitted_insts st en) s = OK t /\
      fresh_vars_wrt limit_st t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      abi_decode_frame d (32+32*((n+31) DIV 32)) s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next))
Proof
  strip_tac >> qabbrev_tac `clean = abi_decoder_prune_vars st.cs_next_var s` >>
  `fresh_vars_wrt st clean /\ abi_decoder_vars_extend s.vs_vars clean s` by
    simp[Abbr `clean`, abi_decoder_prune_fresh, abi_decoder_prune_extension] >>
  `eval_operand dst clean = SOME (n2w d) /\ eval_operand pos clean = SOME (n2w p) /\
   eval_operand base_op clean = SOME (n2w b) /\ eval_operand hi clean = SOME (n2w h) /\
   b+h <= clean.vs_alloca_next /\ d+32+32*((n+31) DIV 32) <= clean.vs_alloca_next` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_vars_def] >>
  drule_all abi_decode_bytes_finite_mem >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (irule abi_decode_sequence_mem_extend >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[]
  >- (disj1_tac >> drule_all abi_decode_sequence_revert_extend >> metis_tac[]) >>
  suspend "accept"
QED
Resume abi_decode_bytes_reentry_sequence_mem[accept]:
  disj2_tac >> drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) s = OK actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `fresh_vars_wrt limit_st actual` by
    (irule abi_decoder_vars_extend_fresh >> goal_assum (drule_at Any) >>
     fs[fresh_vars_wrt_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op actual = eval_operand op s` by
    (mp_tac (Q.INST [`dst` |-> `dst`, `pos` |-> `pos`, `base_op` |-> `base_op`,
      `hi` |-> `hi`, `n` |-> `n`, `st` |-> `st`, `en` |-> `en`,
      `s` |-> `s`, `t` |-> `actual`] abi_decode_bytes_live_frame) >> simp[]) >>
  qexists_tac `actual` >> simp[] >>
  fs[abi_decode_frame_def, Abbr `clean`, abi_decoder_prune_vars_def] >>
  metis_tac[]
QED
Finalise abi_decode_bytes_reentry_sequence_mem
