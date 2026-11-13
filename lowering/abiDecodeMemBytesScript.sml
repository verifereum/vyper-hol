(* Memory execution of bounded ABI bytestring decoding. *)
Theory abiDecodeMemBytes
Ancestors
  abiDecodeMemRange abiDecodeMemBytesGuards abiDecodeMemCountGuard
  abiDecoderContract abiDecoderBytesBound abiDecoderGuards fragExec arithmeticProps localPtrsProps
  fragGasMode fragGasPathMem
  entryDecoderHistoryFrame entrySinkExtraction abiDecoderBytesPrefix
  abiDecoderBytesRuntime abiDecoderBytesPhases abiDecoderBytesEdges
  allocaFootprint entryDecodeProps freshWrites bodyUnopFragMemory
  codegenRel contextCodegenRel venomMemDefs memSafeRun fragExecMem fragGasSeqMem fragGasSeqAbort allocaHistoryFragment
  instMemFrontier loweringStateRelDefs abiEncoder emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_bytes_pointer_straight[local]:
  straight_fresh
    (do up <- emit_op ADD [cnt;Lit 31w];
        mask <- emit_op NOT [Lit 31w];
        rounded <- emit_op AND [up;mask];
        emit_op ADD [dst;rounded]
     od)
Proof
  rpt (irule straight_fresh_bind >>
       (reverse conj_tac >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
       gen_tac >> BETA_TAC) >>
  irule straight_fresh_emit_op >> simp[fresh_write_op_def]
QED

Theorem abi_decode_bytes_copy_mem_ok[local]:
  emit_void MSTORE [lastptr;Lit 0w] st = ((),c1) /\
  emit_op ADD [Lit 32w;cnt] c1 = (sz,c2) /\
  emit_void MCOPY [dst;addr;sz] c2 = ((),c3) /\
  eval_operand lastptr s = SOME (n2w (d+q)) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ fresh_vars_wrt st s /\
  d+q < dimword (:256) /\ d < dimword (:256) /\ a < dimword (:256) /\
  32+c < dimword (:256) /\
  d+q+32 <= s.vs_alloca_next /\ d+32+c <= s.vs_alloca_next /\
  a+32+c <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st c3) s
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st c1) s = OK (mstore (d+q) 0w s)` by
    (qpat_assum `emit_void MSTORE _ _ = _` (mp_then Any mp_tac emitted_insts_emit_void) >> strip_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, exec_write2_def,
          mk_inst_def, eval_operand_def, w2n_n2w]) >>
  `fresh_vars_wrt c1 (mstore (d+q) 0w s)` by
    (drule_all fresh_vars_wrt_emit_void_ss >> simp[fresh_vars_wrt_mstore]) >>
  `!op. eval_operand op (mstore (d+q) 0w s) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def, mstore_def,
                   write_memory_with_expansion_def]) >>
  `eval_operand cnt (mstore (d+q) 0w s) = SOME (n2w c) /\
   eval_operand (Lit 32w) (mstore (d+q) 0w s) = SOME 32w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) _ = OK prepared` >>
  suspend "finish"
QED

Resume abi_decode_bytes_copy_mem_ok[finish]:
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st c3 = emitted_insts st c1 ++
     (emitted_insts c1 c2 ++ emitted_insts c2 c3)` by
    (`emitted_insts c1 c3 = emitted_insts c1 c2 ++ emitted_insts c2 c3` by
       (irule emitted_insts_append >> fs[inst_extends_def]) >>
     `emitted_insts st c3 = emitted_insts st c1 ++ emitted_insts c1 c3` by
       (irule emitted_insts_append >> fs[inst_extends_def] >> rfs[]) >> simp[]) >>
  qpat_x_assum `emitted_insts st c3 = _` (fn th => pure_once_rewrite_tac[th]) >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- (`w2n (n2w (d+q):bytes32) + 32 <= s.vs_alloca_next` by simp[] >>
      metis_tac[emit_mstore_mem_ok]) >>
  gen_tac >> strip_tac >> gvs[] >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- (drule emitted_insts_emit_op >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges,
           source_memory_read_ranges_def, source_memory_write_ranges_def,
           inst_dload_in_section_def, mk_inst_def, is_alloca_op_def]) >>
  gen_tac >> strip_tac >> gvs[] >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a)` by metis_tac[] >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts c1 c2) _ = _` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, exec_pure2_def,
          mk_inst_def, eval_operand_def] >>
     strip_tac >> gvs[update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  qpat_assum `emit_void MCOPY _ _ = _` (mp_then Any mp_tac emit_mcopy_mem_ok) >>
  disch_then irule >> simp[word_add_n2w, w2n_n2w]
QED
Finalise abi_decode_bytes_copy_mem_ok

Theorem abi_decode_bytes_runtime_tail_mem_ok:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c <= n /\ c+31 < dimword (:256) /\
  a < dimword (:256) /\ d+32+32*((n+31) DIV 32) < dimword (:256) /\
  d+32+32*((n+31) DIV 32) <= s.vs_alloca_next /\
  a+32+c <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_runtime_tail _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_bytes_runtime_tail_def, comp_bind_def,
                   comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD [dst;rounded] c3 = (lastptr,c4)` >>
  rename1 `emit_void MSTORE [lastptr;Lit 0w] c4 = ((),c5)` >>
  rename1 `emit_op ADD [Lit 32w;cnt] c5 = (copy_sz,c6)` >>
  `c <= 32*((c+31) DIV 32)` by simp[abi_decode_bytes_round_bounds] >>
  `32*((c+31) DIV 32)+32 <= 32+32*((n+31) DIV 32)` by
    (irule abi_decode_bytes_round_capacity >> simp[]) >>
  drule_all abi_decode_bytes_runtime_pointer_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c4) s = OK prepared` >>
  `straight_fresh
    (do up <- emit_op ADD [cnt;Lit 31w];
        mask <- emit_op NOT [Lit 31w];
        rounded <- emit_op AND [up;mask]; emit_op ADD [dst;rounded] od)` by
    metis_tac[abi_decode_bytes_pointer_straight] >>
  fs[straight_fresh_def, comp_bind_def] >>
  first_x_assum (qspecl_then [`st`, `lastptr`, `c4`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  suspend "tail"
QED

Resume abi_decode_bytes_runtime_tail_mem_ok[tail]:
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c4 st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st c4 ++ emitted_insts c4 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => pure_once_rewrite_tac[th]) >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[writes_fresh_mem_ok] >>
  gen_tac >> strip_tac >> gvs[] >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `prepared = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand dst prepared = SOME (n2w d) /\
   eval_operand addr prepared = SOME (n2w a) /\
   eval_operand cnt prepared = SOME (n2w c)` by metis_tac[] >>
  `d+32*((c+31) DIV 32) < dimword (:256) /\ d < dimword (:256) /\
   32+c < dimword (:256) /\ d+32*((c+31) DIV 32)+32 <= prepared.vs_alloca_next /\
   d+32+c <= prepared.vs_alloca_next` by decide_tac >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any mp_tac abi_decode_bytes_copy_mem_ok) >>
  disch_then drule >> disch_then drule >> disch_then irule >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`a`, `c`, `d`, `32*((c+31) DIV 32)`] >> simp[]
QED
Finalise abi_decode_bytes_runtime_tail_mem_ok

Theorem abi_decode_bytes_tail_no_gas[local]:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []
Proof
  simp[abi_decode_bytes_runtime_tail_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def, LET_THM] >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_decode_bytes_tail_path_mem[local]:
  abi_decode_bytes_runtime_tail dst addr cnt st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand addr s = SOME (n2w a) /\
  eval_operand cnt s = SOME (n2w c) /\ c <= n /\ c+31 < dimword (:256) /\
  a < dimword (:256) /\ d+32+32*((n+31) DIV 32) < dimword (:256) /\
  d+32+32*((n+31) DIV 32) <= s.vs_alloca_next /\
  a+32+c <= s.vs_alloca_next /\ fresh_vars_wrt st s /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = (mcopy d a (32+c)
      (mstore (d+32*((c+31) DIV 32)) 0w s)).vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    alloca_history func t
Proof
  strip_tac >>
  `32*((c+31) DIV 32)+32 <= 32+32*((n+31) DIV 32)` by
    (irule abi_decode_bytes_round_capacity >> simp[]) >>
  `c <= 32*((c+31) DIV 32)` by simp[abi_decode_bytes_round_bounds] >>
  `d+32*((c+31) DIV 32) < dimword (:256) /\
   d < dimword (:256) /\ 32+c < dimword (:256)` by decide_tac >>
  drule_all abi_decode_bytes_runtime_tail_sequence >> strip_tac >>
  drule_all abi_decode_bytes_runtime_tail_mem_ok >> strip_tac >>
  drule abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')`
    by fs[EVERY_MEM] >>
  drule abi_decode_bytes_tail_no_gas >> strip_tac >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all abi_decode_bytes_runtime_tail_allocation_frame >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by (gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> gvs[fresh_vars_wrt_def]
QED

Theorem abi_decode_bytes_bounded_path_mem:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\ eval_operand hi s = SOME (n2w h) /\
  p < dimword (:256) /\ b+h < dimword (:256) /\
  b+h <= s.vs_alloca_next /\
  d+32+32*((n+31) DIV 32) < dimword (:256) /\
  d+32+32*((n+31) DIV 32) <= s.vs_alloca_next /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t)) \/
  (?c t. c <= n /\ p+32+c <= h /\
    abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
    gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = (mcopy d (b+p) (32+c)
      (mstore (d+32*((c+31) DIV 32)) 0w s)).vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    alloca_history func t)
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
  drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule_all abi_decode_count_guard_fragment_shape >> strip_tac >>
  drule abi_decode_bytes_payload_guard_fragment_shape >> strip_tac >>
  drule abi_decode_bytes_runtime_tail_shape >> strip_tac >>
  suspend "code"
QED

Resume abi_decode_bytes_bounded_path_mem[code]:
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
   fn_has_code c4 st' func` by
    (gvs[fn_has_code_def, emitted_blocks_def, inst_extends_def, same_blocks_def] >>
     metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  drule_all abi_decode_bytes_head_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `w2n (n2w p : bytes32) <= w2n (n2w p + 32w : bytes32) /\
    w2n (n2w p + 32w : bytes32) <= w2n (n2w h : bytes32)`
  >- suspend "head_accept" >>
  gvs[] >> metis_tac[]
QED
Resume abi_decode_bytes_bounded_path_mem[head_accept]:
  `p+32 < dimword (:256)` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPECL [`n2w p`, `32w`] w2n_add_overflow) >>
     gvs[w2n_n2w]) >>
  `h < dimword (:256) /\ p+32 <= h` by
    (gvs[word_add_n2w, w2n_n2w]) >>
  gvs[word_add_n2w, w2n_n2w] >>
  rename1 `gas_path_mem ctx func s 0 (OK s1)` >>
  `eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand pos s1 = SOME (n2w p)` by metis_tac[] >>
  `alloca_inv s1` by (irule alloca_inv_fields >> metis_tac[]) >>
  `s1.vs_current_bb = c1.cs_current_bb` by simp[] >>
  drule_all abi_decode_add_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s1 0 (OK s2)` >>
  `gas_path_mem ctx func s 0 (OK s2)` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `b+p < dimword (:256) /\ b+p+32 <= s2.vs_alloca_next` by decide_tac >>
  `eval_operand addr s2 = SOME (n2w (b+p))` by gvs[word_add_n2w] >>
  `alloca_inv s2` by (irule alloca_inv_fields >> metis_tac[]) >>
  `n < dimword (:256)` by
    (mp_tac (Q.INST [`c` |-> `n`] abi_decode_bytes_round_bounds) >> decide_tac) >>
  `w2n (n2w (b+p) : bytes32)+32 <= s2.vs_alloca_next` by simp[w2n_n2w] >>
  drule_all abi_decode_mload_count_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `w2n (abi_decode_load MLOAD (n2w (b+p) : bytes32) s2) <= n`
  >- suspend "count_accept" >>
  `n < w2n (abi_decode_load MLOAD (n2w (b+p) : bytes32) s2)` by decide_tac >>
  gvs[GSYM word_add_n2w] >>
  disj1_tac >> fs[gas_marked_path_def] >>
  drule_all gas_path_mem_then >> simp[] >> metis_tac[]
QED
Resume abi_decode_bytes_bounded_path_mem[count_accept]:
  gvs[GSYM word_add_n2w] >>
  rename1 `gas_path_mem ctx func s2 0 (OK s3)` >>
  `gas_path_mem ctx func s 0 (OK s3)` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `abi_decode_load MLOAD (n2w (b+p) : bytes32) s2 =
   abi_decode_load MLOAD (n2w (b+p) : bytes32) s` by
    simp[abi_decode_load_def, mload_def] >>
  qmatch_asmsub_abbrev_tac `w2n cw <= n` >>
  `cw = n2w (w2n cw)` by simp[] >>
  `eval_operand head s3 = SOME (n2w (p+32)) /\
   eval_operand hi s3 = SOME (n2w h)` by (simp[word_add_n2w] >> metis_tac[]) >>
  `alloca_inv s3` by (irule alloca_inv_fields >> metis_tac[]) >>
  `s3.vs_current_bb = c3.cs_current_bb` by simp[] >>
  drule_all abi_decode_bytes_payload_guard_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `w2n (n2w (p+32) : bytes32) <=
      w2n ((n2w (p+32) : bytes32) + cw) /\
    w2n ((n2w (p+32) : bytes32) + cw) <= w2n (n2w h : bytes32)`
  >- suspend "payload_accept" >>
  gvs[] >> disj1_tac >> fs[gas_marked_path_def] >>
  drule_all gas_path_mem_then >> simp[] >> metis_tac[]
QED
Resume abi_decode_bytes_bounded_path_mem[payload_accept]:
  `h < dimword (:256) /\ p+32 < dimword (:256)` by decide_tac >>
  `p+32+w2n cw < dimword (:256)` by
    (spose_not_then assume_tac >>
     mp_tac (Q.SPECL [`n2w (p+32)`, `cw`] w2n_add_overflow) >>
     gvs[w2n_n2w]) >>
  `p+32+w2n cw <= h` by
    (fs[w2n_add_2, w2n_n2w]) >>
  fs[w2n_add_2, w2n_n2w] >>
  rename1 `gas_path_mem ctx func s3 0 (OK s4)` >>
  `eval_operand dst s4 = SOME (n2w d) /\
   eval_operand addr s4 = SOME (n2w (b+p)) /\
   eval_operand cnt s4 = SOME (n2w (w2n cw))` by
    (simp[word_add_n2w] >> metis_tac[]) >>
  `w2n cw+31 < dimword (:256) /\ b+p < dimword (:256) /\
   b+p+32+w2n cw <= s4.vs_alloca_next` by
    (mp_tac (Q.INST [`c` |-> `n`] abi_decode_bytes_round_bounds) >> decide_tac) >>
  `alloca_inv s4` by (irule alloca_inv_fields >> metis_tac[]) >>
  `d+32+32*((n+31) DIV 32) <= s4.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`c` |-> `w2n (cw : bytes32)`, `a` |-> `b+p`, `d` |-> `d`,
    `n` |-> `n`, `s` |-> `s4`, `st` |-> `c4`]
    abi_decode_bytes_tail_path_mem) >>
  impl_tac >- simp[] >>
  strip_tac >>
  `gas_path_mem ctx func s 0 (OK s4)` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `gas_path_mem ctx func s 0 (OK t)` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  disj2_tac >> qexistsl_tac [`w2n cw`, `t`] >>
  simp[] >>
  conj_tac >- gvs[Abbr `cw`, word_add_n2w] >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!op w. eval_operand op s4 = _ ==> _` irule >>
     qpat_x_assum `!op w. eval_operand op s3 = _ ==> _` irule >>
     qpat_x_assum `!op w. eval_operand op s2 = _ ==> _` irule >>
     qpat_x_assum `!op w. eval_operand op s1 = _ ==> _` irule >>
     metis_tac[]) >>
  `s4.vs_memory = s.vs_memory` by metis_tac[] >>
  qpat_x_assum `s4.vs_memory = s.vs_memory` mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  metis_tac[abiEncoderMemoryTheory.abi_encoder_bytes_write_memory_cong,
    arithmeticTheory.ADD_COMM]
QED
Finalise abi_decode_bytes_bounded_path_mem
