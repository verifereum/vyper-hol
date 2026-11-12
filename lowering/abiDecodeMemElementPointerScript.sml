Theory abiDecodeMemElementPointer
Ancestors
  abiDecodeMemRange abiDecodeMemMemberPointer abiDecodeMemBytesGuards arithmeticProps
  abiDecoderBytesBound abiDecoderGuard abiDecoderRange abiDecoderContract abiDecoderBytesPrefix
  entryDecoderHistoryFrame entrySinkExtraction allocaHistoryFragment
  fragGasSeqMem fragGasSeqAbort fragGasMode fragExecMem fragExec
  freshWrites bodyUnopFragMemory instMemFrontier memSafeRun
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  loweringStateRelDefs venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_element_shape:
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') ==>
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
       compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >> strip_tac >> gvs[emitted_insts_def, inst_extends_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def,
       IS_PREFIX_APPEND]
QED

Theorem abi_decode_element_prefix[local]:
  compile_abi_dec_addr bop src st = (addr,c1) /\
  emit_op MLOAD [addr] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (ptr_op,c3) /\
  eval_operand bop s = SOME b /\ eval_operand src s = SOME p /\
  eval_operand data s = SOME d /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st c3) s = OK t /\
    eval_operand ptr_op t = SOME (d + abi_decode_load MLOAD (b+p) s) /\
    fresh_vars_wrt c3 t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st c3
Proof
  strip_tac >>
  `b+p = n2w (w2n b + w2n p)` by metis_tac[word_add_n2w, n2w_w2n] >>
  `eval_operand bop s = SOME (n2w (w2n b)) /\
   eval_operand src s = SOME (n2w (w2n p))` by simp[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand data s2 = SOME d /\
   abi_decode_load MLOAD (n2w (w2n b+w2n p) : bytes32) s1 =
     abi_decode_load MLOAD (b+p) s` by
    (gvs[abi_decode_load_def, mload_def] >> metis_tac[]) >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  `inst_extends st c1` by
    (Cases_on `bop = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  imp_res_tac inst_extends_emit_op >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st c3) s = OK t /\ inst_extends st c3` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Theorem abi_decode_element_trace[local]:
  hi <> Lit 0w /\
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') ==>
  ?addr off c1 c2 c3 c4 eend c5.
    compile_abi_dec_addr bop src st = (addr,c1) /\
    emit_op MLOAD [addr] c1 = (off,c2) /\
    emit_op ADD [data;off] c2 = (ptr_op,c3) /\
    abi_decode_ge_guard ptr_op data c3 = ((),c4) /\
    emit_op ADD [ptr_op;Lit (n2w sz)] c4 = (eend,c5) /\
    compile_abi_decode_range_check ptr_op eend hi c5 = ((),st')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_dyn_elem_ptr_def, abi_decode_ge_guard_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[pairTheory.PAIR, oneTheory.one]
QED

Theorem abi_decode_element_sequence:
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') /\
  hi <> Lit 0w /\ eval_operand bop s = SOME b /\ eval_operand src s = SOME p /\
  eval_operand data s = SOME d /\ eval_operand hi s = SOME h /\
  fresh_vars_wrt st s ==>
  let v = d + abi_decode_load MLOAD (b+p) s in
  (w2n d <= w2n v /\ w2n v <= w2n (v+n2w sz) /\ w2n (v+n2w sz) <= w2n h ==>
    ?t. run_inst_seq (emitted_insts st st') s = OK t /\
      eval_operand ptr_op t = SOME v /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section) /\
  (~(w2n d <= w2n v /\ w2n v <= w2n (v+n2w sz) /\ w2n (v+n2w sz) <= w2n h) ==>
    ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  drule_all abi_decode_element_trace >> strip_tac >>
  drule_all abi_decode_element_prefix >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c3) s = OK s3` >>
  `eval_operand data s3 = SOME d` by metis_tac[] >>
  imp_res_tac inst_extends_emit_op >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  drule compile_abi_decode_range_check_fragment_shape >> strip_tac >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_element_sequence[accept]:
  strip_tac >> drule_all abi_decode_ge_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand ptr_op s4 = SOME (d+abi_decode_load MLOAD (b+p) s) /\
   eval_operand (Lit (n2w sz)) s4 = SOME (n2w sz)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  `eval_operand ptr_op s5 = SOME (d+abi_decode_load MLOAD (b+p) s) /\
   eval_operand hi s5 = SOME h` by metis_tac[] >>
  drule_all compile_abi_decode_range_check_sequence >> strip_tac >>
  `run_inst_seq (emitted_insts st c4) s = OK s4 /\ inst_extends st c4` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`,`c3`] >> simp[]) >>
  `run_inst_seq (emitted_insts st c5) s = OK s5 /\ inst_extends st c5` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s4`,`c4`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s5`,`c5`] >> simp[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
Resume abi_decode_element_sequence[reject]:
  disch_tac >> Cases_on `w2n d <= w2n (d+abi_decode_load MLOAD (b+p) s)`
  >- suspend "range_reject" >>
  `w2n (d+abi_decode_load MLOAD (b+p) s) < w2n d` by fs[] >>
  drule_all abi_decode_mem_ge_rejected >> strip_tac >>
  `inst_extends c3 st'` by metis_tac[inst_extends_trans] >>
  `inst_extends c4 st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts c3 st' = emitted_insts c3 c4 ++ emitted_insts c4 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts st st' = emitted_insts st c3 ++ emitted_insts c3 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_assum `run_inst_seq (emitted_insts st c3) s = OK s3`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (pure_rewrite_tac o single) >>
  `!u. run_inst_seq (emitted_insts c3 c4) s3 <> OK u` by simp[] >>
  drule run_inst_seq_append_err >>
  disch_then (pure_rewrite_tac o single) >> simp[]
QED
Resume abi_decode_element_sequence[range_reject]:
  drule_all abi_decode_ge_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand ptr_op s4 = SOME (d+abi_decode_load MLOAD (b+p) s) /\
   eval_operand (Lit (n2w sz)) s4 = SOME (n2w sz)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  `eval_operand ptr_op s5 = SOME (d+abi_decode_load MLOAD (b+p) s) /\
   eval_operand hi s5 = SOME h` by metis_tac[] >>
  drule_all abi_decode_range_sequence >> simp[] >> strip_tac >>
  `run_inst_seq (emitted_insts st c4) s = OK s4 /\ inst_extends st c4` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`,`c3`] >> simp[]) >>
  `run_inst_seq (emitted_insts st c5) s = OK s5 /\ inst_extends st c5` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s4`,`c4`] >> simp[]) >>
  `emitted_insts st st' = emitted_insts st c5 ++ emitted_insts c5 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[] >> drule run_inst_seq_append >>
  disch_then (pure_rewrite_tac o single) >>
  drule run_inst_seq_append >>
  disch_then (pure_rewrite_tac o single) >> simp[]
QED
Finalise abi_decode_element_sequence

Theorem abi_decode_element_mem_ok:
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') /\
  hi <> Lit 0w /\ eval_operand bop s = SOME b /\ eval_operand src s = SOME p /\
  w2n (b+p) + 32 <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule_all abi_decode_element_trace >> strip_tac >>
  `straight_fresh (compile_abi_dec_addr bop src)` by
    (Cases_on `bop = Lit 0w` >> simp[compile_abi_dec_addr_def] >>
     FIRST [irule straight_fresh_return,
       irule straight_fresh_emit_op >> simp[fresh_write_op_def]]) >>
  `writes_fresh st (emitted_insts st c1) /\ inst_extends st c1` by
    fs[straight_fresh_def, inst_extends_def] >>
  `eval_operand bop s = SOME (n2w (w2n b)) /\
   eval_operand src s = SOME (n2w (w2n p))` by simp[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK sa` >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `sa.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `sa = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand addr sa = SOME (b+p)` by metis_tac[word_add_n2w,n2w_w2n] >>
  `inst_extends c1 st'` by
    (imp_res_tac inst_extends_emit_op >>
     imp_res_tac abi_decode_ge_guard_shape >>
     imp_res_tac compile_abi_decode_range_check_fragment_shape >>
     metis_tac[inst_extends_trans]) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => pure_once_rewrite_tac[th]) >>
  MATCH_MP_TAC run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[writes_fresh_mem_ok] >>
  gen_tac >> strip_tac >> gvs[] >> suspend "tail"
QED
Resume abi_decode_element_mem_ok[tail]:
  rename1 `run_inst_seq (emitted_insts st c1) s = OK sa` >>
  qpat_x_assum `compile_abi_decode_range_check _ _ _ _ = _` mp_tac >>
  qpat_x_assum `abi_decode_ge_guard _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_range_check_def, abi_decode_ge_guard_def,
    comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_def] >>
  conj_tac >- simp[below_frontier_MLOAD] >>
  Cases_on `step_inst_base (mk_inst c1.cs_next_id MLOAD [addr]
    [STRING #"%" (toString c1.cs_next_var)]) sa` >> simp[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_dload_in_section_def] >>
  rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[]
QED
Finalise abi_decode_element_mem_ok

Theorem abi_decode_element_bounds:
  !(d:bytes32) (v:bytes32) sz (h:bytes32).
  sz < dimword (:256) ==>
  ((w2n d <= w2n (d+v) /\ w2n (d+v) <= w2n (d+v+n2w sz) /\
     w2n (d+v+n2w sz) <= w2n h) <=>
   w2n d + w2n v + sz <= w2n h)
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- (`w2n d + w2n v < dimword (:256)` by
        (spose_not_then assume_tac >>
         `dimword (:256) <= w2n d + w2n v` by decide_tac >>
         drule w2n_add_overflow >> simp[]) >>
      `w2n (d+v) + w2n (n2w sz : bytes32) < dimword (:256)` by
        (spose_not_then assume_tac >>
         `dimword (:256) <= w2n (d+v) + w2n (n2w sz : bytes32)` by decide_tac >>
         drule w2n_add_overflow >> simp[]) >>
      gvs[w2n_add_2, w2n_n2w]) >>
  `w2n h < dimword (:256)` by irule w2n_lt >>
  `w2n d + w2n v < dimword (:256)` by decide_tac >>
  `w2n (d+v) + w2n (n2w sz : bytes32) < dimword (:256)` by
    (simp[w2n_add_2, w2n_n2w] >> decide_tac) >>
  simp[w2n_add_2, w2n_n2w]
QED

Theorem abi_decode_mload_element_path_mem:
  compile_abi_decode_dyn_elem_ptr MLOAD bop src data hi sz st = (ptr_op,st') /\
  hi <> Lit 0w /\ eval_operand bop s = SOME b /\ eval_operand src s = SOME p /\
  eval_operand data s = SOME d /\ eval_operand hi s = SOME h /\
  w2n (b+p) + 32 <= s.vs_alloca_next /\ sz < dimword (:256) /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n d + w2n (abi_decode_load MLOAD (b+p) s) + sz <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand ptr_op t = SOME (d+abi_decode_load MLOAD (b+p) s) /\
      w2n (d+abi_decode_load MLOAD (b+p) s) =
        w2n d + w2n (abi_decode_load MLOAD (b+p) s) /\
      w2n d <= w2n (d+abi_decode_load MLOAD (b+p) s) /\
      w2n (d+abi_decode_load MLOAD (b+p) s) + sz <= w2n h /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
      alloca_history func t) /\
  (~(w2n d + w2n (abi_decode_load MLOAD (b+p) s) + sz <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >> drule abi_decode_element_shape >> strip_tac >>
  drule_all abi_decode_element_mem_ok >> strip_tac >>
  drule_all abi_decode_element_sequence >> simp[LET_THM] >>
  `((w2n d <= w2n (d+abi_decode_load MLOAD (b+p) s) /\
      w2n (d+abi_decode_load MLOAD (b+p) s) <=
        w2n (d+abi_decode_load MLOAD (b+p) s+n2w sz) /\
      w2n (d+abi_decode_load MLOAD (b+p) s+n2w sz) <= w2n h) <=>
     w2n d + w2n (abi_decode_load MLOAD (b+p) s) + sz <= w2n h)` by
       metis_tac[abi_decode_element_bounds] >>
  simp[] >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0`
    by (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_mload_element_path_mem[accept]:
  strip_tac >> gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0`
    by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_MEM] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by simp[IS_PREFIX_APPEND] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all abi_decode_nonallocating_sequence_frame >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  `w2n h < dimword (:256)` by irule w2n_lt >>
  `w2n d + w2n (abi_decode_load MLOAD (b+p) s) < dimword (:256)` by decide_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, w2n_add_2] >>
  gvs[fresh_vars_wrt_def]
QED
Resume abi_decode_mload_element_path_mem[reject]:
  disch_tac >> gvs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
Finalise abi_decode_mload_element_path_mem
