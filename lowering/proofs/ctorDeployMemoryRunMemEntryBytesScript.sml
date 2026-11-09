Theory ctorDeployMemoryRunMemEntryBytes
Ancestors
  loweringStateRelDefs abiEncoder abiDecoderBytesPrefix
  ctorDeployMemoryRunMemEntryWord abiDecoderBytesBound abiDecoderGuard
  abiDecoderBytesTyped ctorAbiActualBytes abiCanonicalBytes
  fragGasSeqMem fragGasPathMem allocaHistory rich_list instIdxIndep fragExec
  ctorAbiActualWorld abiEncoderRegisteredEffect abiDecoderCoherence
  ctorAbiActualNarrowWord allocaFrontierBound allocaBudgetProps abiDecoderLayout
  ctorAbiActualObservations
  abiDecoderBytes abiDecoderBytesFrame abiDecoderReservation abiDecoderContract abiDecoderComposition
  abiDecoderReentry abiDecoderReentryPointer ctorDeployMemoryRunMemEntryReentry
  abiDecoderGuards emitHelperProps exprLoweringProps compileEnv fragExecMem
  instMemFrontier memSafeRun venomInst venomExecSemantics venomState words list arithmetic

Theorem ctor_bytes_copy_mem_ok:
  emit_void DLOADBYTES [dst;src;Lit (n2w k)] st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\ k < dimword (:256) /\
  sb <= LENGTH s.vs_data_section /\ d+k <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >> conj_tac
  >- simp[below_frontier_DLOADBYTES, eval_operand_def, w2n_n2w] >>
  simp[inst_dload_in_section_def, mk_inst_def] >> rpt strip_tac >>
  gvs[w2n_n2w]
QED

Theorem ctor_bytes_count_guard_mem_ok:
  abi_decode_count_guard DLOAD src n st = (count_op,st') /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb <= LENGTH s.vs_data_section ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >>
  gvs[] >>
  asm_rewrite_tac[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  qpat_x_assum `eval_operand src s = _` mp_tac >>
  qpat_x_assum `sb < _` mp_tac >>
  qpat_x_assum `sb <= _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  conj_tac
  >- (simp[inst_dload_in_section_def, mk_inst_def] >> rpt strip_tac >>
      gvs[w2n_n2w]) >>
  Cases_on `step_inst_base
    (mk_inst st.cs_next_id DLOAD [src]
      [STRING #"%" (toString st.cs_next_var)]) s` >> simp_tac (srw_ss()) [] >>
  irule run_inst_seq_mem_ok_every >> simp[] >> rpt conj_tac >> gen_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem ctor_bytes_end_guard_mem_ok:
  abi_decode_bytes_end_guard src len hi st = ((),st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_bytes_end_guard_def, comp_return_def] >> strip_tac >>
      gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  simp[abi_decode_bytes_end_guard_def, abi_decode_bytes_end_def,
       abi_decode_le_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  asm_rewrite_tac[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  rpt (pop_assum kall_tac) >>
  irule run_inst_seq_mem_ok_every >> simp[] >> rpt conj_tac >> gen_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem ctor_bytes_count_guard_no_alloca:
  abi_decode_count_guard DLOAD src n st = (count_op,st') ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  asm_rewrite_tac[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem ctor_bytes_end_guard_no_alloca:
  abi_decode_bytes_end_guard src len hi st = ((),st') ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st') /\ inst_extends st st'
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_bytes_end_guard_def, comp_return_def] >> strip_tac >>
      gvs[emitted_insts_def, inst_extends_refl]) >>
  simp[abi_decode_bytes_end_guard_def, abi_decode_bytes_end_def,
       abi_decode_le_guard_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  conj_tac
  >- (imp_res_tac emitted_insts_emit_op >>
      imp_res_tac emitted_insts_emit_void >> gvs[] >>
      asm_rewrite_tac[emitted_insts_def] >>
      rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
      simp[mk_inst_def, is_terminator_def, is_alloca_op_def]) >>
  metis_tac[inst_extends_trans]
QED

Theorem ctor_bytes_head_mem_ok[local]:
  abi_decode_bytes_head src hi st = (head,st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_bytes_head_def, comp_return_def] >> strip_tac >>
      gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  asm_rewrite_tac[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  rpt (pop_assum kall_tac) >>
  irule run_inst_seq_mem_ok_every >> simp[] >> rpt conj_tac >> gen_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem ctor_bytes_payload_guard_mem_ok[local]:
  abi_decode_bytes_payload_guard head cnt hi st = ((),st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_bytes_payload_guard_def, comp_return_def] >> strip_tac >>
      gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  simp[abi_decode_bytes_payload_guard_def, compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  asm_rewrite_tac[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  rpt (pop_assum kall_tac) >>
  irule run_inst_seq_mem_ok_every >> simp[] >> rpt conj_tac >> gen_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem ctor_bytes_position_prefix_mem_ok[local]:
  abi_decode_bytes_position_prefix src DLOAD (Lit 0w) hi n st = ((addr,count_op),st') /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decode_load DLOAD (n2w sb : bytes32) s = n2w cnt /\
  cnt <= n /\ n < dimword (:256) /\ sb < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + 32 + cnt <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s /\ sb <= LENGTH s.vs_data_section ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_bytes_position_prefix_unbounded,
        compile_abi_dec_addr_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> strip_tac >> gvs[] >>
      irule ctor_bytes_count_guard_mem_ok >> metis_tac[]) >>
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_position_prefix _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_position_prefix_trace, compile_abi_dec_addr_def,
       comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `abi_decode_bytes_head src hi st = (head,c1)` >>
  rename1 `abi_decode_count_guard DLOAD src n c1 = (count_op,c2)` >>
  `sb + 32 <= h` by decide_tac >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  `inst_extends c1 st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts c1 st' = emitted_insts c1 c2 ++ emitted_insts c2 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (irule ctor_bytes_head_mem_ok >> metis_tac[]) >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `run_inst_seq_mem_ok (emitted_insts c1 c2) s1` by
    (irule ctor_bytes_count_guard_mem_ok >>
     qexistsl [`count_op`, `n`, `sb`, `src`] >> simp[] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts c1 st') s1` by
    (once_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
     simp[] >> rpt strip_tac >>
     irule ctor_bytes_payload_guard_mem_ok >> metis_tac[]) >>
  once_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >> gvs[]
QED

Theorem ctor_bytes_fresh_mem_ok:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load DLOAD (n2w sb : bytes32) s = n2w cnt /\
  cnt <= n /\ n < dimword (:256) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + cnt <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s /\ sb <= LENGTH s.vs_data_section /\
  d + abi_decode_bytes_copy_size n <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_phases, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  simp_tac (srw_ss()) [abi_decode_copy_opcode_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gnvs[] >> pairarg_tac >> gnvs[] >>
  rename1 `abi_decode_count_guard DLOAD src n st = (count_op,c1)` >>
  rename1 `abi_decode_bytes_end_guard src count_op hi c1 = (u,c2)` >>
  Cases_on `u` >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  drule abi_decode_bytes_end_guard_sequence >>
  disch_then (qspecl_then [`sb`, `s1`, `cnt`] mp_tac) >>
  (impl_tac >- (simp[] >> Cases_on `hi = Lit 0w` >>
    gvs[] >> qexists `h` >> simp[ADD_ASSOC, ADD_COMM] >> metis_tac[])) >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand src s2 = SOME (n2w sb) /\ eval_operand dst s2 = SOME (n2w d)` by
    metis_tac[] >>
  drule ctor_bytes_count_guard_no_alloca >> strip_tac >>
  drule ctor_bytes_end_guard_no_alloca >> strip_tac >>
  `s1.vs_allocas = s.vs_allocas /\ s1.vs_alloca_next = s.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >> metis_tac[]) >>
  `s2.vs_allocas = s1.vs_allocas /\ s2.vs_alloca_next = s1.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >> metis_tac[]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  imp_res_tac inst_extends_emit_void >>
  `inst_extends st c2` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st c2 ++ emitted_insts c2 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `emitted_insts st c2 = emitted_insts st c1 ++ emitted_insts c1 c2` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    (irule ctor_bytes_count_guard_mem_ok >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts st c2) s` by
    (once_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
     rpt strip_tac >> irule ctor_bytes_end_guard_mem_ok >> metis_tac[]) >>
  `run_inst_seq (emitted_insts st c2) s = OK s2` by
    (irule run_inst_seq_compose_ok >> qexistsl [`s1`, `c1`] >> simp[]) >>
  once_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[] >> irule ctor_bytes_copy_mem_ok >>
  qexistsl [`d`, `dst`, `abi_decode_bytes_copy_size n`, `sb`, `src`] >>
  simp[] >> metis_tac[]
QED

Theorem ctor_bytes_reentry_mem_ok:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w cnt /\
  cnt <= n /\ n < dimword (:256) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
                     sb + 32 + cnt <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  sb <= LENGTH initial.vs_data_section /\
  d + abi_decode_bytes_copy_size n <= initial.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') initial
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `pruned = abi_decoder_prune_vars st.cs_next_var initial` >>
  `eval_operand src pruned = SOME (n2w sb) /\
   eval_operand dst pruned = SOME (n2w d) /\ fresh_vars_wrt st pruned /\
   abi_decode_load DLOAD (n2w sb : bytes32) pruned = n2w cnt /\
   sb <= LENGTH pruned.vs_data_section /\
   d + abi_decode_bytes_copy_size n <= pruned.vs_alloca_next` by
    (asm_simp_tac bool_ss [Abbr `pruned`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
     gvs[abi_decoder_prune_vars_def, abi_decode_load_def]) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  SUBGOAL_THEN
    ``hi = Lit 0w \/ ?h. eval_operand hi pruned = SOME (n2w h) /\
     sb + 32 + cnt <= h /\ h < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >> gvs[] >> qexists `h` >>
      simp[Abbr `pruned`, abi_decoder_prune_eval, ADD_ASSOC, ADD_COMM]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') pruned` by
    (irule ctor_bytes_fresh_mem_ok >> metis_tac[]) >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decode_bytes_sequence >> strip_tac >>
  irule ctor_reentry_sequence_mem >> conj_tac >- simp[] >>
  qexistsl [`initial.vs_vars`, `pruned`, `t`] >>
  simp[Abbr `pruned`, abi_decoder_prune_extension]
QED

Theorem ctor_bytes_sequence_path:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  gas_path_mem ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
    (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts))
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
          emitted_insts st st' = code` by
    (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `gas_path_mem ctx func s
     (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
     (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
    (irule run_inst_seq_gas_path_mem >> gvs[] >> metis_tac[]) >>
  gvs[]
QED

Theorem ctor_bytes_sequence_zero_path:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
  t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     fs[EVERY_MEM] >>
     qpat_x_assum `!i. MEM i _ ==> abi_decoder_reentry_opcode _` drule >>
     simp[abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def]) >>
  drule_all ctor_bytes_sequence_path >> disch_then (qspec_then `ctx` mp_tac) >>
  simp[] >> strip_tac >>
  drule gas_path_mem_ok_suffix >> simp[]
QED

Theorem ctor_bytes_sequence_history:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  fn_has_code st st' func /\ alloca_history func s /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb ==>
  alloca_history func (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
          emitted_insts st st' = code` by
    (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >> simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) code` by
    (fs[EVERY_MEM] >> rpt strip_tac >> metis_tac[is_alloca_op_def]) >>
  `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)` by
    (irule ctor_sequence_history_advance >>
     qexistsl [`bb`, `code`, `s`] >> gvs[]) >>
  gvs[]
QED

Theorem ctor_checked_bytes_sequence:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  type_memory_bytes ce ty < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section =
    enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
  d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
  fn_has_code st st' func /\ alloca_history func initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ty) initial actual /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    abi_encoder_registered_effect {} [(d,type_memory_bytes ce ty)] initial actual /\
    actual.vs_current_bb = initial.vs_current_bb /\
    gas_path_mem ctx func initial 0
      (OK (actual with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\
    alloca_history func (actual with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_bytestring_ceiling_sequence >> strip_tac >>
  drule_all ctor_actual_bytestring_metadata >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >>
     asm_simp_tac (srw_ss()) [abi_decode_source_def, Excl "enc_def"] >>
     qpat_x_assum `mem_bytes_at sb _ _ = _` mp_tac >>
     asm_simp_tac bool_ss []) >>
  `n < dimword (:256)` by
    (`n + 32 <= abi_decode_bytes_copy_size n` by simp[abi_decoder_bytes_copy_size] >>
     decide_tac) >>
  SUBGOAL_THEN
    ``hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
      sb + 32 + LENGTH (bs:word8 list) <= h /\ h < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >> gvs[] >> qexists `h` >>
      fs[canonical_bytes_encoding] >> decide_tac) >>
  `sb <= LENGTH initial.vs_data_section` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (drule ctor_bytes_reentry_mem_ok >>
     asm_simp_tac bool_ss [] >> disch_then irule >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (qexists `d` >> asm_simp_tac bool_ss [] >> metis_tac[]) >>
     qexistsl [`LENGTH bs`, `sb`] >> asm_simp_tac bool_ss []) >>
  drule_all ctor_bytes_sequence_zero_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `actual.vs_current_bb = initial.vs_current_bb` by
    (drule_at (Pos hd)
       (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field) >>
     simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke]) >>
  `alloca_history func (actual with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (drule_all ctor_bytes_sequence_history >> simp[]) >>
  qexists `actual` >> simp[]
QED

Theorem ctor_checked_bytes_run:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_coherent ce env sf ty tv /\ abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
  ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
  alloca_history func initial ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,type_memory_bytes ce ty)] initial actual /\
    alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
    ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
    actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func initial actual /\
    fresh_vars_wrt limit_st actual /\ actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\ actual.vs_labels = initial.vs_labels /\
    gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256) /\
   d + type_memory_bytes ce ty <= initial.vs_alloca_next` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi` by
    (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st')` by metis_tac[] >>
  drule_all ctor_checked_bytes_sequence >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`, `ctor_actual_sites func (frag_ids st st')`, `func`, `ctx`] strip_assume_tac) >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[] >> conj_tac
  >- (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
      simp[abi_encoder_registered_effect_def]) >>
  conj_tac
  >- (qpat_x_assum `ctor_actual_scratch _ _ _ _ _` mp_tac >>
      simp[ctorAbiActualFrameTheory.ctor_actual_scratch_def]) >>
  qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
  simp[abi_decode_frame_def] >> strip_tac >> simp[] >>
  reverse conj_tac
  >- (qpat_x_assum `fresh_vars_wrt _ actual` mp_tac >> simp[fresh_vars_wrt_def]) >>
  rpt strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x)` by
    (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
  first_x_assum drule_all >> simp[eval_operand_def, lookup_var_def]
QED
