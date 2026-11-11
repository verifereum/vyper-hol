(* Memory checks for the count clamp, before array writes or allocation. *)
Theory extcallDecoderArrayPreparationMemory
Ancestors
  abiDecoderRange abiDecoderContract abiDecoderGuards abiDecoderDynarrayPrefix abiDecoderArrayInitExec
  extcallDecoderBulkMemory extcallDecoderHeaderMemory abiDecoderArrayHeader abiDecoderArrayLoopInit
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  fragExecMem fragGasSeqMem fragGasPathMem fragGasSeqAbort instMemFrontier
  venomExecProofs freshWrites loweringStateRelDefs abiDecoderBytesBound
  abiDecoderDynarrayBound appendStorageStageTransportPtr bodyUnopFragMemory
  abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderReentry abiDecoderReentryAddress
  abiDecoderArrayBackedge ssaOperandFrame
  abiEncoderWindowArrayCursorMem abiDecoderDynamicLoopSetup abiDecoderStaticLoopSetup
  abiDecoderArraySetupInputs
  venomInstProofs venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem extcall_decoder_count_guard_mem_ok:
  abi_decode_count_guard MLOAD src limit st = (cnt,st') /\
  eval_operand src s = SOME (n2w p) /\ p < dimword(:256) /\
  p+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok code s` >>
  `code = TAKE 1 code ++ DROP 1 code` by simp[] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  match_mp_tac run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (rpt strip_tac >> irule run_inst_seq_mem_ok_every >>
      simp[Abbr `code`, below_frontier_no_ranges,
           memSafeRunTheory.inst_dload_in_section_def, mk_inst_def]) >>
  simp[Abbr `code`, run_inst_seq_mem_ok_last, GSYM mk_inst_def,
       below_frontier_MLOAD, w2n_n2w]
QED

Theorem extcall_decoder_count_guard_success:
  abi_decode_count_guard MLOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME (n2w p) /\ p < dimword(:256) /\
  p+32 <= s.vs_alloca_next /\
  abi_decode_load MLOAD (n2w p : bytes32) s = n2w n /\
  n <= limit /\ limit < dimword(:256) /\ fresh_vars_wrt st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
      eval_operand count_op t = SOME (n2w n) /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[extcall_decoder_count_guard_mem_ok] >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  drule_all abi_decode_count_guard_fragment_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_decoder_count_guard_reject:
  abi_decode_count_guard MLOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME (n2w p) /\ p < dimword(:256) /\
  p+32 <= s.vs_alloca_next /\ limit < dimword(:256) /\
  limit < w2n (abi_decode_load MLOAD (n2w p : bytes32) s) /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?n t. gas_path_mem ctx func s n (Abort Revert_abort t)
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[extcall_decoder_count_guard_mem_ok] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_count_guard_fragment_shape >> strip_tac >>
  `?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
     rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
     drule_all abi_decode_read >> strip_tac >>
     rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
     `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
     drule_all emit_op_GT_correct >> strip_tac >>
     gvs[w2n_n2w, bool_to_word_def] >>
     drule_all emit_op_ISZERO_correct >> strip_tac >>
     gvs[bool_to_word_def] >>
     drule_all emit_void_ASSERT_revert_full >> strip_tac >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     drule_all abi_decode_sequence_chain >> strip_tac >>
     drule_all abi_decode_sequence_chain >> strip_tac >>
     drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]) >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[fragGasModeTheory.gas_marked_path_def] >> metis_tac[]
QED

Theorem extcall_decoder_array_header_success:
  abi_decode_array_header dst addr MLOAD st = (cnt,st') /\
  eval_operand addr s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  w2n p+32 <= s.vs_alloca_next /\ d < dimword(:256) /\
  d+32 <= s.vs_alloca_next /\ fresh_vars_wrt st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
      eval_operand cnt t = SOME (abi_decode_load MLOAD p s) /\
      mem_word_at d t.vs_memory = abi_decode_load MLOAD p s /\
      abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[extcall_decoder_array_count_mem_ok] >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule_all abi_decoder_guard_sequence_fields >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_decoder_bytes_head_fresh[local]:
  straight_fresh (abi_decode_bytes_head src hi)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [irule straight_fresh_bind, irule straight_fresh_ignore_bind,
    conj_tac, gen_tac >> BETA_TAC,
    irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
    irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
    MATCH_ACCEPT_TAC straight_fresh_return])
QED

Theorem extcall_decoder_unbounded_array_guard_mem_ok[local]:
  abi_decode_dynarray_position_prefix src MLOAD base_op (Lit 0w) maxn asz st = (addr,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand base_op s = SOME (n2w B) /\
  B+sb < dimword(:256) /\ B+sb+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >> Cases_on `base_op = Lit 0w` >>
  qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_dynarray_position_prefix_unbounded, compile_abi_dec_addr_def,
       abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND] >>
  (qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok code s` >>
   `code = TAKE (if (HD code).inst_opcode = MLOAD then 1 else 2) code ++
           DROP (if (HD code).inst_opcode = MLOAD then 1 else 2) code` by simp[] >>
   pop_assum (fn th => pure_once_rewrite_tac[th]) >>
   match_mp_tac run_inst_seq_mem_ok_append >> reverse conj_tac
   >- (rpt strip_tac >> irule run_inst_seq_mem_ok_every >>
       simp[Abbr `code`, below_frontier_no_ranges,
            memSafeRunTheory.inst_dload_in_section_def, mk_inst_def]) >>
   simp[Abbr `code`, run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
        below_frontier_no_ranges, GSYM mk_inst_def] >>
   simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
        word_add_n2w] >>
   simp[GSYM mk_inst_def, below_frontier_MLOAD, eval_operand_def,
        lookup_var_update_var, w2n_n2w] >>
   rpt strip_tac >> gvs[update_var_def, lookup_var_def, w2n_n2w])
QED

Theorem extcall_decoder_array_payload_fresh[local]:
  straight_fresh (abi_decode_dynarray_payload_guard head cnt asz hi)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def] >>
  rpt (FIRST [irule straight_fresh_bind, irule straight_fresh_ignore_bind,
    conj_tac, gen_tac >> BETA_TAC,
    irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
    irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
    MATCH_ACCEPT_TAC straight_fresh_return])
QED

Theorem extcall_decoder_array_guard_mem_ok:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn asz st = (addr,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand base_op s = SOME (n2w B) /\
  B+sb < dimword(:256) /\ B+sb+32 <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  qpat_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [abi_decode_dynarray_position_prefix_trace]) >>
  `abi_decode_dynarray_position_prefix src MLOAD base_op (Lit 0w) maxn asz
      head_st = (addr,count_st)` by
    simp[abi_decode_dynarray_position_prefix_unbounded, comp_bind_def, comp_return_def] >>
  `writes_fresh st (emitted_insts st head_st)` by
    metis_tac[extcall_decoder_bytes_head_fresh, straight_fresh_def] >>
  `writes_fresh count_st (emitted_insts count_st st')` by
    metis_tac[extcall_decoder_array_payload_fresh, straight_fresh_def] >>
  `inst_extends st head_st /\ inst_extends head_st count_st /\
   inst_extends count_st st'` by
    metis_tac[abi_decode_bytes_head_shape, abi_decode_dynarray_position_prefix_shape,
              abi_decode_dynarray_payload_guard_shape, abi_decode_source_opcode_def] >>
  `emitted_insts st st' = emitted_insts st head_st ++
      (emitted_insts head_st count_st ++ emitted_insts count_st st')` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- metis_tac[writes_fresh_mem_ok] >>
  rpt strip_tac >>
  `eval_operand src s' = SOME (n2w sb) /\
   eval_operand base_op s' = SOME (n2w B)` by
    metis_tac[writes_fresh_old_operand, exprSimWordBuiltinsTheory.fresh_vars_wrt_not_fresh_at] >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    (drule_all run_inst_seq_writes_fresh >> strip_tac >>
     qpat_x_assum `s' = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  match_mp_tac run_inst_seq_mem_ok_append >> conj_tac
  >- (irule extcall_decoder_unbounded_array_guard_mem_ok >> metis_tac[]) >>
  metis_tac[writes_fresh_mem_ok]
QED

Theorem extcall_decoder_array_guard_success:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn asz st = (addr,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand base_op s = SOME (n2w B) /\
  B+sb < dimword(:256) /\ B+sb+32 <= s.vs_alloca_next /\
  abi_decode_load MLOAD (n2w (B+sb) : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword(:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
       sb+32+n*asz <= h /\ h < dimword(:256)) /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
      eval_operand addr t = SOME (n2w (B+sb)) /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_halted = s.vs_halted
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[extcall_decoder_array_guard_mem_ok] >>
  drule abi_decode_dynarray_position_prefix_sequence >>
  disch_then (qspecl_then [`s`, `sb`, `n`, `B`] mp_tac) >>
  (impl_tac >- (simp[] >> disj2_tac >> qexists_tac `h` >> simp[])) >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decoder_guard_sequence_fields >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_decoder_array_element_setup_mem_ok:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di asz msz st = (ops,st') /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword(:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  (dec_info_needs_offset di ==> eval_operand base_op s = SOME (n2w B) /\
    B+sb+32+j*asz < dimword(:256) /\
    B+sb+32+j*asz+32 <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  `!k. st.cs_next_var <= k ==> src <> Var (STRING #"%" (toString k)) /\
      base_op <> Var (STRING #"%" (toString k))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  Cases_on `dec_info_needs_offset di` >> Cases_on `base_op = Lit 0w` >>
  Cases_on `hi = Lit 0w` >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_element_setup_def, compile_abi_decode_dyn_elem_ptr_def,
       compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
       abi_decode_indexed_address_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND] >>
  (qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok code s` >>
   `code = TAKE (if (EL 4 code).inst_opcode = MLOAD then 5 else
        if (EL 5 code).inst_opcode = MLOAD then 6 else 1) code ++
     DROP (if (EL 4 code).inst_opcode = MLOAD then 5 else
        if (EL 5 code).inst_opcode = MLOAD then 6 else 1) code` by simp[] >>
   pop_assum (fn th => pure_once_rewrite_tac[th]) >>
   match_mp_tac run_inst_seq_mem_ok_append >> reverse conj_tac
   >- (rpt strip_tac >> irule run_inst_seq_mem_ok_every >>
       simp[Abbr `code`, below_frontier_no_ranges,
            memSafeRunTheory.inst_dload_in_section_def, mk_inst_def]) >>
   simp[Abbr `code`, run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
        GSYM mk_inst_def, below_frontier_MLOAD, w2n_n2w, below_frontier_no_ranges] >>
   simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, exec_pure2_def,
        eval_operand_update_var_avoids, eval_operand_def, lookup_var_update_var,
        word_add_n2w, word_mul_n2w] >>
   simp[GSYM mk_inst_def, below_frontier_MLOAD, eval_operand_def,
        lookup_var_update_var, w2n_n2w] >>
   rpt strip_tac >> gvs[update_var_def, w2n_n2w, mload_def] >> decide_tac)
QED

Theorem extcall_decoder_array_element_setup_success:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di asz msz st = (ops,st') /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword(:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi /\
  (dec_info_needs_offset di ==> eval_operand base_op s = SOME (n2w B) /\
    B+sb+32+j*asz < dimword(:256) /\
    B+sb+32+j*asz+32 <= s.vs_alloca_next /\
    abi_decode_load MLOAD (n2w (B+(sb+32+j*asz)) : bytes32) s = n2w child_off /\
    (hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
      sb+32+child_off+asz <= hb /\ hb < dimword(:256))) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
      eval_operand (FST ops) t = SOME (n2w j) /\
      eval_operand (FST (SND ops)) t =
        SOME (n2w (sb+32+if dec_info_needs_offset di then child_off else j*asz)) /\
      eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*msz)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
      inst_extends st st'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule extcall_decoder_array_element_setup_mem_ok >> metis_tac[]) >>
  `?t. run_inst_seq (emitted_insts st st') s = OK t /\
      eval_operand (FST ops) t = SOME (n2w j) /\
      eval_operand (FST (SND ops)) t =
        SOME (n2w (sb+32+if dec_info_needs_offset di then child_off else j*asz)) /\
      eval_operand (SND (SND ops)) t = SOME (n2w (d+32+j*msz)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
      inst_extends st st'` by
    (Cases_on `dec_info_needs_offset di`
     >- (qpat_x_assum `dec_info_needs_offset di ==> _` drule >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         `mload (w2n (n2w slot : bytes32)) s = n2w j` by simp[w2n_n2w] >>
         drule_all abi_decode_dynamic_element_setup_reentry >> strip_tac >>
         goal_assum (drule_at Any) >> simp[]) >>
     `mload (w2n (n2w slot : bytes32)) s = n2w j` by simp[w2n_n2w] >>
     drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
     goal_assum (drule_at Any) >> simp[abi_decoder_address_frame_def]) >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  qexists_tac `t` >> simp[ADD_COMM]
QED

(* Rejection transport takes the actual rejecting run, not successful guards. *)
Theorem extcall_decoder_array_guard_reject:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn asz st = (addr,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand base_op s = SOME (n2w B) /\
  B+sb < dimword(:256) /\ B+sb+32 <= s.vs_alloca_next /\ fresh_vars_wrt st s /\
  run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?n j. gas_path_mem ctx func s n (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[extcall_decoder_array_guard_mem_ok] >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[fragGasModeTheory.gas_marked_path_def]
QED

Theorem extcall_decoder_array_element_setup_reject:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di asz msz st = (ops,st') /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword(:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  (dec_info_needs_offset di ==> eval_operand base_op s = SOME (n2w B) /\
    B+sb+32+j*asz < dimword(:256) /\
    B+sb+32+j*asz+32 <= s.vs_alloca_next) /\
  run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?n k. gas_path_mem ctx func s n (Abort Revert_abort (t with vs_inst_idx := k))
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule extcall_decoder_array_element_setup_mem_ok >> metis_tac[]) >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[fragGasModeTheory.gas_marked_path_def]
QED
