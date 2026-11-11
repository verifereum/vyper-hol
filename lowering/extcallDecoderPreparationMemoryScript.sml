(* Physical memory checks for decoder guard and child preparation phases. *)
Theory extcallDecoderPreparationMemory
Ancestors
  abiDecoderRange abiDecoderMemberCode abiDecoderMemberSetup abiDecoderReentry
  abiEncoder compileEnv emitHelper ssaOperandFrame abiDecoderMemberBound abiDecoderContract
  exprLoweringProps fragExecMem instMemFrontier fragGasSeqMem fragGasPathMem
  fragGasSeqAbort abiDecoderBytesBound exprSimCalldataSlice freshWrites
  extcallDecoderMemberPreparationMemory extcallDecoderArrayPreparationMemory
  venomExecSemantics venomState venomInst memSafeRun emitHelperProps
  words arithmetic list rich_list

Theorem extcall_decoder_range_check_mem_ok:
  compile_abi_decode_range_check src e hi st = ((),st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem extcall_decoder_range_check_success:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h /\
  w2n p <= w2n q /\ w2n q <= w2n h /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  drule_all compile_abi_decode_range_check_sequence >> strip_tac >>
  drule compile_abi_decode_range_check_fragment_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (metis_tac[extcall_decoder_range_check_mem_ok]) >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extcall_decoder_range_check_reject_run[local]:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h /\
  ~(w2n p <= w2n q /\ w2n q <= w2n h) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
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
  `eval_operand no_wrap s4 =
    SOME (bool_to_word (bool_to_word (w2n q < w2n p) = 0w))` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  `eval_operand ok s5 = SOME 0w` by
    (Cases_on `w2n q < w2n p` >> Cases_on `w2n h < w2n q` >>
     gvs[bool_to_word_def, WORD_AND_CLAUSES]) >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  ntac 4 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  drule_all run_inst_seq_emit_extend >> metis_tac[]
QED

Theorem extcall_decoder_range_check_reject:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h /\
  ~(w2n p <= w2n q /\ w2n q <= w2n h) /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?n t. gas_path_mem ctx func s n (Abort Revert_abort t)
Proof
  strip_tac >>
  drule_all extcall_decoder_range_check_reject_run >> strip_tac >>
  drule compile_abi_decode_range_check_fragment_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[extcall_decoder_range_check_mem_ok] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[fragGasModeTheory.gas_marked_path_def] >> metis_tac[]
QED


Theorem extcall_decoder_bytes_head_mem_ok:
  abi_decode_bytes_head src hi st = (head,st') ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  Cases_on `hi = Lit 0w`
  >- (simp[abi_decode_bytes_head_def, comp_return_def] >> strip_tac >>
      gvs[emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >> rpt strip_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem extcall_decoder_bytes_head_reject_run[local]:
  abi_decode_bytes_head src hi st = (head,st') /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand hi s = SOME (n2w h) /\ sb < dimword(:256) /\
  h < dimword(:256) /\ h < sb+32 /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit 32w] st = (head,c1)` >>
  rename1 `compile_abi_decode_range_check src head hi c1 = ((),fin)` >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[word_add_n2w] >>
  `eval_operand src s1 = SOME (n2w sb) /\
   eval_operand hi s1 = SOME (n2w h)` by metis_tac[] >>
  `~(w2n (n2w sb : bytes32) <= w2n (n2w (sb+32) : bytes32) /\
      w2n (n2w (sb+32) : bytes32) <= w2n (n2w h : bytes32))` by
    (mp_tac (Q.INST [`modulus` |-> `dimword(:256)`, `a` |-> `sb`, `n` |-> `32`, `limit` |-> `h`] slice_bounds_mod) >>
     simp[w2n_n2w, dimword_def] >> decide_tac) >>
  drule_all extcall_decoder_range_check_reject_run >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac compile_abi_decode_range_check_shape >>
  `emitted_insts st fin = emitted_insts st c1 ++ emitted_insts c1 fin` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts c1 fin` assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem extcall_decoder_bytes_head_success:
  abi_decode_bytes_head src hi st = (head,st') /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand hi s = SOME (n2w h) /\ sb+32 <= h /\
  h < dimword(:256) /\ fresh_vars_wrt st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
      eval_operand head t = SOME (n2w (sb+32)) /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  `writes_fresh st (emitted_insts st st')` by
    metis_tac[extcall_decoder_bytes_head_fresh, straight_fresh_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_halted = s.vs_halted` by
    (qpat_x_assum `t = _ with vs_vars := _` SUBST1_TAC >> simp[]) >>
  drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[extcall_decoder_bytes_head_mem_ok] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem extcall_decoder_bytes_head_reject:
  abi_decode_bytes_head src hi st = (head,st') /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand hi s = SOME (n2w h) /\ sb < dimword(:256) /\
  h < dimword(:256) /\ h < sb+32 /\ fresh_vars_wrt st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?n t. gas_path_mem ctx func s n (Abort Revert_abort t)
Proof
  strip_tac >> drule_all extcall_decoder_bytes_head_reject_run >> strip_tac >>
  drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    metis_tac[extcall_decoder_bytes_head_mem_ok] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[fragGasModeTheory.gas_marked_path_def] >> metis_tac[]
QED

Theorem extcall_decoder_underflow_reject_run[local]:
  emit_op LT [actual;src] st = (under,c1) /\
  emit_op ISZERO [under] c1 = (ok,c2) /\
  emit_void ASSERT [ok] c2 = ((),fin) /\ fresh_vars_wrt st s /\
  eval_operand actual s = SOME a /\ eval_operand src s = SOME b /\
  w2n a < w2n b ==>
  ?t. run_inst_seq (emitted_insts st fin) s = Abort Revert_abort t
Proof
  strip_tac >> drule_all emit_op_LT_correct >> strip_tac >>
  gvs[bool_to_word_def] >> drule_all emit_op_ISZERO_correct >> strip_tac >>
  gvs[bool_to_word_def] >> drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> metis_tac[]
QED

Theorem extcall_decoder_member_pointer_wrap_run[local]:
  compile_getelemptr_abi src T ao MLOAD base_op hi st = (member_ptr,fin) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off /\
  sb < dimword(:256) /\ off < dimword(:256) /\
  dimword(:256) <= sb+off /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st fin) s = Abort Revert_abort t /\
      inst_extends st fin
Proof
  strip_tac >> qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w ao)] st = (hp,c1)` >>
  rename1 `compile_abi_dec_addr base_op hp c1 = (ha,c2)` >>
  rename1 `emit_op MLOAD [ha] c2 = (ov,c3)` >>
  rename1 `emit_op ADD [src;ov] c3 = (member_ptr,c4)` >>
  rename1 `emit_op LT [member_ptr;src] c4 = (under,c5)` >>
  rename1 `emit_op ISZERO [under] c5 = (ok,c6)` >>
  rename1 `emit_void ASSERT [ok] c6 = ((),last)` >>
  `compile_getelemptr_abi src T ao MLOAD base_op (Lit 0w) st = (member_ptr,c4)` by
    simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off` by
    simp[ADD_COMM] >>
  drule_all abi_decode_dynamic_member_pointer_sentinel >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c4) s = OK prepared` >>
  `eval_operand src prepared = SOME (n2w sb)` by metis_tac[] >>
  `w2n (n2w (sb+off) : bytes32) < w2n (n2w sb : bytes32)` by
    (mp_tac (Q.INST [`modulus` |-> `dimword(:256)`, `a` |-> `sb`,
        `n` |-> `off`, `limit` |-> `dimword(:256)-1`] slice_bounds_mod) >>
     simp[w2n_n2w] >>
     `0 < dimword(:256)` by simp[] >>
     `((off+sb) MOD dimword(:256)) < dimword(:256)` by simp[] >> decide_tac) >>
  drule_all extcall_decoder_underflow_reject_run >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c4 last /\ inst_extends st last` by
    metis_tac[inst_extends_trans] >>
  drule_all run_inst_seq_emit_extend >> metis_tac[]
QED

Theorem extcall_decoder_member_setup_wrap_run[local]:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,fin) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off /\
  sb < dimword(:256) /\ off < dimword(:256) /\
  dimword(:256) <= sb+off /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st fin) s = Abort Revert_abort t
Proof
  strip_tac >> qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_member_setup_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T ao MLOAD base_op hi st = (mp,mid)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] mid = (dp,last)` >>
  `abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off` by simp[ADD_COMM] >>
  `dimword(:256) <= sb+off` by simp[ADD_COMM] >>
  drule_all extcall_decoder_member_pointer_wrap_run >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  `!u. run_inst_seq (emitted_insts st mid) s <> OK u` by simp[] >>
  drule_all run_inst_seq_emit_extend_err >> metis_tac[]
QED

Theorem extcall_decoder_member_setup_wrap_reject:
  abi_decode_member_setup dst src MLOAD base_op hi T ao vo st = (ops,fin) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w off /\
  sb < dimword(:256) /\ off < dimword(:256) /\ dimword(:256) <= sb+off /\
  B+sb+ao < dimword(:256) /\ B+sb+ao+32 <= s.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var base_op /\ fresh_vars_wrt st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?n t. gas_path_mem ctx func s n (Abort Revert_abort t)
Proof
  strip_tac >> drule_all extcall_decoder_member_setup_wrap_run >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st fin)` by fs[EVERY_CONJ] >>
  `run_inst_seq_mem_ok (emitted_insts st fin) s` by
    (irule extcall_decoder_member_setup_mem_ok >> metis_tac[]) >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[fragGasModeTheory.gas_marked_path_def] >> metis_tac[]
QED
