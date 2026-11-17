(* Counted memory-safe paths through allocation-free calldata bulk decoding. *)
Theory sourceBulkGasMem
Ancestors
  calldataBulkLive calldataBulkLeaf calldataBytesLeaf calldataBytesLive calldataWordLeaf
  calldataDynOwned safeSequence
  abiDecoderBulkExecute abiDecoderBulk abiDecoderContract abiDecoderGuards
  abiDecoderComposition abiDecoderReentry abiDecoderRange abiDecoderGuard abiEncoder
  fragGasSeqMem fragExecMem stmtReasonLitFragMemory
  compileEnv emitHelper emitHelperProps exprLoweringProps
  venomInst venomState venomExecSemantics words list rich_list arithmetic

Theorem source_bulk_prefix_safe[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  w2n (abi_decode_load CALLDATALOAD p s) <= maxn /\ maxn < dimword (:256) /\
  d+32 < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s)*mem_sz < dimword (:256) /\
  d+32+w2n (abi_decode_load CALLDATALOAD p s)*mem_sz <= s.vs_alloca_next ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [calldata_bulk_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule calldata_bulk_body_extends >> strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >>
     drule emitted_insts_emit_void >> strip_tac >> gvs[]) >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac calldata_prefix_safe_append >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  gen_tac >> strip_tac >>
  drule_all calldata_count_guard_repeat_sequence >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_bulk_body_live_prefix_safe) >>
  `eval_operand src t = SOME p /\ eval_operand dst t = SOME (n2w d)` by metis_tac[] >>
  `abi_decode_load CALLDATALOAD p t = abi_decode_load CALLDATALOAD p s` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  qexistsl_tac [`src`,`p`,`mem_sz`,`dst`,`d`] >> simp[]
QED

Theorem source_bulk_no_gas[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts st st')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [calldata_bulk_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  qpat_x_assum `abi_decode_bulk_body _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, abi_decode_bulk_body_def,
    abiDecoderArrayHeaderTheory.abi_decode_array_header_def,
    abi_decode_bulk_payload_def, abi_decode_copy_opcode_def,
    compile_abi_dec_addr_def, abi_decode_le_guard_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  gvs[emitted_insts_def, mk_inst_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac bool_ss [DROP_LENGTH_APPEND, APPEND] >> simp[mk_inst_def]
QED

Theorem source_bulk_run_gas_path_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) sa = ((),sb) /\
  ~dec_info_needs_clamp ei /\
  eval_operand src s = SOME (n2w pos) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load CALLDATALOAD (n2w pos : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  pos + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var dst /\
  sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  d + (32 + n * mem_sz) <= s.vs_alloca_next /\
  d + (32 + n * mem_sz) < dimword (:256) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK actual ==>
  gas_path_mem ctx fn s 0 (OK (actual with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >>
     reverse conj_tac >- (drule calldata_bulk_opcodes >> simp[EVERY_MEM]) >>
     ho_match_mp_tac (GEN_ALL source_bulk_prefix_safe) >>
     qexistsl_tac [`src`, `n2w pos`, `mem_sz`, `maxn`, `ei`, `dst`, `d`, `abi_sz`] >>
     simp[] >> decide_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[source_bulk_no_gas] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
  drule_all fn_has_code_code >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    simp[FILTER_EQ_NIL] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all run_inst_seq_gas_path_mem >> simp[]
QED
