(* Conditional composite decoder replay: concrete guarded entry phases. *)
Theory extcallDecoderCompositeMemory
Ancestors
  extcallDecoderPreparationMemory extcallDecoderHeadBounds
  extcallDecoderMemberSemantics extcallDecoderArraySemantics extcallDecoderStaticSuffix
  extcallDecoderPrefixMemory extcallDecoderBulkMemory extcallDecoderLoopEdgesMemory
  abiDecoderComplexGuard abiDecoderComplexHead freshWrites exprSimCalldataSlice
  abiDecoderReentry abiDecoderVarSequence abiDecoderDynamicLoopSetup
  loweringStateRelDefs varsExt
  fragGasSeqMem fragGasSeqAbort fragGasMode fragGasPathMem instMemFrontier
  abiDecoderGuard abiDecoderGuards abiDecoderRange abiDecoderBytesBound
  abiEncoder compileEnv emitHelper fragExecMem abiDecoderContract
  emitHelperProps exprLoweringProps
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem extcall_decoder_complex_guard_mem_ok[local]:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) ==>
  run_inst_seq_mem_ok (emitted_insts st fin) s
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >> rpt strip_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem extcall_decoder_complex_guard_reject_run[local]:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand hi s = SOME (n2w H) /\
  sb < dimword(:256) /\ H < dimword(:256) /\ headsz < dimword(:256) /\
  H < sb+headsz /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st fin) s = Abort Revert_abort t
Proof
  strip_tac >> qpat_x_assum `abi_decode_complex_head_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_complex_head_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [src; Lit (n2w headsz)] st = (endop,c1)` >>
  `eval_operand (Lit (n2w headsz)) s = SOME (n2w headsz)` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[word_add_n2w] >>
  `eval_operand src s1 = SOME (n2w sb) /\ eval_operand hi s1 = SOME (n2w H)` by metis_tac[] >>
  `~(w2n (n2w sb : bytes32) <= w2n (n2w (sb+headsz) : bytes32) /\
      w2n (n2w (sb+headsz) : bytes32) <= w2n (n2w H : bytes32))` by
    (mp_tac (Q.INST [`modulus` |-> `dimword(:256)`, `a` |-> `sb`,
       `n` |-> `headsz`, `limit` |-> `H`] slice_bounds_mod) >>
     simp[w2n_n2w] >> decide_tac) >>
  `eval_operand endop s1 = SOME (n2w (sb+headsz))` by simp[ADD_COMM] >>
  drule_all extcall_decoder_range_check_reject_run >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac compile_abi_decode_range_check_shape >>
  `emitted_insts st fin = emitted_insts st c1 ++ emitted_insts c1 fin` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts c1 fin` assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem extcall_decoder_complex_guard_reject:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand hi s = SOME (n2w H) /\
  sb < dimword(:256) /\ H < dimword(:256) /\ headsz < dimword(:256) /\
  H < sb+headsz /\ abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?k t. gas_path_mem ctx fn s k (Abort Revert_abort t)
Proof
  strip_tac >>
  `(!z. src = Var z ==> not_fresh_at st z) /\
   (!z. hi = Var z ==> not_fresh_at st z)` by
    (Cases_on `src` >> Cases_on `hi` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `eval_operand src (drop_fresh st s) = SOME (n2w sb) /\
   eval_operand hi (drop_fresh st s) = SOME (n2w H)` by
    asm_simp_tac bool_ss [eval_operand_drop_fresh] >>
  `fresh_vars_wrt st (drop_fresh st s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all extcall_decoder_complex_guard_reject_run >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st fin)` by gvs[EVERY_CONJ, EVERY_MEM] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    ~is_ext_call_op i.inst_opcode) (emitted_insts st fin)` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >>
     Cases_on `i.inst_opcode` >> gvs[abi_decoder_reentry_opcode_def, is_ext_call_op_def]) >>
  `vars_ext (drop_fresh st s) s` by simp[vars_ext_drop_fresh] >>
  drule_all run_inst_seq_vars_ext >>
  simp[vars_ext_result_def] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st fin) s` by
    metis_tac[extcall_decoder_complex_guard_mem_ok] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.SPEC `T` run_inst_seq_abort_gas_path)) >>
  simp[gas_marked_path_def] >> metis_tac[]
QED

Theorem extcall_decoder_complex_guard_success:
  abi_decode_complex_head_guard src hi headsz st = ((),fin) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand hi s = SOME (n2w H) /\
  sb+headsz <= H /\ H < dimword(:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  fin.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st fin) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?k t. gas_path_mem ctx fn s k
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st fin))) /\
    fresh_vars_wrt limit t /\ abi_decoder_address_frame st.cs_next_var s t
Proof
  strip_tac >>
  Q.SUBGOAL_THEN `hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    sb+headsz <= hb /\ hb < dimword(:256)` assume_tac >- metis_tac[] >>
  drule_all abi_decoder_complex_guard_reentry >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st fin)` by gvs[EVERY_CONJ, EVERY_MEM] >>
  `run_inst_seq_mem_ok (emitted_insts st fin) s` by
    metis_tac[extcall_decoder_complex_guard_mem_ok] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st fin))`,
    `actual`] >> simp[ADD_COMM]
QED
