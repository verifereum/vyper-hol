(* Physical memory certificate for the actual dynamic-array bulk branch. *)
Theory extcallDecoderBulkMemory
Ancestors
  abiEncoder abiDecoderBulk abiDecoderBulkExecute abiDecoderArrayHeader abiDecoderComposition
  abiDecoderGuard abiDecoderFrame abiDecoderFrameCompose abiDecoderContract
  extcallDecoderAtomicMemory fragExecMem fragGasSeqMem fragGasPathMem
  ssaOperandFrame instMemFrontier emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomInst venomState words list rich_list arithmetic

Theorem extcall_decoder_bulk_payload_mem_ok[local]:
  abi_decode_bulk_payload dst src cnt mem_sz MLOAD base_op st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand cnt s = SOME (n2w n) /\
  B+sb+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  n*mem_sz < dimword (:256) /\
  B+sb+32+n*mem_sz <= s.vs_alloca_next /\
  d+32+n*mem_sz <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  `!k. st.cs_next_var <= k ==>
     src <> Var (STRING #"%" (toString k)) /\
     dst <> Var (STRING #"%" (toString k)) /\
     cnt <> Var (STRING #"%" (toString k)) /\
     base_op <> Var (STRING #"%" (toString k))` by
    (rpt strip_tac >> gvs[] >>
     metis_tac[fresh_vars_wrt_eval_operand, GREATER_EQ]) >>
  Cases_on `base_op = Lit 0w` >>
  qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def,
       abi_decode_copy_opcode_def, comp_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_mem_ok_def, below_frontier_no_ranges,
       step_inst_base_opcode_eqs, mk_inst_def] >>
  simp[exec_pure2_def, eval_operand_update_var_avoids,
       eval_operand_def, lookup_var_update_var, word_mul_n2w, word_add_n2w,
       below_frontier_MCOPY, GSYM mk_inst_def, w2n_n2w]
QED

Theorem extcall_decoder_array_count_mem_ok:
  abi_decode_array_header dst addr MLOAD st = (cnt,st') /\
  eval_operand addr s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  w2n p+32 <= s.vs_alloca_next /\ d < dimword (:256) /\
  d+32 <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  `dst <> Var (STRING #"%" (toString st.cs_next_var))` by
    (strip_tac >> gvs[] >> metis_tac[fresh_vars_wrt_eval_operand, GREATER_EQ, LESS_EQ_REFL]) >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, run_inst_seq_mem_ok_def,
       below_frontier_MLOAD, below_frontier_MSTORE,
       step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_update_var_avoids, eval_operand_def, lookup_var_update_var, w2n_n2w] >>
  simp[exec_read1_def, exec_write2_def, eval_operand_update_var_avoids,
       eval_operand_def, lookup_var_update_var, GSYM mk_inst_def,
       below_frontier_MLOAD, below_frontier_MSTORE, w2n_n2w]
QED

Theorem extcall_decoder_bulk_body_mem_ok[local]:
  abi_decode_bulk_body dst src addr MLOAD base_op mem_sz st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand addr s = SOME (n2w (B+sb)) /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decode_load MLOAD (n2w (B+sb) : bytes32) s = n2w n /\
  B+sb+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  n*mem_sz < dimword (:256) /\
  B+sb+32+n*mem_sz <= s.vs_alloca_next /\
  d+32+n*mem_sz <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst addr MLOAD st = (cnt,c1)` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `d < dimword (:256) /\ B+sb < dimword (:256) /\
   d+32 <= s.vs_alloca_next /\ B+sb+32 <= s.vs_alloca_next` by decide_tac >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK prepared` >>
  `w2n (n2w (B+sb) : bytes32)+32 <= s.vs_alloca_next` by simp[w2n_n2w] >>
  drule_all extcall_decoder_array_count_mem_ok >> strip_tac >>
  `prepared.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
     qpat_x_assum `run_inst_seq _ _ = OK prepared` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[DROP_LENGTH_APPEND, run_inst_seq_def, step_inst_base_opcode_eqs,
          mk_inst_def, exec_read1_def, exec_write2_def, AllCaseEqs()] >>
     strip_tac >> gvs[mstore_def, write_memory_with_expansion_def]) >>
  `eval_operand src prepared = SOME (n2w sb) /\
   eval_operand base_op prepared = SOME (n2w B) /\
   eval_operand dst prepared = SOME (n2w d)` by metis_tac[] >>
  `eval_operand cnt prepared = SOME (n2w n) /\
   B+sb+32+n*mem_sz <= prepared.vs_alloca_next /\
   d+32+n*mem_sz <= prepared.vs_alloca_next` by simp[] >>
  `run_inst_seq_mem_ok (emitted_insts c1 st') prepared` by
    (irule extcall_decoder_bulk_payload_mem_ok >>
     conj_tac >- (qexistsl [`B`, `base_op`, `cnt`, `d`, `dst`, `mem_sz`, `n`, `sb`, `src`] >> simp[]) >>
     simp[]) >>
  `inst_extends c1 st'` by
    (qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `base_op = Lit 0w` >>
     simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def,
          abi_decode_copy_opcode_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def,
         inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND]) >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[]
QED

(* The guarded bulk body, with the physical source snapshot kept separate
   from the payload's semantic interpretation. *)
Theorem extcall_decoder_bulk_body_path:
  abi_decode_bulk_body dst src addr MLOAD base_op mem_sz st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand addr s = SOME (n2w (B+sb)) /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decode_load MLOAD (n2w (B+sb) : bytes32) s = n2w n /\
  B+sb+32 < dimword (:256) /\ d+32 < dimword (:256) /\
  n*mem_sz < dimword (:256) /\
  B+sb+32+n*mem_sz <= s.vs_alloca_next /\
  d+32+n*mem_sz <= s.vs_alloca_next /\
  (B+sb+32+n*mem_sz <= d \/ d+32 <= B+sb+32) /\
  (B+H <= d \/ d+(32+n*mem_sz) <= B) /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
      mem_word_at d t.vs_memory = n2w n /\
      mem_bytes_at (d+32) (n*mem_sz) t.vs_memory =
        mem_bytes_at (B+sb+32) (n*mem_sz) s.vs_memory /\
      mem_bytes_at B H t.vs_memory = mem_bytes_at B H s.vs_memory /\
      abi_decode_frame d (32+n*mem_sz) s t /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      inst_extends st st'
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `MLOAD`] abi_decode_bulk_body_sequence)) >>
  disch_then (qspecl_then [`B`, `sb`, `s`, `n`, `d`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule extcall_decoder_bulk_body_mem_ok >>
     conj_tac >- (qexistsl [`B`, `addr`, `base_op`, `d`, `dst`, `mem_sz`, `n`, `sb`, `src`] >> simp[]) >>
     simp[]) >>
  drule_all abi_decode_bulk_body_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  `mem_bytes_at B H t.vs_memory = mem_bytes_at B H s.vs_memory` by
    (irule (SRULE [abi_decode_source_def, abi_decode_source_opcode_def]
       (Q.INST [`opc` |-> `MLOAD`] abi_decode_frame_source_window)) >>
     qexistsl [`d`, `32+n*mem_sz`] >> simp[]) >>
  qexists_tac `t` >> gvs[abi_decode_source_def]
QED
