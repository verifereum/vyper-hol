(* Memory-safe execution of the bulk dynamic-array decoder. *)
Theory abiDecodeMemBulk
Ancestors
  abiDecoderReentry abiDecodeMemBytesGuards abiDecodeMemCountGuard abiDecoderBulk
  abiDecoderDynarrayBound abiDecoderDynarrayPrefix abiDecoderBytesPrefix
  abiDecoderRange abiDecoderBytesBound abiDecoderContract
  entryDecoderHistoryFrame entrySinkExtraction allocaHistoryFragment
  fragGasMode fragGasPathMem fragGasSeqMem fragGasSeqAbort freshWrites
  fragExec fragExecMem bodyUnopFragMemory instMemFrontier memSafeRun localPtrsProps
  loweringStateRelDefs emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_dynarray_payload_guard_path_mem:
  abi_decode_dynarray_payload_guard head cnt stride hi st = ((),st') /\
  hi <> Lit 0w /\ eval_operand head s = SOME p /\
  eval_operand cnt s = SOME q /\ eval_operand hi s = SOME h /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n p <= w2n (p+q*n2w stride) /\ w2n (p+q*n2w stride) <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_allocas = s.vs_allocas /\ alloca_history func t) /\
  (~(w2n p <= w2n (p+q*n2w stride) /\ w2n (p+q*n2w stride) <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_dynarray_payload_guard_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt;Lit (n2w stride)] st = (sz,mid)` >>
  `abi_decode_bytes_payload_guard head sz hi mid = ((),st')` by
    gvs[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  `inst_extends mid st' /\ st'.cs_blocks = mid.cs_blocks /\
   st'.cs_current_bb = mid.cs_current_bb` by
    metis_tac[abi_decode_bytes_payload_guard_fragment_shape] >>
  `fn_has_code st mid func /\ fn_has_code mid st' func` by
    (gvs[fn_has_code_def, emitted_blocks_def, inst_extends_def] >>
     metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `eval_operand (Lit (n2w stride)) s = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK u` >>
  suspend "multiply_path"
QED

Resume abi_decode_dynarray_payload_guard_path_mem[multiply_path]:
  `straight_fresh (emit_op MUL [cnt;Lit (n2w stride)])` by
    (irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
  `writes_fresh st (emitted_insts st mid)` by fs[straight_fresh_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op u = eval_operand op s` by
    (Cases >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def, lookup_var_def, not_fresh_at_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st mid) s` by metis_tac[writes_fresh_mem_ok] >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `mid.cs_current_bb = st.cs_current_bb /\
   isPREFIX st.cs_current_insts mid.cs_current_insts` by fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st mid) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st mid)` by simp[mk_inst_def, is_terminator_def, is_alloca_op_def] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st mid)` by fs[EVERY_MEM] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all abi_decode_nonallocating_sequence_frame >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st mid) = LENGTH mid.cs_current_insts` by
    (gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  suspend "multiply_cursor"
QED
Resume abi_decode_dynarray_payload_guard_path_mem[multiply_cursor]:
  qabbrev_tac `v = u with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  `gas_path_mem ctx func s 0 (OK v) /\ alloca_history func v /\
   eval_operand sz v = SOME (q*n2w stride) /\ fresh_vars_wrt mid v /\
   (!op w. eval_operand op s = SOME w ==> eval_operand op v = SOME w) /\
   v.vs_memory = s.vs_memory /\
   v.vs_call_ctx = s.vs_call_ctx /\ v.vs_data_section = s.vs_data_section /\
   v.vs_alloca_next = s.vs_alloca_next /\
   v.vs_allocas = s.vs_allocas /\ ~v.vs_halted /\
   v.vs_current_bb = mid.cs_current_bb /\ v.vs_inst_idx = LENGTH mid.cs_current_insts` by
    gvs[Abbr `v`, mk_inst_def, eval_operand_def, lookup_var_def, fresh_vars_wrt_def] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op s` by
    (simp[Abbr `v`, eval_operand_def, lookup_var_def]) >>
  `eval_operand head v = SOME p /\ eval_operand hi v = SOME h` by metis_tac[] >>
  `alloca_inv v` by (irule alloca_inv_fields >> metis_tac[]) >>
  drule_all abi_decode_bytes_payload_guard_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_dynarray_payload_guard_path_mem[accept]:
  strip_tac >> gvs[] >>
  `gas_path_mem ctx func s 0 (OK t)` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `st.cs_next_var <= mid.cs_next_var` by decide_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[abi_decoder_operand_live_mono]
QED
Resume abi_decode_dynarray_payload_guard_path_mem[reject]:
  strip_tac >> gvs[] >> fs[gas_marked_path_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED
Finalise abi_decode_dynarray_payload_guard_path_mem
