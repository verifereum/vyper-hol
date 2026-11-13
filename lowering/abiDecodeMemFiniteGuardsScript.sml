(* Finite guard witnesses used to replay scratch-free decoders. *)
Theory abiDecodeMemFiniteGuards
Ancestors
  abiDecodeMemRange abiDecodeMemCountGuard abiDecoderRange abiDecoderBytesBound
  abiDecoderGuards abiDecoderDynarrayBound abiDecoderBytesPrefix abiDecoderContract freshWrites
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  fragExecMem instMemFrontier memSafeRun bodyUnopFragMemory
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_decode_add_range_sequence_mem:
  emit_op ADD [a;b] st = (v,mid) /\
  compile_abi_decode_range_check a v hi mid = ((),en) /\
  eval_operand a s = SOME p /\ eval_operand b s = SOME q /\
  eval_operand hi s = SOME h /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\ inst_extends st en /\
  (w2n p <= w2n (p+q) /\ w2n (p+q) <= w2n h ==>
    ?t. run_inst_seq (emitted_insts st en) s = OK t /\
      eval_operand v t = SOME (p+q) /\ fresh_vars_wrt en t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (~(w2n p <= w2n (p+q) /\ w2n (p+q) <= w2n h) ==>
    ?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t)
Proof
  strip_tac >> drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK u` >>
  `eval_operand a u = SOME p /\ eval_operand hi u = SOME h` by metis_tac[] >>
  `inst_extends mid en` by metis_tac[compile_abi_decode_range_check_shape] >>
  `inst_extends st en` by metis_tac[inst_extends_trans] >>
  `emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st mid) s` by
    (drule emitted_insts_emit_op >> strip_tac >>
     irule run_inst_seq_mem_ok_every >>
     simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def,
          is_alloca_op_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
     metis_tac[abi_decode_range_mem_ok]) >>
  simp[] >> conj_tac >- suspend "accept" >>
  strip_tac >> drule_all abi_decode_range_sequence >> simp[] >> strip_tac >>
  asm_rewrite_tac[] >> drule run_inst_seq_append >> simp[] >> metis_tac[]
QED
Resume abi_decode_add_range_sequence_mem[accept]:
  strip_tac >> drule_all compile_abi_decode_range_check_sequence >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st en)` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `compile_abi_decode_range_check _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> strip_tac >>
     gvs[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]) >>
  drule_all abi_decode_nonallocating_sequence_frame >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Finalise abi_decode_add_range_sequence_mem

Theorem abi_decode_mload_count_sequence_mem:
  abi_decode_count_guard MLOAD src limit st = (count_op,en) /\
  eval_operand src s = SOME p /\ w2n p+32 <= s.vs_alloca_next /\
  limit < dimword (:256) /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\
  (w2n (abi_decode_load MLOAD p s) <= limit ==>
    ?t. run_inst_seq (emitted_insts st en) s = OK t /\
      eval_operand count_op t = SOME (abi_decode_load MLOAD p s) /\
      fresh_vars_wrt en t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\ inst_extends st en /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (limit < w2n (abi_decode_load MLOAD p s) ==>
    ?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t)
Proof
  strip_tac >> drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all abi_decode_mload_count_mem_ok >> strip_tac >> simp[] >>
  conj_tac
  >- (strip_tac >>
      `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
      `abi_decode_load MLOAD p s = n2w (w2n (abi_decode_load MLOAD p s))` by simp[] >>
      drule_all abi_decode_count_guard_sequence >> strip_tac >>
      drule abi_decode_mload_count_opcodes >> strip_tac >>
      `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
        (emitted_insts st en)` by fs[EVERY_MEM] >>
      drule_all abi_decode_nonallocating_sequence_frame >> metis_tac[]) >>
  strip_tac >> metis_tac[abi_decode_mload_count_rejected]
QED

Theorem abi_decode_bytes_head_sequence_mem:
  abi_decode_bytes_head src hi st = (head,en) /\ hi <> Lit 0w /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\ inst_extends st en /\
  (w2n p <= w2n (p+32w) /\ w2n (p+32w) <= w2n h ==>
    ?t. run_inst_seq (emitted_insts st en) s = OK t /\
      eval_operand head t = SOME (p+32w) /\ fresh_vars_wrt en t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (~(w2n p <= w2n (p+32w) /\ w2n (p+32w) <= w2n h) ==>
    ?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_range_sequence_mem >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem abi_decode_bytes_payload_sequence_mem:
  abi_decode_bytes_payload_guard head len hi st = ((),en) /\ hi <> Lit 0w /\
  eval_operand head s = SOME p /\ eval_operand len s = SOME q /\
  eval_operand hi s = SOME h /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\ inst_extends st en /\
  (w2n p <= w2n (p+q) /\ w2n (p+q) <= w2n h ==>
    ?t. run_inst_seq (emitted_insts st en) s = OK t /\
      fresh_vars_wrt en t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (~(w2n p <= w2n (p+q) /\ w2n (p+q) <= w2n h) ==>
    ?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all abi_decode_add_range_sequence_mem >> strip_tac >> simp[] >>
  metis_tac[]
QED

Theorem abi_decode_dynarray_payload_sequence_mem:
  abi_decode_dynarray_payload_guard head cnt stride hi st = ((),en) /\ hi <> Lit 0w /\
  eval_operand head s = SOME p /\ eval_operand cnt s = SOME q /\
  eval_operand hi s = SOME h /\ fresh_vars_wrt st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\ inst_extends st en /\
  (w2n p <= w2n (p+q*n2w stride) /\ w2n (p+q*n2w stride) <= w2n h ==>
    ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (~(w2n p <= w2n (p+q*n2w stride) /\ w2n (p+q*n2w stride) <= w2n h) ==>
    ?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_dynarray_payload_guard_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt;Lit (n2w stride)] st = (sz,mid)` >>
  `abi_decode_bytes_payload_guard head sz hi mid = ((),en)` by
    gvs[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  `eval_operand (Lit (n2w stride)) s = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK u` >>
  `eval_operand head u = SOME p /\ eval_operand hi u = SOME h` by metis_tac[] >>
  drule_all abi_decode_bytes_payload_sequence_mem >> strip_tac >>
  `inst_extends st en` by metis_tac[inst_extends_trans] >>
  `emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st mid) s` by
    (drule emitted_insts_emit_op >> strip_tac >> irule run_inst_seq_mem_ok_every >>
     simp[below_frontier_no_ranges, inst_dload_in_section_def, mk_inst_def,
       is_alloca_op_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  simp[] >> conj_tac >- suspend "accept" >>
  strip_tac >> gvs[] >> metis_tac[run_inst_seq_emit_extend]
QED
Resume abi_decode_dynarray_payload_sequence_mem[accept]:
  strip_tac >> gvs[] >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `emit_op MUL _ _ = _`
      (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq _ s = OK u` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, update_var_def, eval_operand_def] >> strip_tac >> gvs[]) >>
  `run_inst_seq (emitted_insts st en) s = OK t` by
    metis_tac[run_inst_seq_compose_ok] >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
Finalise abi_decode_dynarray_payload_sequence_mem
