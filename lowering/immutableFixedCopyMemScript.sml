(* Memory safety of fixed constructor immutable writes. *)
Theory immutableFixedCopyMem
Ancestors
  immutableAssignStoreMem immutableCopyExecution bodyImmutableCopyMemory
  abiDecoderBytesPrefix abiEncoderWindowSequence windowSequenceMem
  instMemFrontier memSafeRun fragExecMem fragExec
  context compileEnv emitHelper emitHelperProps loweringStateRelDefs
  exprLoweringProps venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map

Theorem immutable_offset_allocation_frame[local]:
  compile_lit_byte_offset op off sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      strip_tac >> gvs[emitted_insts_def, run_inst_seq_def]) >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, run_inst_seq_def] >>
  irule abi_decode_nonallocating_sequence_frame >>
  goal_assum (drule_at Any) >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[DROP_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem immutable_load_mem_ok[local]:
  emit_op MLOAD [op] sa = (r,sb) /\
  eval_operand op s = SOME a /\ w2n a + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD]
QED

Theorem immutable_load_allocation_frame[local]:
  emit_op MLOAD [op] sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule abi_decode_nonallocating_sequence_frame >>
  goal_assum (drule_at Any) >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[DROP_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem immutable_frame_mem_append[local]:
  immutable_execution_frame sa s sm t /\
  immutable_execution_frame sm t sb u /\
  run_inst_seq_mem_ok (emitted_insts sa sm) s /\
  run_inst_seq_mem_ok (emitted_insts sm sb) t ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[immutable_execution_frame_def] >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[]
QED

Theorem immutable_store_allocation_frame[local]:
  compile_imm_store_word (SOME region) dst value sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> irule abi_decode_nonallocating_sequence_frame >>
  goal_assum (drule_at Any) >>
  drule compile_imm_store_word_result >> strip_tac >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def,
       is_terminator_def, is_alloca_op_def]
QED

Theorem immutable_fixed_read_mem[local]:
  compile_lit_byte_offset src off sa = (op,sm) /\
  emit_op MLOAD [op] sm = (value,sb) /\
  eval_operand src s = SOME a /\ fresh_vars_wrt sa s /\
  w2n (a+n2w off) + 32 <= s.vs_alloca_next ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\
    eval_operand value t = SOME (mload (w2n (a+n2w off)) s)
Proof
  strip_tac >> drule_all immutable_offset_frame >> strip_tac >>
  rename1 `immutable_execution_frame sa s sm u` >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (irule immutable_offset_allocation_frame >>
     fs[immutable_execution_frame_def] >> metis_tac[]) >>
  drule immutable_execution_frame_operands >> strip_tac >>
  drule_all immutable_memory_load_frame >> strip_tac >>
  rename1 `immutable_execution_frame sm u sb t` >>
  qexists_tac `t` >> conj_tac
  >- (irule immutable_execution_frame_trans >> metis_tac[]) >>
  conj_tac
  >- (irule immutable_frame_mem_append >> qexistsl_tac [`sm`,`u`,`t`] >>
      simp[] >> conj_tac
      >- metis_tac[body_immutable_byte_offset_mem_ok] >>
      irule immutable_load_mem_ok >> metis_tac[]) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (irule immutable_load_allocation_frame >>
     fs[immutable_execution_frame_def] >> metis_tac[]) >>
  gvs[mload_def]
QED

Theorem immutable_fixed_write_mem[local]:
  compile_lit_byte_offset dst off sa = (op,sm) /\
  compile_imm_store_word (SOME region) op value sm = ((),sb) /\
  eval_operand dst s = SOME b /\ eval_operand region s = SOME 0w /\
  eval_operand value s = SOME v /\ fresh_vars_wrt sa s /\
  w2n (b+n2w off) + 32 <= s.vs_alloca_next ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all immutable_offset_frame >> strip_tac >>
  rename1 `immutable_execution_frame sa s sm u` >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (irule immutable_offset_allocation_frame >>
     fs[immutable_execution_frame_def] >> metis_tac[]) >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand value u = SOME v /\ eval_operand region u = SOME 0w` by
    metis_tac[] >>
  drule_all immutable_store_execution_frame >> strip_tac >>
  rename1 `immutable_execution_frame sm u sb t` >>
  qexists_tac `t` >> conj_tac
  >- (irule immutable_execution_frame_trans >> metis_tac[]) >>
  conj_tac
  >- (irule immutable_frame_mem_append >> qexistsl_tac [`sm`,`u`,`t`] >>
      simp[] >> conj_tac
      >- metis_tac[body_immutable_byte_offset_mem_ok] >>
      irule immutable_store_word_mem_ok >> metis_tac[]) >>
  `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (irule immutable_store_allocation_frame >>
     fs[immutable_execution_frame_def] >> metis_tac[]) >>
  simp[]
QED

Theorem immutable_store_one_mem:
  immutable_store_one (SOME region) src dst off sa = ((),sb) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt sa s /\
  w2n (a+n2w off) + 32 <= s.vs_alloca_next /\
  w2n (b+n2w off) + 32 <= s.vs_alloca_next ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  drule_all immutable_fixed_read_mem >> strip_tac >>
  rename1 `immutable_execution_frame sa s sm u` >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand dst u = SOME b /\ eval_operand region u = SOME 0w` by
    metis_tac[] >>
  `w2n (b+n2w off) + 32 <= u.vs_alloca_next` by simp[] >>
  drule_all immutable_fixed_write_mem >> strip_tac >>
  rename1 `immutable_execution_frame sm u sb t` >>
  qexists_tac `t` >> conj_tac
  >- (irule immutable_execution_frame_trans >> metis_tac[]) >>
  conj_tac >- (irule immutable_frame_mem_append >> metis_tac[]) >> simp[]
QED

Theorem immutable_fixed_words_mem:
  !n off sa sb s a b.
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt sa s /\
  w2n a + off + 32*n <= s.vs_alloca_next /\
  w2n b + off + 32*n <= s.vs_alloca_next /\
  w2n a + off + 32*n < dimword (:256) /\
  w2n b + off + 32*n < dimword (:256) ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Induct
  >- (simp[compile_imm_store_words_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[immutable_execution_frame_def, immutable_operand_frame_refl,
           emitted_insts_def, run_inst_seq_def, run_inst_seq_mem_ok_def,
           same_blocks_def]) >>
  simp[immutable_store_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >>
  `w2n (a+n2w off) + 32 <= s.vs_alloca_next /\
   w2n (b+n2w off) + 32 <= s.vs_alloca_next` by
    (conj_tac >> irule body_immutable_copy_offset_range >>
     simp[MULT_SUC] >> decide_tac) >>
  drule_all immutable_store_one_mem >> strip_tac >>
  rename1 `immutable_execution_frame sa s sm u` >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand src u = SOME a /\ eval_operand dst u = SOME b /\
   eval_operand region u = SOME 0w` by metis_tac[] >>
  `?t. immutable_execution_frame sm u sb t /\
    run_inst_seq_mem_ok (emitted_insts sm sb) u /\
    t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_x_assum `!off sa sb s a b. _`
       (qspec_then `off+32` irule) >>
     goal_assum (drule_at Any) >> simp[] >> gvs[MULT_SUC] >>
     metis_tac[]) >>
  qexists_tac `t` >> conj_tac
  >- (irule immutable_execution_frame_trans >> metis_tac[]) >>
  conj_tac >- (irule immutable_frame_mem_append >> metis_tac[]) >> simp[]
QED

