(* Memory safety of fixed constructor immutable writes. *)
Theory immutableFixedOptionMem
Ancestors
  immutableStoreOptionMem immutableCopyExecution immutableConstructorRelation
  valueEncodingProps bodyImmutableCopyMemory
  abiDecoderBytesPrefix abiEncoderWindowSequence windowSequenceMem
  instMemFrontier memSafeRun fragExecMem fragExec memContinuation
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

Theorem immutable_fixed_read_mem[local]:
  compile_lit_byte_offset src off sa = (op,sm) /\
  emit_op MLOAD [op] sm = (value,sb) /\
  eval_operand src s = SOME a /\ fresh_vars_wrt sa s /\
  w2n (a+n2w off) + 32 <= s.vs_alloca_next ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_immutables = s.vs_immutables /\
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
  compile_imm_store_word imm op value sm = ((),sb) /\
  eval_operand dst s = SOME b /\ (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  eval_operand value s = SOME v /\ fresh_vars_wrt sa s /\
  w2n (b+n2w off) + 32 <= s.vs_alloca_next ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = (mstore (w2n (b+n2w off)) v s).vs_memory /\
    t.vs_immutables = s.vs_immutables |+ (w2n (b+n2w off),v)
Proof
  strip_tac >> drule_all immutable_offset_frame >> strip_tac >>
  rename1 `immutable_execution_frame sa s sm u` >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (irule immutable_offset_allocation_frame >>
     fs[immutable_execution_frame_def] >> metis_tac[]) >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand value u = SOME v /\ (!region. imm = SOME region ==> eval_operand region u = SOME 0w)` by
    metis_tac[] >>
  `w2n (b+n2w off) + 32 <= u.vs_alloca_next` by simp[] >>
  drule_all immutable_store_option_frame >> strip_tac >>
  rename1 `immutable_execution_frame sm u sb t` >>
  qexists_tac `t` >> conj_tac
  >- (irule immutable_execution_frame_trans >> metis_tac[]) >>
  conj_tac
  >- (irule immutable_frame_mem_append >>
      metis_tac[body_immutable_byte_offset_mem_ok]) >>
  gvs[mstore_def]
QED

Theorem immutable_store_one_mem_option:
  immutable_store_one imm src dst off sa = ((),sb) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\ fresh_vars_wrt sa s /\
  w2n (a+n2w off) + 32 <= s.vs_alloca_next /\
  w2n (b+n2w off) + 32 <= s.vs_alloca_next ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = (immutable_word_transfer T T a b off s).vs_memory /\
    t.vs_immutables = (immutable_word_transfer T T a b off s).vs_immutables
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  drule_all immutable_fixed_read_mem >> strip_tac >>
  rename1 `immutable_execution_frame sa s sm u` >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand dst u = SOME b /\ (!region. imm = SOME region ==> eval_operand region u = SOME 0w)` by
    metis_tac[] >>
  `w2n (b+n2w off) + 32 <= u.vs_alloca_next` by simp[] >>
  drule_all immutable_fixed_write_mem >> strip_tac >>
  rename1 `immutable_execution_frame sm u sb t` >>
  qexists_tac `t` >> conj_tac
  >- (irule immutable_execution_frame_trans >> metis_tac[]) >>
  conj_tac >- (irule immutable_frame_mem_append >> metis_tac[]) >>
  simp[immutable_word_transfer_def, immutable_copy_read_def, istore_def, mstore_def, mload_def]
QED

Theorem immutable_fixed_words_mem_option:
  !n off sa sb s a b.
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\ fresh_vars_wrt sa s /\
  w2n a + off + 32*n <= s.vs_alloca_next /\
  w2n b + off + 32*n <= s.vs_alloca_next /\
  w2n a + off + 32*n < dimword (:256) /\
  w2n b + off + 32*n < dimword (:256) ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = (immutable_transfers T T a b n off s).vs_memory /\
    t.vs_immutables = (immutable_transfers T T a b n off s).vs_immutables
Proof
  Induct
  >- (simp[compile_imm_store_words_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[immutable_execution_frame_def, immutable_operand_frame_refl,
           emitted_insts_def, run_inst_seq_def, run_inst_seq_mem_ok_def,
           same_blocks_def, immutable_transfers_def]) >>
  simp[immutable_store_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >>
  `w2n (a+n2w off) + 32 <= s.vs_alloca_next /\
   w2n (b+n2w off) + 32 <= s.vs_alloca_next` by
    (conj_tac >> irule body_immutable_copy_offset_range >>
     simp[MULT_SUC] >> decide_tac) >>
  drule_all immutable_store_one_mem_option >> strip_tac >>
  rename1 `immutable_execution_frame sa s sm u` >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand src u = SOME a /\ eval_operand dst u = SOME b /\
   (!region. imm = SOME region ==> eval_operand region u = SOME 0w)` by metis_tac[] >>
  `?t. immutable_execution_frame sm u sb t /\
    run_inst_seq_mem_ok (emitted_insts sm sb) u /\
    t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
    t.vs_memory = (immutable_transfers T T a b n (off+32) u).vs_memory /\
    t.vs_immutables = (immutable_transfers T T a b n (off+32) u).vs_immutables` by
    (qpat_x_assum `!off sa sb s a b. _`
       (qspec_then `off+32` irule) >>
     goal_assum (drule_at Any) >> simp[] >> gvs[MULT_SUC] >>
     metis_tac[]) >>
  qexists_tac `t` >> conj_tac
  >- (irule immutable_execution_frame_trans >> metis_tac[]) >>
  conj_tac >- (irule immutable_frame_mem_append >> metis_tac[]) >>
  simp[immutable_transfers_def] >> irule immutable_transfers_cong >>
  fs[immutable_execution_frame_def, immutable_transfer_data]
QED

Theorem immutable_store_one_code_option:
  immutable_store_one imm src dst off sa = ((),sb) ==>
  same_blocks sa sb /\
  ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) is
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  imp_res_tac immutable_byte_offset_extends >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emit_op_extends >>
  drule immutable_store_option_code >> strip_tac >>
  imp_res_tac exprSimCopyTheory.code_offset_insts >>
  conj_tac >- gvs[same_blocks_def] >>
  qexists_tac `emitted_insts sa st1 ++ emitted_insts st1 st1' ++
    emitted_insts st1' st1'' ++ emitted_insts st1'' sb` >>
  conj_tac >- simp[APPEND_ASSOC] >>
  simp[mk_inst_def, EVERY_APPEND] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem immutable_fixed_words_code_option:
  !n off sa sb.
  compile_imm_store_words imm src dst n off sa = ((),sb) ==>
  same_blocks sa sb /\
  ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) is
Proof
  Induct
  >- simp[compile_imm_store_words_def, comp_return_def, same_blocks_def] >>
  simp[immutable_store_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >> drule immutable_store_one_code_option >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[same_blocks_def] >> metis_tac[APPEND_ASSOC, EVERY_APPEND]
QED

Theorem immutable_fixed_words_mem_cont_option:
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  immutable_execution_frame sa s sb t /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `frag_exec_mem ctx sa sb (\u. u = s)
    (\u. u = (t with vs_inst_idx := LENGTH sb.cs_current_insts)) (K F)` by
    (irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
     drule immutable_fixed_words_code_option >> strip_tac >>
     fs[immutable_execution_frame_def, same_blocks_def] >>
     gvs[EVERY_MEM] >> rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  drule mem_cont_sim_from_fragment >>
  disch_then (qspec_then `s` mp_tac) >> simp[]
QED

Theorem immutable_fixed_step_frame[local]:
  MEM i.inst_opcode [ADD; MLOAD; ISTORE] /\ step_inst_base i s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
               vs_immutables := t.vs_immutables|>
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  asm_simp_tac bool_ss [exec_read1_def, exec_pure2_def] >>
  simp[AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def, istore_def, mstore_def, write_memory_with_expansion_def,
      venom_state_component_equality]
QED

Theorem immutable_fixed_sequence_frame[local]:
  !code s t.
  EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) code /\
  run_inst_seq code s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
               vs_immutables := t.vs_immutables|>
Proof
  Induct >- simp[run_inst_seq_def] >> rpt gen_tac >>
  simp_tac (srw_ss()) [run_inst_seq_def, EVERY_DEF, AllCaseEqs(), Excl "MEM"] >>
  strip_tac >> drule_at (Pos last) immutable_fixed_step_frame >> simp[] >> strip_tac >>
  rename1 `run_inst_seq code middle = OK t` >>
  first_x_assum (qspecl_then [`middle`,`t`] mp_tac) >> simp[] >>
  strip_tac >> gvs[venom_state_component_equality]
QED

Theorem immutable_fixed_copy_mem_endpoint_option:
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\ fresh_vars_wrt sa s /\ 0 < n /\
  a + off + 32*n <= s.vs_alloca_next /\
  b + off + 32*n <= s.vs_alloca_next /\
  a + off + 32*n < dimword (:256) /\
  b + off + 32*n < dimword (:256) /\
  (b + off + 32*n <= a + off \/ a + off + 32*n <= b + off) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
                 vs_immutables := t.vs_immutables|> /\
    t.vs_memory = (mcopy (b+off) (a+off) (32*n) s).vs_memory /\
    mem_bytes_at (b+off) (32*n) t.vs_memory =
      mem_bytes_at (a+off) (32*n) s.vs_memory /\
    (!p k. p+k <= b+off \/ b+off+32*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (n2w a:bytes32) = a /\ w2n (n2w b:bytes32) = b` by
    (simp[w2n_n2w] >> conj_tac >> irule LESS_MOD >> decide_tac) >>
  drule immutable_fixed_words_mem_option >>
  disch_then (qspecl_then [`s`,`n2w a`,`n2w b`] mp_tac) >> simp[] >> strip_tac >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule immutable_fixed_words_mem_cont_option >> metis_tac[]) >>
  `t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
                 vs_immutables := t.vs_immutables|>` by
    (drule immutable_fixed_words_code_option >> strip_tac >>
     irule immutable_fixed_sequence_frame >>
     fs[immutable_execution_frame_def, emitted_insts_def, DROP_APPEND] >>
     metis_tac[]) >>
  `(immutable_transfers T T (n2w a) (n2w b) n off s).vs_memory =
    (mcopy (b+off) (a+off) (32*n) s).vs_memory` by
    (irule immutable_memory_transfers_snapshot >> simp[]) >>
  qexists_tac `t` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `t = s with <|vs_vars := _; vs_memory := _;
                    vs_immutables := _|>` mp_tac >>
               simp[venom_state_component_equality]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[mcopy_mem_bytes_at_same] >>
  rpt strip_tac >> simp[] >>
  qspecl_then [`p`,`k`,`b+off`,`a+off`,`32*n`,`s`] mp_tac
    mcopy_mem_bytes_at_disjoint >> simp[] >> decide_tac
QED
