(* TOP-LEVEL: allocate the actual Log data arena while retaining evaluated
   arguments and topics. The arena pointer and ownership come from ALLOCA. *)
Theory abiLogDataAllocation
Ancestors
  abiBufferAllocationPath abiBufferAllocationCode abiLogReady abiFieldOperands
  abiLogAllocationRequests abiFieldRequests abiFieldDefs
  typedLogArgs typedLogArgsFrames typedSArrayDynInvariant typedArrayLoopNames
  abiStaticLoopCode abiBytestringCode abiAllocationFrame abiAllocatedWindows abiStateFrame
  memoryValueSnapshot valueEncoding context compileEnv fragExec fragBlockPath
  instIdxIndep venomState list pair words arithmetic

Theorem log_args_allocation_frame:
  !args atvs vs before after id var_base capacity index ftv dst.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    log_args_rel args atvs vs before /\ log_args_safe args atvs before dst (type_memory_size ftv) /\
    log_args_avoid args (compiler_var_names var_base 1) ==>
    log_args_rel args atvs vs after /\ log_args_safe args atvs after dst (type_memory_size ftv)
Proof
  rpt gen_tac >> strip_tac >>
  `after.vs_memory = before.vs_memory` by simp[] >>
  `array_copy_frame ftv 1 dst before.vs_memory after.vs_memory` by simp[] >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 1) ==>
    eval_operand arg_op after = eval_operand arg_op before` by
    (rpt gen_tac >> asm_simp_tac (srw_ss()) [compiler_var_names_def, GENLIST, eval_op_inst_idx] >>
     DISCH_TAC >> irule memory_snapshot_allocated_operand >> first_assum MATCH_ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`args`, `atvs`, `vs`, `before`, `after`, `ftv`, `1`, `dst`,
    `compiler_var_names var_base 1`] log_args_frame) >> simp[]
QED

Theorem log_data_allocation_encoder_requests:
  !rows id var_base capacity index before after output_id output_capacity.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    id < output_id /\ 32 <= capacity /\ abi_alloca_request_ok output_id output_capacity before ==>
    abi_alloca_request_ok output_id output_capacity after /\
    (abi_alloca_request_ok (output_id + 1) 32 before /\
      EVERY (\request. abi_alloca_request_ok (FST request) (SND request) before)
        (abi_field_requests (output_id + 3) rows) ==>
      abi_alloca_request_ok (output_id + 1) 32 after /\
      EVERY (\request. abi_alloca_request_ok (FST request) (SND request) after)
        (abi_field_requests (output_id + 3) rows))
Proof
  rpt gen_tac >> strip_tac >>
  `abi_alloca_request_ok output_id output_capacity after` by
    (mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `index`, `before`, `after`, `output_id`, `output_capacity`]
       buffer_allocation_request) >> impl_tac >- (simp[] >> decide_tac) >> simp[]) >>
  asm_simp_tac bool_ss [] >> strip_tac >> conj_tac
  >- (mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `index`, `before`, `after`, `output_id + 1`, `32`]
       buffer_allocation_request) >> impl_tac >- (simp[] >> decide_tac) >> simp[]) >>
  mp_tac (Q.SPECL [`id`, `var_base`, `capacity`, `index`, `before`, `after`, `abi_field_requests (output_id + 3) rows`]
    buffer_allocation_word_requests) >> impl_tac >- simp[abi_field_requests_sizes] >> simp[]
QED

Theorem compile_log_data_allocation_path:
  !ctx func capacity cs buf cs' args atvs vs ftv topic_ops topics ss.
    compile_alloc_buffer capacity cs = (buf,cs') /\ fn_has_code cs cs' func /\
    alloca_inv ss /\ abi_alloca_request_ok cs.cs_next_id capacity ss /\
    ss.vs_alloca_next + capacity < dimword(:256) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    log_args_rel args atvs vs ss /\
    log_args_safe args atvs ss (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size ftv) /\
    EVERY (\arg. abi_operand_before cs.cs_next_var (FST arg)) args /\
    EVERY (abi_operand_before cs.cs_next_var) topic_ops /\ eval_operands topic_ops ss = SOME topics /\
    type_memory_size ftv <= capacity ==>
    ?out. fragment_path ctx func ss out /\
      out = (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var capacity ss
        with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operand buf.buf_operand out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      abi_operand_before cs'.cs_next_var buf.buf_operand /\
      abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size ftv) /\
      alloca_inv out /\ out.vs_memory = ss.vs_memory /\
      ss.vs_alloca_next <= out.vs_alloca_next /\ out.vs_alloca_next <= ss.vs_alloca_next + capacity /\
      log_args_rel args atvs vs out /\
      log_args_safe args atvs out (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size ftv) /\
      EVERY (abi_operand_before cs'.cs_next_var) topic_ops /\ eval_operands topic_ops out = SOME topics /\
      abi_state_frame ss out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `capacity`, `cs`, `buf`, `cs'`, `ss`] compile_alloc_buffer_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `log_args_avoid args (compiler_var_names cs.cs_next_var 1)` by
    (simp_tac bool_ss [log_args_avoid_def, EVERY_MEM] >> qx_gen_tac `arg` >> DISCH_TAC >>
     mp_tac (Q.SPECL [`cs.cs_next_var`, `FST (arg:operand # type)`, `cs.cs_next_var`, `1`]
       abi_operand_before_names) >> impl_tac >- fs[EVERY_MEM] >> simp_tac bool_ss [EVERY_MEM]) >>
  mp_tac (Q.SPECL [`args`, `atvs`, `vs`, `ss`, `out`, `cs.cs_next_id`, `cs.cs_next_var`,
    `capacity`, `LENGTH cs'.cs_current_insts`, `ftv`, `w2n (memory_snapshot_addr cs.cs_next_id ss)`]
    log_args_allocation_frame) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) (type_memory_size ftv)` by
    (drule_all abi_allocated_window_shrink >> simp[]) >>
  `eval_operands topic_ops out = SOME topics` by (drule_all eval_operands_before_frame >> simp[]) >>
  drule compile_alloc_buffer_code >> strip_tac >>
  `cs.cs_next_var <= cs'.cs_next_var` by decide_tac >>
  `EVERY (abi_operand_before cs'.cs_next_var) topic_ops` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
     irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> fs[EVERY_MEM]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED
