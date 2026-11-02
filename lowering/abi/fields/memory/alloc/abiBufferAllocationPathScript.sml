(* TOP-LEVEL: actual buffer allocation preserves packed data and older
   operands, establishes its owned output window and keeps the allocator
   invariant. Both fresh and sufficiently large cached records are accepted. *)
Theory abiBufferAllocationPath
Ancestors
  abiBufferAllocationCode abiAllocationFrame abiAllocatedWindows abiPathAllocRecords
  abiStateFrame abiFieldOperands abiStaticLoopCode memoryValueSnapshot
  context compileEnv fragExec fragBlockPath exprLoweringProps instIdxIndep
  venomState venomMemDefs venomInst list words arithmetic

Theorem abi_allocated_window_inst_idx:
  !ss id offset count index.
    abi_allocated_window (ss with vs_inst_idx := index) id offset count =
      abi_allocated_window ss id offset count
Proof
  simp[abi_allocated_window_def]
QED

Theorem abi_state_frame_inst_idx:
  !before after index.
    abi_state_frame before (after with vs_inst_idx := index) = abi_state_frame before after
Proof
  simp[abi_state_frame_def]
QED

Theorem buffer_allocation_context:
  !id var_base byte_count ss.
    abi_state_frame ss (memory_snapshot_allocated id var_base byte_count ss) /\
    (memory_snapshot_allocated id var_base byte_count ss).vs_current_bb = ss.vs_current_bb /\
    (memory_snapshot_allocated id var_base byte_count ss).vs_halted = ss.vs_halted /\
    (memory_snapshot_allocated id var_base byte_count ss).vs_memory = ss.vs_memory /\
    (memory_snapshot_allocated id var_base byte_count ss).vs_allocas =
      (memory_snapshot_alloc_frame id byte_count ss).vs_allocas /\
    (memory_snapshot_allocated id var_base byte_count ss).vs_alloca_next =
      (memory_snapshot_alloc_frame id byte_count ss).vs_alloca_next
Proof
  rpt gen_tac >> simp[memory_snapshot_allocated_def, memory_snapshot_alloc_frame_def] >>
  rw[] >> simp[update_var_def, abi_state_frame_def]
QED

Theorem buffer_allocation_window:
  !id var_base byte_count ss.
    alloca_inv ss /\ abi_alloca_request_ok id byte_count ss /\
    ss.vs_alloca_next + byte_count < dimword(:256) ==>
    abi_allocated_window (memory_snapshot_allocated id var_base byte_count ss) id
      (w2n (memory_snapshot_addr id ss)) byte_count
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_allocation_frame_record >> strip_tac >>
  rename1 `FLOOKUP (memory_snapshot_alloc_frame id byte_count ss).vs_allocas id = SOME (offset,recorded_size)` >>
  simp_tac bool_ss [abi_allocated_window_def, memory_snapshot_allocated_def, update_var_def] >>
  qexistsl_tac [`offset`, `recorded_size`] >> simp[] >> decide_tac
QED

Theorem buffer_allocation_old_operand:
  !id var_base byte_count ss arg_op.
    abi_operand_before var_base arg_op ==>
    eval_operand arg_op (memory_snapshot_allocated id var_base byte_count ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> irule memory_snapshot_allocated_operand >>
  qpat_x_assum `abi_operand_before _ _` (mp_tac o REWRITE_RULE [abi_operand_before_def]) >>
  disch_then (qspec_then `var_base` mp_tac) >> simp[compiler_var_name_def]
QED

Theorem compile_alloc_buffer_path:
  !ctx func byte_count cs buf cs' ss.
    compile_alloc_buffer byte_count cs = (buf,cs') /\ fn_has_code cs cs' func /\
    alloca_inv ss /\ abi_alloca_request_ok cs.cs_next_id byte_count ss /\
    ss.vs_alloca_next + byte_count < dimword(:256) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\
      out = (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var byte_count ss
        with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operand buf.buf_operand out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      abi_operand_before cs'.cs_next_var buf.buf_operand /\
      abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) byte_count /\
      alloca_inv out /\ out.vs_memory = ss.vs_memory /\
      ss.vs_alloca_next <= out.vs_alloca_next /\ out.vs_alloca_next <= ss.vs_alloca_next + byte_count /\
      abi_state_frame ss out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (!id offset count. abi_allocated_window ss id offset count ==> abi_allocated_window out id offset count)
Proof
  rpt gen_tac >> strip_tac >> `byte_count < dimword(:256)` by decide_tac >>
  drule_all compile_alloc_buffer_execution >> DISCH_TAC >> drule_all compile_alloc_buffer_code >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `memory_snapshot_allocated cs.cs_next_id cs.cs_next_var byte_count ss`] fragment_path_emitted) >>
  impl_tac >- simp[mk_inst_def, is_terminator_def] >> DISCH_TAC >>
  qabbrev_tac `out = memory_snapshot_allocated cs.cs_next_id cs.cs_next_var byte_count ss
    with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  `fragment_path ctx func ss out` by fs[Abbr`out`] >>
  drule_all fragment_path_allocation_post >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `byte_count`, `ss`] buffer_allocation_context) >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `byte_count`, `ss`] buffer_allocation_window) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `byte_count`, `ss`] abi_allocation_frame_next) >> strip_tac >>
  `abi_operand_before cs'.cs_next_var buf.buf_operand` by
    (asm_simp_tac bool_ss [] >>
     mp_tac (Q.SPECL [`cs.cs_next_var`, `cs.cs_next_var + 1`] abi_operand_before_reserved) >>
     simp[compiler_var_name_def]) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op out = eval_operand arg_op ss` by
    (rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [Abbr`out`, eval_op_inst_idx] >>
     irule buffer_allocation_old_operand >> first_assum MATCH_ACCEPT_TAC) >>
  `eval_operand buf.buf_operand out = SOME (memory_snapshot_addr cs.cs_next_id ss)` by
    simp[Abbr`out`, eval_op_inst_idx] >>
  `abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) byte_count` by
    asm_simp_tac bool_ss [Abbr`out`, abi_allocated_window_inst_idx] >>
  `out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
    out.vs_memory = ss.vs_memory /\ ss.vs_alloca_next <= out.vs_alloca_next /\
    out.vs_alloca_next <= ss.vs_alloca_next + byte_count /\ abi_state_frame ss out` by
    asm_simp_tac (srw_ss()) [Abbr`out`, abi_state_frame_inst_idx] >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> simp[Abbr`out`]
QED
