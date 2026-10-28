(* TOP-LEVEL: actual buffer allocation consumes a pending-identity budget
   once per fresh slot and preserves it on cached replay. Both paths retain
   ownership, old allocation windows, source memory and reserved operands. *)
Theory abiBufferBudgetPath
Ancestors
  abiAllocationBudgetReady abiAllocationBudget abiAllocationTrace abiAllocationFrame abiBufferAllocationPath
  abiBufferAllocationCode abiAllocatedWindows abiPathAllocRecords abiStateFrame abiFieldOperands
  abiStaticLoopCode memoryValueSnapshot context compileEnv fragExec fragBlockPath
  exprLoweringProps instIdxIndep venomState venomMemDefs venomInst list words arithmetic

Theorem compile_alloc_buffer_snapshot_path:
  !ctx func byte_count cs buf cs' ss.
    compile_alloc_buffer byte_count cs = (buf,cs') /\ fn_has_code cs cs' func /\
    byte_count < dimword (:256) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    fragment_path ctx func ss
      (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var byte_count ss
        with vs_inst_idx := LENGTH cs'.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_alloc_buffer_execution >> DISCH_TAC >>
  drule compile_alloc_buffer_code >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `cs'`, `ss`,
    `memory_snapshot_allocated cs.cs_next_id cs.cs_next_var byte_count ss`]
    mp_tac fragment_path_emitted >>
  impl_tac >- simp[mk_inst_def, is_terminator_def] >> simp[]
QED

Theorem buffer_allocation_budget_window:
  !id var_base byte_count ids ss.
    MEM id ids /\ abi_alloca_budget byte_count ids ss < dimword (:256) /\
    abi_alloca_request_ok id byte_count ss /\ alloca_inv ss ==>
    abi_allocated_window (memory_snapshot_allocated id var_base byte_count ss) id
      (w2n (memory_snapshot_addr id ss)) byte_count
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_alloca_budget_ready >> strip_tac >>
  rename1 `FLOOKUP (memory_snapshot_alloc_frame id byte_count ss).vs_allocas id = SOME (offset,recorded_size)` >>
  simp_tac bool_ss [abi_allocated_window_def, memory_snapshot_allocated_def, update_var_def] >>
  qexistsl_tac [`offset`, `recorded_size`] >> simp[] >> decide_tac
QED

Theorem buffer_allocation_budget_image:
  !byte_count ids id var_base ss index.
    MEM id ids ==>
    abi_alloca_pending ids (memory_snapshot_allocated id var_base byte_count ss with vs_inst_idx := index) =
      abi_alloca_pending ids ss DELETE id /\
    abi_alloca_budget byte_count ids (memory_snapshot_allocated id var_base byte_count ss with vs_inst_idx := index) =
      abi_alloca_budget byte_count ids ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  `abi_alloca_pending ids (memory_snapshot_allocated id var_base byte_count ss with vs_inst_idx := index) =
      abi_alloca_pending ids (memory_snapshot_alloc_frame id byte_count ss) /\
    abi_alloca_budget byte_count ids (memory_snapshot_allocated id var_base byte_count ss with vs_inst_idx := index) =
      abi_alloca_budget byte_count ids (memory_snapshot_alloc_frame id byte_count ss)` by
    simp[abi_alloca_pending_def, abi_alloca_budget_def, memory_snapshot_allocated_def, update_var_def] >>
  simp[abi_alloca_pending_frame, abi_alloca_budget_frame]
QED

Theorem compile_alloc_buffer_budget_path:
  !ctx func byte_count ids cs buf cs' ss.
    compile_alloc_buffer byte_count cs = (buf,cs') /\ fn_has_code cs cs' func /\
    MEM cs.cs_next_id ids /\ abi_alloca_budget byte_count ids ss < dimword (:256) /\
    alloca_inv ss /\ abi_alloca_request_ok cs.cs_next_id byte_count ss /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\
      out = (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var byte_count ss
        with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      eval_operand buf.buf_operand out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      abi_operand_before cs'.cs_next_var buf.buf_operand /\
      abi_allocated_window out cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id ss)) byte_count /\
      alloca_inv out /\ out.vs_memory = ss.vs_memory /\ out.vs_alloca_next < dimword (:256) /\
      ss.vs_alloca_next <= out.vs_alloca_next /\ out.vs_alloca_next <= ss.vs_alloca_next + byte_count /\
      abi_alloca_pending ids out = abi_alloca_pending ids ss DELETE cs.cs_next_id /\
      abi_alloca_budget byte_count ids out = abi_alloca_budget byte_count ids ss /\
      abi_allocation_trace byte_count ids ss out /\
      abi_state_frame ss out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      (!id offset count. abi_allocated_window ss id offset count ==> abi_allocated_window out id offset count)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_alloca_budget_ready >> strip_tac >>
  qspecl_then [`ctx`, `func`, `byte_count`, `cs`, `buf`, `cs'`, `ss`]
    mp_tac compile_alloc_buffer_snapshot_path >> impl_tac >- simp[] >> DISCH_TAC >>
  drule compile_alloc_buffer_code >> strip_tac >>
  qabbrev_tac `out = memory_snapshot_allocated cs.cs_next_id cs.cs_next_var byte_count ss
    with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  `fragment_path ctx func ss out` by fs[Abbr`out`] >>
  drule_all fragment_path_allocation_post >> strip_tac >>
  qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `byte_count`, `ss`]
    strip_assume_tac buffer_allocation_context >>
  qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `byte_count`, `ids`, `ss`]
    mp_tac buffer_allocation_budget_window >> impl_tac >- simp[] >> DISCH_TAC >>
  qspecl_then [`cs.cs_next_id`, `byte_count`, `ss`] strip_assume_tac abi_allocation_frame_next >>
  `abi_operand_before cs'.cs_next_var buf.buf_operand` by
    (asm_simp_tac bool_ss [] >>
     qspecl_then [`cs.cs_next_var`, `cs.cs_next_var + 1`] mp_tac abi_operand_before_reserved >>
     simp[compiler_var_name_def]) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss` by
    (rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [Abbr`out`, eval_op_inst_idx] >>
     irule buffer_allocation_old_operand >> simp[]) >>
  qspecl_then [`byte_count`, `ids`, `cs.cs_next_id`, `cs.cs_next_var`, `ss`, `LENGTH cs'.cs_current_insts`]
    mp_tac buffer_allocation_budget_image >> impl_tac >- simp[] >> strip_tac >>
  qexists_tac `out` >>
  fs[Abbr`out`, abi_allocated_window_inst_idx, abi_state_frame_inst_idx, eval_op_inst_idx,
    abi_allocation_trace_image]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual pending-budget buffer allocation: " ^ name)
  end) (DB.thms "abiBufferBudgetPath")
