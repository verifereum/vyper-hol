(* TOP-LEVEL: actual output allocation transports evaluated arguments,
   typed packed data and the dynamic encoder's bounded scratch requirements. *)
Theory abiLogAllocationReady
Ancestors
  typedCopyStateFrame abiAllocatedState abiAllocatorState
  abiLogAllocationRequests abiBufferAllocationCode abiLogReady abiFieldOperands
  abiFieldRequests abiFieldDefs abiFieldStateDefs abiAllocatedWindows abiAllocationFrame memoryValueSnapshot
  memoryValueDefs valueEncoding context compileEnv venomState list pair words arithmetic

Theorem abi_log_packing_allocation_resources:
  !before after source_id root_addr source_size output_id capacity requests.
    copy_state_frame before after /\ alloca_inv before /\
    abi_allocated_window before source_id (w2n (root_addr:bytes32)) source_size /\
    abi_alloca_request_ok output_id capacity before /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) before) requests ==>
    alloca_inv after /\
    abi_allocated_window after source_id (w2n root_addr) source_size /\
    abi_alloca_request_ok output_id capacity after /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) after) requests /\
    after.vs_alloca_next = before.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  `abi_allocator_state after = abi_allocator_state before` by
    fs[copy_state_frame_def, abi_allocator_state_eq] >>
  drule abi_alloca_inv_state >> DISCH_TAC >>
  drule abi_allocated_window_state >> DISCH_TAC >>
  drule abi_alloca_request_ok_state >> DISCH_TAC >>
  fs[copy_state_frame_def]
QED

Theorem abi_log_allocation_args:
  !capacity cs cut buf before middle src topic_ops topics root_addr tvs vs.
    compile_alloc_buffer capacity cs = (buf,cut) /\
    middle.vs_memory = before.vs_memory /\ middle.vs_alloca_next <= before.vs_alloca_next + capacity /\
    (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op middle = eval_operand arg_op before) /\
    abi_operand_before cs.cs_next_var src /\ EVERY (abi_operand_before cs.cs_next_var) topic_ops /\
    eval_operand src before = SOME root_addr /\ eval_operands topic_ops before = SOME topics /\
    memory_tuple_rel tvs vs (w2n root_addr) before.vs_memory /\ before.vs_alloca_next + capacity < dimword(:256) ==>
    abi_operand_before cut.cs_next_var src /\ EVERY (abi_operand_before cut.cs_next_var) topic_ops /\
    eval_operand src middle = SOME root_addr /\ eval_operands topic_ops middle = SOME topics /\
    memory_tuple_rel tvs vs (w2n root_addr) middle.vs_memory /\ middle.vs_alloca_next < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_alloc_buffer_code >> strip_tac >>
  `cs.cs_next_var <= cut.cs_next_var` by decide_tac >>
  `abi_operand_before cut.cs_next_var src` by (drule_all abi_operand_before_mono >> simp[]) >>
  `EVERY (abi_operand_before cut.cs_next_var) topic_ops` by
    (simp_tac bool_ss [EVERY_MEM] >> rpt strip_tac >>
     irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> fs[EVERY_MEM]) >>
  `eval_operands topic_ops middle = SOME topics` by (drule_all eval_operands_before_frame >> simp[]) >>
  `eval_operand src middle = SOME root_addr` by asm_simp_tac bool_ss [] >>
  `middle.vs_alloca_next < dimword(:256)` by decide_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_log_allocation_dynamic:
  !rows capacity cs cut buf before middle source_id root_addr tvs.
    compile_alloc_buffer capacity cs = (buf,cut) /\
    middle = (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var capacity before with vs_inst_idx := LENGTH cut.cs_current_insts) /\
    middle.vs_alloca_next <= before.vs_alloca_next + capacity /\
    (!id offset count. abi_allocated_window before id offset count ==> abi_allocated_window middle id offset count) /\
    32 <= capacity /\ abi_alloca_request_ok (cs.cs_next_id + 1) 32 before /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) before) (abi_field_requests (cs.cs_next_id + 3) rows) /\
    source_id < cs.cs_next_id /\ before.vs_alloca_next + capacity + 32 + SUM (MAP abi_field_budget rows) < dimword(:256) /\
    abi_allocated_window before source_id (w2n (root_addr:bytes32)) (type_memory_size_list tvs) ==>
    abi_alloca_request_ok cut.cs_next_id 32 middle /\
    EVERY (\request. abi_alloca_request_ok (FST request) (SND request) middle) (abi_field_requests (cut.cs_next_id + 2) rows) /\
    EVERY (\old_id. old_id < cut.cs_next_id) [source_id;cs.cs_next_id] /\ source_id <> cs.cs_next_id /\
    middle.vs_alloca_next + 32 + SUM (MAP abi_field_budget rows) < dimword(:256) /\
    abi_allocated_window middle source_id (w2n (root_addr:bytes32)) (type_memory_size_list tvs)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_alloc_buffer_code >> strip_tac >>
  drule_all abi_log_allocation_scratch_requests >> strip_tac >>
  qpat_x_assum `middle = _` (K ALL_TAC) >>
  `cut.cs_next_id + 2 = cs.cs_next_id + 3` by simp[] >>
  `EVERY (\old_id. old_id < cut.cs_next_id) [source_id;cs.cs_next_id] /\ source_id <> cs.cs_next_id` by
    (asm_simp_tac bool_ss [EVERY_DEF] >> decide_tac) >>
  `middle.vs_alloca_next + 32 + SUM (MAP abi_field_budget rows) < dimword(:256)` by decide_tac >>
  `abi_allocated_window middle source_id (w2n root_addr) (type_memory_size_list tvs)` by
    (qpat_x_assum `!id offset count. _` irule >> first_assum MATCH_ACCEPT_TAC) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed source Log readiness after allocation: " ^ name)
  end) (DB.thms "abiLogAllocationReady")
