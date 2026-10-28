(* TOP-LEVEL: an actual variable-sized output allocation retains the native
   encoder's pending scratch budget and compatible cached word requests.
   Helpers expose compiler history and allocator-field observations. *)
Theory abiNativeLogAllocationReady
Ancestors
  abiNativeEncodingDefs abiAllocationBudget abiAllocationFrame abiAllocatorState abiLogAllocationRequests
  abiAllocatedWindows
  abiBufferAllocationCode compileIdFlow memoryValueSnapshot exprLoweringProps compileEnv fragExec
  venomState venomInst finite_map pred_set list arithmetic

Theorem buffer_allocation_profile_pending:
  !ids id var_base capacity index before after.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) ==>
    abi_alloca_pending ids after = abi_alloca_pending ids before DELETE id
Proof
  rpt gen_tac >> DISCH_TAC >>
  `abi_alloca_pending ids after = abi_alloca_pending ids (memory_snapshot_alloc_frame id capacity before)` by
    simp[abi_alloca_pending_def, memory_snapshot_allocated_def, update_var_def] >>
  simp[abi_alloca_pending_frame]
QED

Theorem buffer_allocation_profile_budget:
  !slot_size ids id var_base capacity index before after.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    after.vs_alloca_next <= before.vs_alloca_next + capacity ==>
    abi_alloca_budget slot_size ids after <= abi_alloca_budget slot_size ids before + capacity
Proof
  rpt gen_tac >> strip_tac >> drule buffer_allocation_profile_pending >>
  disch_then (qspec_then `ids` ASSUME_TAC) >>
  `CARD (abi_alloca_pending ids after) <= CARD (abi_alloca_pending ids before)` by
    (simp[CARD_DELETE] >> IF_CASES_TAC >> decide_tac) >>
  `slot_size * CARD (abi_alloca_pending ids after) <= slot_size * CARD (abi_alloca_pending ids before)` by
    simp[LE_MULT_LCANCEL] >>
  PURE_REWRITE_TAC [abi_alloca_budget_def] >> decide_tac
QED

Theorem buffer_allocation_profile_requests:
  !ids id var_base capacity index before after.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    32 <= capacity /\ (!request_id. MEM request_id ids ==> abi_alloca_request_ok request_id 32 before) ==>
    !request_id. MEM request_id ids ==> abi_alloca_request_ok request_id 32 after
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> DISCH_TAC >>
  qspecl_then [`id`, `var_base`, `capacity`, `index`, `before`, `after`, `request_id`, `32`]
    mp_tac buffer_allocation_request >> simp[]
QED

Theorem compile_alloc_buffer_id_history:
  !capacity cs buf cut.
    compile_alloc_buffer capacity cs = (buf,cut) /\ compiler_id_history cs ==>
    compiler_id_history cut
Proof
  rpt gen_tac >> strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  fs[compiler_id_history_def, same_blocks_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_APPEND, mk_inst_def] >> res_tac >> decide_tac
QED

Theorem abi_native_log_output_allocation_ready:
  !func cs cut cs' buf capacity before after source_id src_addr span payload.
    compile_alloc_buffer capacity cs = (buf,cut) /\ fn_inst_ids_distinct func /\ compiler_id_history cs /\
    after = (memory_snapshot_allocated cs.cs_next_id cs.cs_next_var capacity before
      with vs_inst_idx := LENGTH cut.cs_current_insts) /\
    alloca_inv after /\ after.vs_alloca_next <= before.vs_alloca_next + capacity /\
    abi_allocated_window after source_id (w2n src_addr) span /\
    abi_allocated_window after cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id before)) capacity /\
    source_id <> cs.cs_next_id /\ ~MEM source_id (compiler_alloca_ids cut cs') /\
    ~MEM cs.cs_next_id (compiler_alloca_ids cut cs') /\
    32 <= capacity /\ LENGTH payload <= capacity /\
    abi_alloca_budget 32 (compiler_alloca_ids cut cs') before + capacity < dimword (:256) /\
    (!id. MEM id (compiler_alloca_ids cut cs') ==> abi_alloca_request_ok id 32 before) ==>
    abi_native_memory_ready func cut cs' source_id cs.cs_next_id src_addr span
      (memory_snapshot_addr cs.cs_next_id before) payload after
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_alloc_buffer_id_history >> DISCH_TAC >>
  `abi_alloca_budget 32 (compiler_alloca_ids cut cs') after < dimword (:256)` by
    (qspecl_then [`32`, `compiler_alloca_ids cut cs'`, `cs.cs_next_id`, `cs.cs_next_var`,
       `capacity`, `LENGTH cut.cs_current_insts`, `before`, `after`]
       mp_tac buffer_allocation_profile_budget >> impl_tac >- simp[] >> DISCH_TAC >> decide_tac) >>
  `!id. MEM id (compiler_alloca_ids cut cs') ==> abi_alloca_request_ok id 32 after` by
    (qspecl_then [`compiler_alloca_ids cut cs'`, `cs.cs_next_id`, `cs.cs_next_var`,
       `capacity`, `LENGTH cut.cs_current_insts`, `before`, `after`]
       mp_tac buffer_allocation_profile_requests >> simp[]) >>
  `abi_allocated_window after cs.cs_next_id (w2n (memory_snapshot_addr cs.cs_next_id before)) (LENGTH payload)` by
    (qspecl_then [`after`, `cs.cs_next_id`, `w2n (memory_snapshot_addr cs.cs_next_id before)`,
       `capacity`, `LENGTH payload`] mp_tac abi_allocated_window_shrink >> simp[]) >>
  qpat_x_assum `after = _` (K ALL_TAC) >> simp[abi_native_memory_ready_def]
QED

Theorem abi_native_log_data_allocation_resources:
  !ids id var_base capacity index before after output_id output_capacity.
    after = (memory_snapshot_allocated id var_base capacity before with vs_inst_idx := index) /\
    after.vs_alloca_next <= before.vs_alloca_next + capacity /\
    id <> output_id /\ 32 <= capacity /\
    abi_alloca_request_ok output_id output_capacity before /\
    abi_alloca_budget 32 ids before + capacity + output_capacity < dimword (:256) /\
    (!request_id. MEM request_id ids ==> abi_alloca_request_ok request_id 32 before) ==>
    abi_alloca_request_ok output_id output_capacity after /\
    abi_alloca_budget 32 ids after + output_capacity < dimword (:256) /\
    (!request_id. MEM request_id ids ==> abi_alloca_request_ok request_id 32 after)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_alloca_request_ok output_id output_capacity after` by
    (qspecl_then [`id`, `var_base`, `capacity`, `index`, `before`, `after`, `output_id`, `output_capacity`]
       mp_tac buffer_allocation_request >> simp[]) >>
  `abi_alloca_budget 32 ids after + output_capacity < dimword (:256)` by
    (qspecl_then [`32`, `ids`, `id`, `var_base`, `capacity`, `index`, `before`, `after`]
       mp_tac buffer_allocation_profile_budget >> impl_tac >- simp[] >> DISCH_TAC >> decide_tac) >>
  qspecl_then [`ids`, `id`, `var_base`, `capacity`, `index`, `before`, `after`]
    mp_tac buffer_allocation_profile_requests >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native Log output allocation readiness: " ^ name)
  end) (DB.thms "abiNativeLogAllocationReady")
