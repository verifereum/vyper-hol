(* TOP-LEVEL: runtime array resources retain owned root input/output and
   the actual index-counter instruction. Allocation growth preserves them;
   pure loop effects preserve exactly their allocation observations. *)
Theory abiNativeArrayResources
Ancestors
  abiNativeCursor abiNativeEncodingDefs abiAllocatedWindows abiAllocatorState abiWriterFrame allocationGrowth
  compileAllocaProvenance compileEnv fragExec venomMemDefs venomState list words

Definition abi_native_array_resources_def:
  abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      (root_addr:bytes32) source_capacity (dst_addr:bytes32) (payload:word8 list) ss <=>
    alloca_inv ss /\ abi_allocated_window ss source_id (w2n root_addr) source_capacity /\
    abi_allocated_window ss target_id (w2n dst_addr) (LENGTH payload) /\
    abi_native_cursor func root_cs root_after counter_inst counter_addr loop_cs ss
End

Theorem abi_native_array_resources_initial:
  !func root_cs root_after source_id target_id counter_inst counter_addr loop_cs root_addr source_capacity dst_addr payload initial ss.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial /\
    abi_native_cursor func root_cs root_after counter_inst counter_addr loop_cs ss /\
    alloca_inv ss /\ allocation_growth initial ss ==>
    abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr payload ss
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  `abi_allocated_window ss source_id (w2n root_addr) source_capacity` by
    (qspecl_then [`initial`, `ss`, `source_id`, `w2n root_addr`, `source_capacity`]
       mp_tac allocation_growth_window >> simp[]) >>
  `abi_allocated_window ss target_id (w2n dst_addr) (LENGTH payload)` by
    (qspecl_then [`initial`, `ss`, `target_id`, `w2n dst_addr`, `LENGTH payload`]
       mp_tac allocation_growth_window >> simp[]) >>
  PURE_REWRITE_TAC [abi_native_array_resources_def] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_array_resources_allocator_state:
  !func root_cs root_after source_id target_id counter_inst counter_addr loop_cs root_addr source_capacity dst_addr payload before after.
    abi_allocator_state after = abi_allocator_state before ==>
    (abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr payload after <=>
     abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr payload before)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_allocator_state_eq] >> strip_tac >>
  simp[abi_native_array_resources_def, abi_native_cursor_def, abi_allocated_window_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native runtime array resources: " ^ name)
  end) (DB.thms "abiNativeArrayResources")
