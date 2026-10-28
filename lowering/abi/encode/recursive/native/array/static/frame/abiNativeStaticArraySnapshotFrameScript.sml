(* TOP-LEVEL: actual loop SSA/control snapshots inherit the precise
   data/index frame and the enclosing computed-profile frame. *)
Theory abiNativeStaticArraySnapshotFrame
Ancestors
  abiNativeStaticArrayFrame abiNativeArrayFrames abiNativeArrayResources abiNativeCursor abiNativeEncodingDefs
  abiNativeStaticArrayState abiMemoryEncoding abiFieldLayoutDefs abiAllocationWindows abiAllocatorState
  abiMemoryFrame abiStaticLoopRun compileAllocaProvenance compileEnv venomState list words arithmetic

Theorem abi_native_static_array_snapshot_frame:
  !iterations func root_cs root_after source_id target_id counter_inst counter_addr loop_cs root_addr source_capacity
      dst_addr info stride fields initial ss labels out.
    iterations <= LENGTH fields /\
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_array_resources func root_cs root_after source_id target_id counter_inst counter_addr loop_cs
      root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) ss /\
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity 0 ss /\
    out.vs_memory = (FUNPOW (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info)
      stride counter_addr labels) iterations ss).vs_memory /\ abi_allocator_state out = abi_allocator_state ss ==>
    abi_memory_frame [(w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
      abi_field_bytes (abi_field_head_size fields) fields));(w2n counter_addr,32)] ss out /\
    abi_memory_frame ((w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
      abi_field_bytes (abi_field_head_size fields) fields))::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`iterations`, `func`, `root_cs`, `root_after`, `source_id`, `target_id`, `counter_inst`, `counter_addr`,
    `loop_cs`, `root_addr`, `source_capacity`, `dst_addr`, `info`, `stride`, `fields`, `initial`, `ss`, `labels`]
    mp_tac abi_native_static_array_run_frame >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `abi_memory_frame [(w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
    abi_field_bytes (abi_field_head_size fields) fields));(w2n counter_addr,32)] ss out` by
    (qspecl_then [`[(w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields));(w2n counter_addr,32)]`, `ss`, `out`,
       `FUNPOW (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info)
         stride counter_addr labels) iterations ss`] mp_tac abi_memory_frame_memory_eq >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_native_array_resources _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_array_resources_def]) >>
  qspecl_then [`func`, `root_cs`, `root_after`, `counter_inst`, `counter_addr`, `loop_cs`, `ss`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`, `ss`, `out`]
    mp_tac abi_native_array_counter_frame >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`compiler_alloca_ids root_cs root_after`, `ss`, `out`] mp_tac abi_allocation_windows_allocator_state >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static array snapshot write frames: " ^ name)
  end) (DB.thms "abiNativeStaticArraySnapshotFrame")
